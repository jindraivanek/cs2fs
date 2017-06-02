module cs2fs.FSharpOutput

open ExtCore
open cs2fs.AST

let rec intersperse sep =
    function
    | [] -> []
    | [x] -> [x]
    | x::xs -> x::sep::(intersperse sep xs)

let nl = System.Environment.NewLine

type Block =
    | Text of string
    | Line
    | IndentBlock of Block
    | Block of Block list
    
let printBlock block =
    let printIndent x = ([1..x] |> Seq.map (fun _ -> "    ") |> String.concat "")
    let rec print =
        function
        | Text s -> s
        | Line -> newline
        | _ -> ""
    let rec f indent =
        function
        | Text s -> [indent, Text s]
        | Line -> [indent, Line]
        | Block (b::bs) -> f indent b @ f indent (Block bs)
        | Block [] -> []
        | IndentBlock b -> f (indent + 1) b
    f 0 block 
    |> Seq.fold (fun (acc,lineBegin) (indent, b) -> 
        acc + (if lineBegin then printIndent indent else "") + print b, match b with |Line -> true |_->false) ("",false)
    |> fst  
    
let block xs = xs |> Seq.toList |> Block
let (|++|) x y = Block [x;y]
let (|+>|) x y = Block [x; IndentBlock y]

let surround head tail body = head + body + tail

let delim sep xs = xs |> String.concat sep

let multi f = function
    | x::(y::tl) as xs -> f xs
    | [x] -> x
    | [] -> f []

let delimSurround sep head tail xs = xs |> (delim sep >> surround head tail)

let LineText = Text >> (fun x -> x |++| Line)
let newline b = block [b; Line]
let delimText sep xs = xs |> Seq.toList |> intersperse (Text sep) |> block
let delimLineText sep xs = xs |> Seq.toList |> intersperse (Line |++| Text sep) |> block
let surroundText head tail body = Text head |++| body |++| Text tail
let delimSurroundText sep head tail xs = xs |> (delimText sep >> surroundText head tail)

let rec getTyp =
    function
    | TypType (TypeId x) -> Text x
    | TypGeneric (GenericId x) -> Text x
    | TypWithGeneric(GenericId g, x) -> getTyp x |++| Text ("<" + g + ">") 
    | TypFun(t1, t2) -> [t1; t2] |> Seq.map getTyp |> delimText " -> "
    | TypTuple(ts) -> ts |> Seq.map getTyp |> delimText " * " |> surroundText "(" ")"

let rec getPat =
    function
    | PatConst (ConstId c) -> Text c
    | PatWildcard -> Text "_"
    | PatBind (ValId v) -> Text v
    | PatCons (ValId v, ps) -> Text (v + " ") |++| (ps |> Seq.map getPat |> delimText " ")
    | PatInfixCons (p1, (ValId v), p2) -> [getPat p1; Text v; getPat p2] |> delimText " " |> surroundText "(" ")"
    | PatTuple ts -> ts |> List.map getPat |> delimSurroundText ", " "(" ")" 
    | PatList ts -> ts |> List.map getPat |> delimSurroundText "; " "[" "]" 
    | PatRecord rows -> rows |> Seq.map (fun (FieldId f, p) -> Text (f + " = ") |++| getPat p) |> delimText "; " |> surroundText "{" "}" 
    | PatWithType (t, p) -> [getPat p; getTyp t] |> delimText " : "
    | PatBindAs (ValId v, p) -> [getPat p;  Text v] |> delimText " as "

let rec getDecl =
    function
    | TypeDeclRecord rows -> rows |> Seq.map (fun (FieldId f, t) -> Text (f + " : ") |++| getDecl t) |> delimText "; " |> surroundText "{" "}"
    | TypeDeclUnion rows -> rows |> Seq.map (fun (ValId v, t) -> Text v |++| (t |> Option.map (fun x -> Text " of " |++| getDecl x) |> Option.fill (Text ""))) |> delimText " | "
    | TypeDeclTuple ts -> ts |> Seq.map getDecl |> delimText " * " |> surroundText "(" ")"
    | TypeDeclId (TypeId p) -> Text p
    | TypeDeclWithGeneric (GenericId g, t) -> [Text g; getDecl t] |> delimText " "

let rec getMatch (p, whenE, e) =
    let whenClause = whenE |> Option.map (fun x -> Text " when " |++| getExpr x) |> Option.fill (Text "")
    [getPat p |++| whenClause; getExpr e] |> delimText " -> "

and getBind isRec isFirstRec (p, e) =
    match isRec, isFirstRec with
    | true, true -> Text "let rec "
    | true, false -> Text "and "
    | _ -> Text "let " 
    |++| getPat p |++| Text " = " |++| Line |++| getExpr e

and getExpr =
    function
    | ExprConst (ConstId c) -> Text c
    | ExprVal (ValId v) -> Text v
    | ExprApp (e1, e2) -> [getExpr e1; getExpr e2] |> delimText " " |> surroundText "(" ")"
    | ExprInfixApp (e1, ValId v, e2) -> [getExpr e1; Text v; getExpr e2] |> delimText " " |> surroundText "(" ")"
    | ExprTuple ts -> ts |> List.map getExpr |> delimSurroundText ", " "(" ")"
    | ExprList ts -> ts |> List.map getExpr |> delimSurroundText "; " "[" "]"
    | ExprRecord (copyE, rows) -> 
        let fields = rows |> Seq.map (fun (FieldId f, e) -> Text f |++| Text " = " |++| getExpr e) |> delimText "; " 
        let copyStat = copyE |> Option.map (fun x -> getExpr x |++| Text " with ") |> Option.fill (Text "")
        copyStat |++| fields |> surroundText "{" "}"
    | ExprBind (p,e) -> 
        getBind false false (p,e)
    | ExprRecBind bindings -> 
        let n = Seq.length bindings
        (bindings |> Seq.mapi (fun i x -> getBind true (i=0) x |> newline) |> block) 
    | ExprMatch (e, rows) -> 
        ([Text "match"; getExpr e; Text "with"] |> delimText " ")
        |++| Line |++| (rows |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
    | ExprMatchLambda (rows) -> 
        Text "function"
        |++| Line |++| (rows |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
    | ExprLambda (args, e) -> Text "fun " |++| (args |> Seq.map getPat |> delimText " ") |++| Text " -> " |++| getExpr e |> surroundText "(" ")"
    | ExprWithType (t, e) -> getExpr e |++| Text " : " |++| getTyp t
    | ExprModule (ModuleId m, e) -> Text "module " |++| Text m |++| Text " = struct " |++| Line |++| getExpr e |++| Text " end"
    | ExprType (TypeId tId, t) -> Text "type " |++| Text tId |++| Text " = " |++| getDecl t
    | ExprNewType (TypeId tId, t) -> Text "datatype " |++| Text tId |++| Text " = " |++| getDecl t
    | ExprInclude (ModuleId m) -> Text "load " |++| Text m
    | ExprSequence es -> 
        let n = Seq.length es
        es |> Seq.mapi (fun i e -> 
            getExpr e |++| 
            (if i < n-1 then 
                match e with 
                |ExprBind _ 
                |ExprRecBind _ -> Text " in " 
                |_ -> Text "" 
            else Text ""))
        |> delimLineText ""
