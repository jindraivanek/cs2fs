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
        | Line -> nl
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
let lineblock xs = xs |> Seq.toList |> intersperse Line |> Block
let (|++|) x y = Block [x;y]
let (|+>|) x y = Block [x; IndentBlock y]

let surround head tail body = head + body + tail

let delim sep xs = xs |> String.concat sep

let multi f = function
    | x::(y::tl) as xs -> f xs
    | [x] -> x
    | [] -> f []

let delimSurround sep head tail xs = xs |> (delim sep >> surround head tail)

let LineText = Text >> (fun x -> Line |++| x)
let indentLineBlock b = Line |+>| b

let newline b = block [b; Line]
let delimText sep xs = xs |> Seq.toList |> intersperse (Text sep) |> block
let delimLineText sep xs = xs |> Seq.toList |> intersperse (Line |++| Text sep) |> block
let surroundText head tail body = Text head |++| body |++| Text tail
let delimSurroundText sep head tail xs = xs |> (delimText sep >> surroundText head tail)


let getModifier =
    function
    | Private -> Text "private"
    | Static -> Text "static"
    | Mutable -> Text "mutable"
    
let getModifierGroup =
    function
    | Private -> 2
    | Static
    | Mutable -> 1

let getModifiersOfGroup rank ms = 
    ms |> Seq.filter (fun x -> getModifierGroup x = rank) 
    |> Seq.map (fun m -> getModifier m |++| Text " ") |> block

let getModifiers ms = [1..2] |> Seq.map (fun r -> getModifiersOfGroup r ms) |> block 

let getGenerics gs = gs |> Seq.map (fun (GenericId g) -> Text ("'" + g)) |> delimSurroundText ", " "<" ">"

let rec getTyp =
    function
    | TypType (TypeId x) -> Text x
    | TypGeneric (GenericId x) -> Text ("'" + x)
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

let getPatNoType =
    function
    | PatWithType (_, p) -> getPat p
    | p -> getPat p

let rec getDecl =
    function
    | TypeDeclRecord rows -> rows |> Seq.map (fun (FieldId f, t) -> Text (f + " : ") |++| getDecl t) |> delimText "; " |> surroundText "{" "}"
    | TypeDeclUnion rows -> rows |> Seq.map (fun (ValId v, t) -> Text v |++| (t |> Option.map (fun x -> Text " of " |++| getDecl x) |> Option.fill (Text ""))) |> delimText " | "
    | TypeDeclTuple ts -> ts |> Seq.map getDecl |> delimText " * " |> surroundText "(" ")"
    | TypeDeclId (TypeId p) -> Text p
    | TypeDeclClass (modifiers, generics, p, members) -> getModifiers modifiers |++| getPat p


let rec getMatch (p, whenE, e) =
    let whenClause = whenE |> Option.map (fun x -> Text " when " |++| getExpr x) |> Option.fill (Text "")
    [getPat p |++| whenClause; getExpr e] |> delimText " -> "

and getMember x =
    let property pat init getter (haveSetter, setter) =
        let isAutoProperty = Option.isNone getter && (haveSetter = false || Option.isNone setter)
        let header = Text (if isAutoProperty then  "member val " else "member this.") |++| getPatNoType pat |++| (if isAutoProperty then Text " = " |++| getExpr init else Text "")
        let getterText = 
            getter |> Option.map (fun e -> Line |+>| (Text "with get() = " |++| Line |+>| getExpr e)) 
            |> Option.fill (Text "")
        let setterText = 
            setter |> Option.map (fun e -> Line |+>| (Text "and set(value) = " |++| Line |+>| getExpr e)) 
            |> Option.fill (Text (if isAutoProperty then " with get, set" else ""))
        header |++| getterText |++| (if haveSetter then setterText else Text "")
    match x with
    | ExprMember (ValId v, generics, modifiers, thisVal, args, expr) -> 
        getModifiersOfGroup 1 modifiers |++| Text "member " |++| getModifiersOfGroup 2 modifiers 
        |++| (thisVal |> Option.map (fun (ValId x) -> Text(x + ".")) |> Option.fill (Text "")) |++| Text v
        |++| getGenerics generics |++| getPat args |++| Text " = " |++| Line |+>| getExpr expr
    | ExprMemberProperty (pat, init, getter) -> property pat init getter (false, None)
    | ExprMemberPropertyWithSet (pat, init, getter, setter) -> property pat init getter (true, setter)
    | ExprAttribute (attrs, e) -> 
        attrs |> List.map (fun (AttributeId x) -> Text x) |> delimSurroundText "; " "[<" ">]" |++| Line
        |++| getMember e

and getBind header modifiers isRec isFirstRec (p, e) =
    match isRec, isFirstRec with
    | true, true -> Text (header + " rec ")
    | true, false -> Text "and "
    | _ -> Text (header + " ") 
    |++| getModifiers modifiers |++| getPat p |++| Text " = " |++| Line |+>| getExpr e

and getExpr =
    function
    | ExprConst (ConstId c) -> Text c
    | ExprVal (ValId v) -> Text v
    | ExprApp (e1, e2) -> [getExpr e1; getExpr e2] |> delimText " " |> surroundText "(" ")"
    | ExprDotApp (e1, e2) -> [getExpr e1; getExpr e2] |> delimText "."
    | ExprInfixApp (e1, ValId v, e2) -> [getExpr e1; Text v; getExpr e2] |> delimText " " |> surroundText "(" ")"
    | ExprTuple ts -> ts |> List.map getExpr |> delimSurroundText ", " "(" ")"
    | ExprList ts -> ts |> List.map getExpr |> delimSurroundText "; " "[" "]"
    | ExprRecord (copyE, rows) -> 
        let fields = rows |> Seq.map (fun (FieldId f, e) -> Text f |++| Text " = " |++| getExpr e) |> delimText "; " 
        let copyStat = copyE |> Option.map (fun x -> getExpr x |++| Text " with ") |> Option.fill (Text "")
        copyStat |++| fields |> surroundText "{" "}"
    | ExprBind (modifiers, p, e) -> 
        getBind "let" modifiers false false (p,e)
    | ExprUseBind (p, e) -> 
        getBind "use" [] false false (p,e)
    | ExprRecBind bindings -> 
        let n = Seq.length bindings
        (bindings |> Seq.mapi (fun i x -> getBind "let" [] true (i=0) x |> newline) |> block) 
    | ExprMatch (e, rows) -> 
        ([Text "match"; getExpr e; Text "with"] |> delimText " ")
        |++| Line |++| (rows |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
    | ExprMatchLambda (rows) -> 
        Text "function"
        |++| Line |++| (rows |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
    | ExprLambda (args, e) -> 
        Text "fun " |++| (args |> Seq.map getPat |> delimText " ") |++| Text " -> " |++| getExpr e |> surroundText "(" ")"
    | ExprWithType (t, e) -> getExpr e |++| Text " : " |++| getTyp t
    | ExprModule (ModuleId m, e) -> Text "module " |++| Text m |++| Text " =" |++| Line |+>| getExpr e
    | ExprNamespace (NamespaceId m, e) -> Text "namespace " |++| Text m |++| Line |++| getExpr e
    | ExprType (TypeId tId, TypeDeclClass (modifiers, generics, args, members)) -> 
        Text "type " |++| Text tId |++| getModifiers modifiers |++| getGenerics generics |++| getPat args |++| Text " =" |++| Line 
        |+>| (members |> Seq.map getMember |> lineblock)
    | ExprType (TypeId tId, t) -> Text "type " |++| Text tId |++| Text " = " |++| getDecl t
    | ExprNew (TypeId tId, e) -> Text "new " |++| Text tId |++| getExpr e
    | ExprInclude (ModuleId m) -> Text "open " |++| Text m
    | ExprIf (cond, thenExpr, elseExprMaybe) ->
        Text "if " |++| getExpr cond |++| LineText "then" |++| indentLineBlock (getExpr thenExpr)
        |++| (elseExprMaybe |> Option.map (fun e -> LineText "else" |++| indentLineBlock (getExpr e)) |> Option.fill (Text ""))
    | ExprFor (pat, collection, expr) ->
        Text "for " |++| getPat pat |++| Text " in " |++| getExpr collection |++| Text " do" |++| indentLineBlock (getExpr expr)
    | ExprWhile (cond, expr) ->
        Text "while " |++| getExprIndentWithParIfSeq cond |++| Text " do" |++| indentLineBlock (getExpr expr)
    | ExprSequence es -> 
        es |> Seq.map getExpr |> delimLineText ""
    | ExprAttribute (attrs, e) ->
        attrs |> List.map (fun (AttributeId x) -> Text x) |> delimSurroundText "; " "[<" ">]" |++| Line
        |++| getExpr e
      
    | ExprTypeConversion (TypeId t, e) -> getExpr e |++| Text (" :> " + t) |> surroundText "(" ")"

and getExprIndentIfSeq e =
    match e with
    | ExprSequence (_::_::_) -> getExpr e |> indentLineBlock
    | _ -> getExpr e
and getExprIndentWithParIfSeq e = getExprIndentIfSeq e |> surroundText "(" ")"

let toFs (Program e) =
    e |> cs2fs.AST.simplify 
    |> cs2fs.AST.Transforms.globalNamespace
    |> cs2fs.AST.Transforms.assignmentAsExpr
    |> cs2fs.AST.Transforms.binaryOpWithString
    |> cs2fs.AST.Transforms.entryPoint
    |> getExpr