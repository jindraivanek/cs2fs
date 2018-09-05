module cs2fs.FSharpOutput

open ExtCore
open cs2fs.AST

let rec intersperse sep =
    function
    | [] -> []
    | [x] -> [x]
    | x::xs -> x::sep::(intersperse sep xs)

let nl = System.Environment.NewLine

type Delim = 
    | Keyword of string
    | DelimOp of string
    | Line
    | LineIndent
let precedence = function
    | Keyword _ -> 0
    | DelimOp _ -> 1
    | Line -> -1
    | LineIndent -> -2

type Block =
    | Text of string
    | Surround of Block * string * string 
    | Delim of Block * Delim * Block

module P =
    type Block =
        | Text of string
        | Line
        | IndentBlock of Block
        | Paren of Block
        | Block of Block list
    
    let rec mapBlock f =
        function
        | Block bs -> List.map (mapBlock f) bs |> Block |> f
        | IndentBlock b -> mapBlock f b |> IndentBlock |> f
        | x -> f x
        
    let printBlock block =
        let printIndent x = ([1..x] |> Seq.map (fun _ -> "    ") |> String.concat "")
        let rec print =
            function
            | Text s -> s
            | Line -> nl
            | _ -> ""
        let rec simplify = function
            | Block [Paren b] -> Paren (Block [b]) |> simplify
            | Block (Block b :: rest) -> Block (b @ rest) |> simplify
            | Block bs -> 
                let rec simplifyList = function
                    | Text "" :: rest -> simplifyList rest
                    | Block [] :: rest -> simplifyList rest
                    | Block b1 :: Block b2 :: rest -> Block (b1 @ b2) :: simplifyList rest
                    | Line :: Paren b :: Line :: rest -> Line :: b :: Line :: simplifyList rest
                    | b :: rest -> b :: simplifyList rest
                    | [] -> []
                let bs' = bs |> simplifyList |> List.map simplify 
                if List.length bs <> List.length bs' then bs' |> Block |> simplify  else bs' |> Block 
            | Paren (Paren b) 
            | Paren b -> b |> simplify |> Paren 
            | IndentBlock (Paren b)
            | IndentBlock b -> simplify b |> IndentBlock
            | x -> x
        let parenStart = Text "("
        let parenEnd = Text ")"
        let rec f indent =
            function
            | Text ""
            | Block [] -> []
            | Text s -> [indent, Text s]
            | Line -> [indent, Line]
            | Block (b::bs) -> f indent b @ f indent (Block bs)
            | IndentBlock b -> f (indent + 1) b
            | Paren b -> f indent (Block [parenStart; b; parenEnd])

        let simplified = block |> simplify
        let simplified = simplified |> f 0
        simplified
        |> Seq.fold (fun (acc,lineBegin) (indent, b) -> 
            acc + (if lineBegin then printIndent indent else "") + print b, match b with |Line -> true |_->false) ("",false)
        |> fst  

let rec ofBlock b =
    let ofDelim p1 o p2 = 
        match o with
        | Keyword t
        | DelimOp t -> P.Block [p1; P.Text t; p2]
        | Line -> P.Block [p1; P.Line; p2]
        | LineIndent -> P.Block [p1; P.IndentBlock p2]
    match b with
    | Text t -> P.Text t
    | Surround (b, x, y) -> P.Block [P.Text x; ofBlock b; P.Text y]
    | Delim (Delim(b1, o1, b2), o2, b3) when precedence o1 < precedence o2 ->
        let x = ofBlock b1
        let y = P.Paren (ofDelim (ofBlock b2) o2 (ofBlock b3))
        ofDelim x o1 y
    | Delim (b1, o1, Delim (b2, o2, b3)) when precedence o1 > precedence o2 ->
        let x = P.Paren (ofDelim (ofBlock b1) o1 (ofBlock b2))
        let y = ofBlock b3
        ofDelim x o2 y
    | Delim (b1, o, b2) -> ofDelim (ofBlock b1) o (ofBlock b2)

let reduce op xs = if Seq.isEmpty xs then Text "" else Seq.reduce op xs
let (|++|) x y = Delim (x, DelimOp " ", y)
let (|+!|) x y = Delim (x, Line, y)
let (|+>|) x y = Delim (x, LineIndent, y)
let block xs = xs |> reduce (|++|)
let lineblock xs = xs |> reduce (|+!|)

let surround head tail body = head + body + tail

let delim sep xs = xs |> String.concat sep

let multi f = function
    | x::(y::tl) as xs -> f xs
    | [x] -> x
    | [] -> f []

let delimSurround sep head tail xs = xs |> (delim sep >> surround head tail)

//let LineText = Text >> (fun x -> Line |++| x)
//let indentLineBlock b = Line |+>| b

let newline b = b |+!| Text ""
let delimText sep xs = xs |> Seq.toList |> intersperse (Text sep) |> block
let delimOp sep xs = xs |> reduce (fun s x -> Delim (s, DelimOp sep, x))
let delimLineText sep xs = xs |> Seq.toList |> intersperse (Text sep) |> lineblock
let surroundText head tail body = Surround (body, head, tail)
let delimSurroundOp sep head tail xs = xs |> (delimOp sep >> surroundText head tail)

let opt o f = Option.map f o |> Option.fill (Text "")

// let singleLiner b =
//     function
//     | Line -> Text "; "
//     | x -> x
//     |> (fun f -> mapBlock f b)

// let removeTopParen = function
//     | Paren x -> x
//     | x -> x

let getModifier =
    function
    | Private -> Text "private"
    | Static -> Text "static"
    | Mutable -> Text "mutable"
    | Override -> Text "override"
    
let getModifierGroup =
    function
    | Private -> 2
    | Static
    | Mutable 
    | Override -> 1

let getModifiersOfGroup rank ms = 
    ms |> Seq.filter (fun x -> getModifierGroup x = rank) 
    |> Seq.map (fun m -> getModifier m |++| Text " ") |> block

let getModifiers ms = [1..2] |> Seq.map (fun r -> getModifiersOfGroup r ms) |> block 

let haveModifier (m: Modifier) ms = ms |> Seq.contains m
let rec getTyp =
    function
    | TypType (TypeId x) -> Text x
    | TypGeneric (GenericId x) -> Text ("'" + x)
    | TypWithGeneric(gs, x) -> getTyp x |++| getGenerics gs 
    | TypFun(t1, t2) -> [t1; t2] |> Seq.map getTyp |> delimOp "->"
    | TypTuple(ts) -> ts |> Seq.map getTyp |> delimOp "*"

and getGenerics gs = 
    if Seq.isEmpty gs then Text ""
    else gs |> Seq.map getTyp |> delimSurroundOp ", " "<" ">"


let rec getPat =
    function
    | PatConst (ConstId c) -> Text c
    | PatWildcard -> Text "_"
    | PatBind (ValId v) -> Text v
    | PatCons (ValId v, ps) -> Text (v + " ") |++| (ps |> Seq.map getPat |> block)
    | PatInfixCons (p1, (ValId v), p2) -> [getPat p1; Text v; getPat p2] |> block
    | PatTuple ts -> ts |> List.map getPat |> delimText ","
    | PatList ts -> ts |> List.map getPat |> delimSurroundOp "; " "[" "]" 
    | PatRecord rows -> rows |> Seq.map (fun (FieldId f, p) -> Text (f + " = ") |++| getPat p) |> delimOp ";" |> surroundText "{" "}" 
    | PatWithType (t, PatWildcard) -> Text ":? " |++| getTyp t
    | PatWithType (t, p) -> [getPat p; getTyp t] |> delimText ":"
    | PatBindAs (ValId v, p) -> [getPat p;  Text v] |> delimText "as"

let getPatNoType =
    function
    | PatWithType (_, p) -> getPat p
    | p -> getPat p

let rec getDecl =
    function
    | TypeDeclRecord rows -> rows |> Seq.map (fun (FieldId f, t) -> [Text f; getDecl t] |> delimOp " : ") |> delimOp "; " |> surroundText "{" "}"
    | TypeDeclUnion rows -> rows |> Seq.map (fun (ValId v, t) -> Text v |++| (t |> Option.map (fun x -> Text " of " |++| getDecl x) |> Option.fill (Text ""))) |> delimOp " | "
    | TypeDeclTuple ts -> ts |> Seq.map getDecl |> delimOp "*"
    | TypeDeclId (TypeId p) -> Text p
    | TypeDeclClass (modifiers, generics, p, members) -> getModifiers modifiers |++| getPat p


let rec getMatch (p, whenE, e) =
    let whenClause = whenE |> Option.map (fun x -> Text "when" |++| getExpr x) |> Option.fill (Text "")
    [getPat p |++| whenClause; getExprM e] |> delimOp "->"

and getMember className x =
    let property pat init getter (haveSetter, setter) =
        let isAutoProperty = Option.isNone getter && (haveSetter = false || Option.isNone setter)
        let header = Text (if isAutoProperty then  "member val " else "member this.") |++| getPatNoType pat |++| (if isAutoProperty then Text " = " |++| getExpr init else Text "")
        let getterText = 
            getter |> Option.map (fun e -> Text "" |+>| (Text "with get() = " |+>| getExpr e)) 
            |> Option.fill (Text "")
        let setterText = 
            setter |> Option.map (fun e -> Text "" |+>| (Text "and set(value) = " |+>| getExpr e)) 
            |> Option.fill (Text (if isAutoProperty then " with get, set" else ""))
        header |++| getterText |++| (if haveSetter then setterText else Text "")
    match x with
    | ExprMember (ValId v, generics, modifiers, thisVal, args, expr) -> 
        getModifiersOfGroup 1 modifiers |++| Text (if haveModifier Override modifiers then "" else "member ") |++| getModifiersOfGroup 2 modifiers 
        |++| (thisVal |> Option.map (fun (ValId x) -> Text(x + ".")) |> Option.fill (Text "")) |++| Text v
        |++| getGenerics generics |++| getPat args |++| Text " = " |+>| getExpr expr
    | ExprMemberConstructor (modifiers, args, expr) -> 
        let init = ExprApp (ExprVal (ValId className), ExprTuple [])
        getModifiersOfGroup 1 modifiers |++| getModifiersOfGroup 2 modifiers |++| Text "new"
        |++| getPat args |++| Text " as this = " |+>| (getExpr init |++| Text "then" |+>| getExpr expr)
    | ExprMemberProperty (pat, init, getter) -> property pat init getter (false, None)
    | ExprMemberPropertyWithSet (pat, init, getter, setter) -> property pat init getter (true, setter)
    | ExprInterfaceImpl (t, e) -> Text "interface " |++| getTyp t |++| Text " with" |+>| getExpr e
    | ExprInherit t  -> Text "inherit " |++| getTyp t |++| Text "()"
    | ExprAttribute (attrs, e) -> 
        attrs |> List.map (fun (AttributeId x) -> Text x) |> delimSurroundOp ";" "[<" ">]"
        |+!| getMember className e
    | ExprType _ -> getExpr x

and getBind header modifiers isRec isFirstRec (p, e) =
    match isRec, isFirstRec with
    | true, true -> Text (header + " rec ")
    | true, false -> Text "and "
    | _ -> Text (header + " ") 
    |++| getModifiers modifiers |++| getPat p |++| Text " = " |++| (getExprM e)

and getExpr =
    function
    | ExprConst (ConstId c) -> Text c
    | ExprVal (ValId v) -> Text v
    | ExprApp (e1, e2) -> [getExpr e1; getExprMP e2] |> block
    | ExprDotApp ((ExprConst _) as e1, e2) 
    | ExprDotApp ((ExprNew _) as e1, e2) 
        -> [getExpr e1; getExpr e2] |> delimOp "."
    | ExprDotApp (e1, e2) -> [getExpr e1; getExpr e2] |> delimOp "."
    | ExprItemApp (e1, e2) -> [getExpr e1; surroundText "[" "]" (e2 |> getExprNP)] |> delimOp "."
    | ExprInfixApp (e1, ValId v, e2) -> [getExprMNP e1; Text v; getExprMNP e2] |> block
    | ExprTuple ts -> ts |> List.map getExpr |> delimOp ","
    | ExprList ts -> ts |> List.map getExpr |> delimSurroundOp ";" "[" "]"
    | ExprArray ts -> ts |> List.map getExpr |> delimSurroundOp ";" "[|" "|]"
    | ExprRecord (copyE, rows) -> 
        let fields = rows |> Seq.map (fun (FieldId f, e) -> Text f |++| Text " = " |++| getExpr e) |> delimOp ";" 
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
        |+!| (rows |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
    | ExprMatchLambda (rows) -> 
        Text "function"
        |+!| (rows |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
    | ExprLambda (args, e) -> 
        Text "fun " |++| (args |> Seq.map getPat |> delimText " ") |++| Text " -> " |++| getExprMNP e
    | ExprWithType (t, e) -> getExpr e |++| Text " : " |++| getTyp t
    | ExprModule (ModuleId m, e) -> Text "module " |++| Text m |++| Text " =" |+>| getExpr e
    | ExprNamespace (NamespaceId m, e) -> Text "namespace " |++| Text m |+!| getExpr e
    | ExprType (TypeId tId, TypeDeclClass (modifiers, generics, args, members)) -> 
        Text "type " |++| Text tId |++| getModifiers modifiers |++| getGenerics generics |++| getPat args |++| Text " ="
        |+>| (members |> Seq.map (getMember tId) |> lineblock)
    | ExprType (TypeId tId, t) -> Text "type " |++| Text tId |++| Text " = " |++| getDecl t
    | ExprNew (t, e) -> Text "new " |++| getTyp t |++| getExpr e
    | ExprDefaultOf t -> Text "Unchecked.defaultof<" |++| getTyp t |++| Text ">"
    | ExprInclude (ModuleId m) -> Text "open " |++| Text m
    | ExprIf (cond, thenExpr, elseExprMaybe) ->
        Text "if " |++| getExprNP cond |+!| Text "then " |++| getExprMNP thenExpr
        |++| opt elseExprMaybe (fun e -> Text "" |+!| Text "else " |++| getExprMNP e)
    | ExprFor (pat, collection, expr) ->
        Text "for " |++| getPat pat |++| Text " in " |++| getExprNP collection |++| Text " do" |+>| (getExprNP expr)
    | ExprWhile (cond, expr) ->
        Text "while " |++| getExprMP cond |++| Text " do" |+>| (getExprNP expr)
    | ExprDo expr -> Text "do " |+>| (getExprNP expr)
    | ExprTry (expr, catches, finallyMaybe) ->
        Text "try" |+>| (getExpr expr)
        |+!| Text "with" |++| (catches |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
        |++| opt finallyMaybe (fun e -> Text "" |+!| Text "finally" |++| (getExpr e))
    | ExprSequence es -> 
        es |> Seq.map getExprNP |> delimLineText ""
    | ExprAttribute (attrs, e) ->
        attrs |> List.map (fun (AttributeId x) -> Text x) |> delimSurroundOp "; " "[<" ">]"
        |+!| getExpr e
    | ExprWithGeneric (g, e) ->
        getExpr e |++| (g |> List.map getTyp |> delimSurroundOp ", " "<" ">")
      
    | ExprTypeConversion (t, e) -> 
        let def = getExpr e |++| Text " :> " |++| (getTyp t)
        match t with
        | TypType (TypeId tt) ->
            match tt with
            | "string" 
            | "int" -> Text (tt + " ") |++| getExpr e
            | _ -> def
        | _ -> def
    | ExprArrayInit (t, ranks) ->
        let n = List.length ranks
        let arrayModule =
            match n with
            | 1 -> "Array"
            | 2 -> "Array2D"
            | 3 -> "Array3D"
            | 4 -> "Array4D"
            | _ -> failwith "not supported array rank"
        Text (arrayModule + ".zeroCreate ") |++| (ranks |> Seq.map getExpr |> delimText " ")
    | ExprReturn e -> Text "return " |++| getExprM e

// and getExprIndentIfMultiline f e =
//     let b = getExpr e
//     let rec blockHaveLine = function
//     | P.Block bs -> bs |> List.exists blockHaveLine
//     | P.IndentBlock b -> blockHaveLine b
//     | P.Paren b -> blockHaveLine b
//     | P.Line -> true
//     | _ -> false
//     if b |> blockHaveLine then
//         getExpr e |> indentLineBlock |> f
//     else getExpr e
// and getExprM e = getExprIndentIfMultiline id e

// and getExprMP e = getExprIndentIfMultiline Paren e

// and getExprNP e = getExpr e |> removeTopParen
// and getExprMNP e = getExprM e |> removeTopParen
and getExprM e = getExpr e

and getExprMP e = getExpr e

and getExprNP e = getExpr e
and getExprMNP e = getExprM e

let toFs (Program e) =
    //printfn "%A" e
    let e =
        e 
        |> cs2fs.AST.Transforms.simplify 
        |> cs2fs.AST.Transforms.lastReturn
        |> cs2fs.AST.Transforms.unitAfterSequenceWithoutValue
        |> cs2fs.AST.Transforms.globalNamespace
        |> cs2fs.AST.Transforms.assignmentAsExpr
        |> cs2fs.AST.Transforms.binaryOpWithString
        |> cs2fs.AST.Transforms.entryPoint
        |> cs2fs.AST.Transforms.typeReplecement
        |> cs2fs.AST.Transforms.constReplacement
        |> cs2fs.AST.Transforms.removeUnnecessaryTypeConversion
    //printfn "%A" e
    let b = e |> getExpr |> ofBlock
    //printfn "%A" b
    b