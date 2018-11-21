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

let opt o f = Option.map f o |> Option.fill (Text "")

let singleLiner b =
    function
    | Line -> Text "; "
    | x -> x
    |> (fun f -> mapBlock f b)

let removeTopParen = function
    | Paren x -> x
    | x -> x

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
    | TypFun(t1, t2) -> [t1; t2] |> Seq.map getTyp |> delimText " -> " |> Paren
    | TypTuple(ts) -> ts |> Seq.map getTyp |> delimText " * " |> Paren

and getGenerics gs = 
    if Seq.isEmpty gs then Text ""
    else gs |> Seq.map getTyp |> delimSurroundText ", " "<" ">"


let rec getPat =
    function
    | PatConst (_, ConstId c) -> Text c
    | PatWildcard _ -> Text "_"
    | PatBind (_, ValId v) -> Text v
    | PatCons (_, ValId v, ps) -> Text (v + " ") |++| (ps |> Seq.map getPat |> delimText " ")
    | PatInfixCons (_, p1, (ValId v), p2) -> [getPat p1; Text v; getPat p2] |> delimText " " |> Paren
    | PatTuple (_, ts) -> ts |> List.map (getPat >> removeTopParen) |> delimText ", " |> Paren
    | PatList (_, ts) -> ts |> List.map getPat |> delimSurroundText "; " "[" "]" 
    | PatRecord (_, rows) -> rows |> Seq.map (fun (FieldId f, p) -> Text (f + " = ") |++| getPat p) |> delimText "; " |> surroundText "{" "}" 
    | PatWithType (_, t, PatWildcard _) -> Text ":? " |++| getTyp t
    | PatWithType (_, t, p) -> [getPat p; getTyp t] |> delimText " : " |> Paren
    | PatBindAs (_, ValId v, p) -> [getPat p;  Text v] |> delimText " as "

let getPatNoType =
    function
    | PatWithType (_, _, p) -> getPat p
    | p -> getPat p

let rec getDecl =
    function
    | TypeDeclRecord (_, rows) -> rows |> Seq.map (fun (FieldId f, t) -> Text (f + " : ") |++| getDecl t) |> delimText "; " |> surroundText "{" "}"
    | TypeDeclUnion (_, rows) -> rows |> Seq.map (fun (ValId v, t) -> Text v |++| (t |> Option.map (fun x -> Text " of " |++| getDecl x) |> Option.fill (Text ""))) |> delimText " | "
    | TypeDeclTuple (_, ts) -> ts |> Seq.map getDecl |> delimText " * " |> Paren
    | TypeDeclId (_, TypeId p) -> Text p
    | TypeDeclClass (_, modifiers, generics, p, members) -> getModifiers modifiers |++| getPat p


let rec getMatch (_, p, whenE, e) =
    let whenClause = whenE |> Option.map (fun x -> Text " when " |++| getExpr x) |> Option.fill (Text "")
    [getPat p |++| whenClause; getExprM e] |> delimText " -> "

and getMember className x =
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
    | ExprError (_, msg) -> Text <| sprintf "(* ERROR %s *)" msg
    | ExprMember (_, ValId v, generics, modifiers, thisVal, args, expr) -> 
        getModifiersOfGroup 1 modifiers |++| Text (if haveModifier Override modifiers then "" else "member ") |++| getModifiersOfGroup 2 modifiers 
        |++| (thisVal |> Option.map (fun (ValId x) -> Text(x + ".")) |> Option.fill (Text "")) |++| Text v
        |++| getGenerics generics |++| getPat args |++| Text " = " |++| Line |+>| getExpr expr
    | ExprMemberConstructor (ctx, modifiers, args, expr) -> 
        let init = ExprApp (ctx, ExprVal (ctx, ValId className), ExprTuple (ctx, []))
        getModifiersOfGroup 1 modifiers |++| getModifiersOfGroup 2 modifiers |++| Text "new"
        |++| getPat args |++| Text " as this = " |++| Line |+>| (getExpr init |++| Line |++| Text "then" |++| Line |+>| getExpr expr)
    | ExprMemberProperty (_, pat, init, getter) -> property pat init getter (false, None)
    | ExprMemberPropertyWithSet (_, pat, init, getter, setter) -> property pat init getter (true, setter)
    | ExprInterfaceImpl (_, t, e) -> Text "interface " |++| getTyp t |++| Text " with" |++| Line |+>| getExpr e
    | ExprInherit (_, t)  -> Text "inherit " |++| getTyp t |++| Text "()"
    | ExprAttribute (_, attrs, e) -> 
        attrs |> List.map (fun (AttributeId x) -> Text x) |> delimSurroundText "; " "[<" ">]" |++| Line
        |++| getMember className e
    | ExprType _ -> getExpr x

and getBind header modifiers isRec isFirstRec (p, e) =
    match isRec, isFirstRec with
    | true, true -> Text (header + " rec ")
    | true, false -> Text "and "
    | _ -> Text (header + " ") 
    |++| getModifiers modifiers |++| getPat p |++| Text " = " |++| (getExprM e |> removeTopParen)

and getExpr (e:Expr<'a>) =
    match e with
    | ExprError (_, msg) -> Text <| sprintf "(* ERROR %s *)" msg
    | ExprConst (_, ConstId c) -> Text c
    | ExprVal (_, ValId v) -> Text v
    | ExprApp (_, e1, e2) -> [getExpr e1; getExprMP e2] |> delimText " " |> Paren
    | ExprDotApp (_, ((ExprConst _) as e1), e2) 
    | ExprDotApp (_, ((ExprNew _) as e1), e2) 
        -> [getExpr e1 |> Paren; getExpr e2] |> delimText "."
    | ExprDotApp (_, e1, e2) -> [getExpr e1; getExpr e2] |> delimText "."
    | ExprItemApp (_, e1, e2) -> [getExpr e1; surroundText "[" "]" (e2 |> getExprNP)] |> delimText "."
    | ExprInfixApp (_, e1, ValId v, e2) -> [getExprMNP e1; Text v; getExprMNP e2] |> delimText " " |> Paren
    | ExprTuple (_, ts) -> ts |> List.map getExpr |> delimText ", " |> Paren
    | ExprList (_, ts) -> ts |> List.map getExpr |> delimSurroundText "; " "[" "]"
    | ExprArray (_, ts) -> ts |> List.map getExpr |> delimSurroundText "; " "[|" "|]"
    | ExprRecord (_, copyE, rows) -> 
        let fields = rows |> Seq.map (fun (FieldId f, e) -> Text f |++| Text " = " |++| getExpr e) |> delimText "; " 
        let copyStat = copyE |> Option.map (fun x -> getExpr x |++| Text " with ") |> Option.fill (Text "")
        copyStat |++| fields |> surroundText "{" "}"
    | ExprBind (_, modifiers, p, e) -> 
        getBind "let" modifiers false false (p,e)
    | ExprUseBind (_, p, e) -> 
        getBind "use" [] false false (p,e)
    | ExprRecBind (_, bindings) -> 
        let n = Seq.length bindings
        (bindings |> Seq.mapi (fun i x -> getBind "let" [] true (i=0) x |> newline) |> block) 
    | ExprMatch (_, e, rows) -> 
        ([Text "match"; getExpr e; Text "with"] |> delimText " ")
        |++| Line |++| (rows |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
    | ExprMatchLambda (_, rows) -> 
        Text "function"
        |++| Line |++| (rows |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
    | ExprLambda (_, args, e) -> 
        Text "fun " |++| (args |> Seq.map getPat |> delimText " ") |++| Text " -> " |++| getExprMNP e |> Paren
    | ExprWithType (_, t, e) -> getExpr e |++| Text " : " |++| getTyp t
    | ExprModule (_, ModuleId m, e) -> Text "module " |++| Text m |++| Text " =" |++| Line |+>| getExpr e
    | ExprNamespace (_, NamespaceId m, e) -> Text "namespace " |++| Text m |++| Line |++| getExpr e
    | ExprType (_, TypeId tId, TypeDeclClass (_, modifiers, generics, args, members)) -> 
        Text "type " |++| Text tId |++| getModifiers modifiers |++| getGenerics generics |++| getPat args |++| Text " =" |++| Line 
        |+>| (members |> Seq.map (getMember tId) |> lineblock)
    | ExprType (_, TypeId tId, t) -> Text "type " |++| Text tId |++| Text " = " |++| getDecl t
    | ExprNew (_, t, e) -> Text "new " |++| getTyp t |++| getExpr e
    | ExprDefaultOf (_, t) -> Text "Unchecked.defaultof<" |++| getTyp t |++| Text ">"
    | ExprInclude (_, ModuleId m) -> Text "open " |++| Text m
    | ExprIf (_, cond, thenExpr, elseExprMaybe) ->
        Text "if " |++| getExprNP cond |++| LineText "then " |++| getExprMNP thenExpr
        |++| opt elseExprMaybe (fun e -> LineText "else " |++| getExprMNP e)
    | ExprFor (_, pat, collection, expr) ->
        Text "for " |++| getPat pat |++| Text " in " |++| getExprNP collection |++| Text " do" |++| indentLineBlock (getExprNP expr)
    | ExprWhile (_, cond, expr) ->
        Text "while " |++| getExprMP cond |++| Text " do" |++| indentLineBlock (getExprNP expr)
    | ExprDo (_, expr) -> Text "do " |++| indentLineBlock (getExprNP expr)
    | ExprTry (_, expr, catches, finallyMaybe) ->
        Text "try" |++| indentLineBlock (getExpr expr)
        |++| Line |++| Text "with" |++| indentLineBlock (catches |> Seq.map (fun m -> getMatch m) |> delimLineText "| ")
        |++| opt finallyMaybe (fun e -> Line |++| Text "finally" |++| indentLineBlock (getExpr e))
    | ExprSequence (_, es) -> 
        es |> Seq.map getExprNP |> delimLineText ""
    | ExprAttribute (_, attrs, e) ->
        attrs |> List.map (fun (AttributeId x) -> Text x) |> delimSurroundText "; " "[<" ">]" |++| Line
        |++| getExpr e
    | ExprWithGeneric (_, g, e) ->
        getExpr e |++| (g |> List.map getTyp |> delimSurroundText ", " "<" ">")
      
    | ExprTypeConversion (_, t, e) -> 
        let def = getExpr e |++| Text " :> " |++| (getTyp t)
        match t with
        | TypType (TypeId tt) ->
            match tt with
            | "string" 
            | "int" -> Text (tt + " ") |++| getExpr e
            | _ -> def
        | _ -> def
        |> Paren
    | ExprArrayInit (_, t, ranks) ->
        let n = List.length ranks
        let arrayModule =
            match n with
            | 1 -> "Array"
            | 2 -> "Array2D"
            | 3 -> "Array3D"
            | 4 -> "Array4D"
            | _ -> failwith "not supported array rank"
        Text (arrayModule + ".zeroCreate ") |++| (ranks |> Seq.map getExpr |> delimText " ")
    | ExprReturn (_, e) -> Text "return " |++| getExprM e

and getExprIndentIfMultiline f e =
    let b = getExpr e
    let rec blockHaveLine = function
    | Block bs -> bs |> List.exists blockHaveLine
    | IndentBlock b -> blockHaveLine b
    | Paren b -> blockHaveLine b
    | Line -> true
    | _ -> false
    if b |> blockHaveLine then
        getExpr e |> indentLineBlock |> f
    else getExpr e
and getExprM e = getExprIndentIfMultiline id e

and getExprMP e = getExprIndentIfMultiline Paren e

and getExprNP e = getExpr e |> removeTopParen
and getExprMNP e = getExprM e |> removeTopParen

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
        |> cs2fs.AST.Transforms.typeReplacement
        |> cs2fs.AST.Transforms.constReplacement
        |> cs2fs.AST.Transforms.removeUnnecessaryTypeConversion
    //printfn "%A" e
    let b = e |> getExpr
    //printfn "%A" b
    b
