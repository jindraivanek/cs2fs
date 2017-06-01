module cs2fs

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

let rec intersperse sep =
    function
    | [] -> []
    | [x] -> [x]
    | x::xs -> x::sep::(intersperse sep xs)

let newline = System.Environment.NewLine

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

let (|VariableDeclarationSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclarationSyntax as node ->
      Some (node.Type, node.Variables |> Seq.toList)
    | _ -> None
    
let (|VariableDeclaratorSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclaratorSyntax as node ->
      Some (node.Identifier, node.ArgumentList, Option.ofObj node.Initializer)
    | _ -> None
    
let (|ParameterListSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.ParameterListSyntax as node ->
      Some (node.OpenParenToken, node.Parameters |> Seq.toList, node.CloseParenToken)
    | _ -> None
    
let (|ArgumentListSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.ArgumentListSyntax as node ->
      Some (node.OpenParenToken, node.Arguments |> Seq.toList, node.CloseParenToken)
    | _ -> None
    
let (|FieldDeclarationSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.FieldDeclarationSyntax as node ->
      Some (node.AttributeLists |> Seq.toList, node.Declaration, node.Modifiers |> Seq.toList)
    | _ -> None
    
let rec getParentOfType<'t when 't :> SyntaxNode> (node: SyntaxNode) =
    match node.Parent with
    | null -> None
    | :? 't as p -> Some p
    | p -> getParentOfType p

let rec convertNode debug (model: SemanticModel) (node: SyntaxNode) =
    let descend n = convertNode debug model n
    let descendOption n def = defaultArg (n |> Option.map (convertNode debug model)) def
    let descendInd n = convertNode debug model n |> IndentBlock
    let Text s = 
        ((if debug then "§" else "") +
        (sprintf "%s%s"
            s
            (if debug then "(" + (if isNull node then "null" else node.GetType().Name) + ")" else "")) 
        + (if debug then "§" else ""))
        |> Text
    let LineText = Text >> (fun x -> x |++| Line)
    let newline b = block [b; Line]
    let delimText sep xs = xs |> Seq.toList |> intersperse (Text sep) |> block
    
    let printType (n:Syntax.TypeSyntax) = n.ToString()
    let printTypeAbbr (n:Syntax.TypeSyntax) =
        let t = n.ToString()
        if n.IsVar then "" else (" : " + t)
    let printParamaterList (ParameterListSyntax(left, prms, right)) =
        let prms = 
            prms |> Seq.map (fun (ParameterSyntax(attrs, typ, ident, _)) -> 
                ident.Text + printTypeAbbr typ) |> delim ", "
        left.Text + prms + right.Text
    let printArgumentList (ArgumentListSyntax(left, args, right)) =
        let args = 
            args |> Seq.map (fun (ArgumentSyntax(_, refOrOut, e)) -> 
                descend e) |> delimText ", "
        Text left.Text |++| args |++| Text right.Text
    let defInit typ = (sprintf " = Unchecked.defaultof<%s>" <| printType typ)
    
    let getModifiers (n:SyntaxNode) =
        match n with
        | :? Syntax.MethodDeclarationSyntax as n -> n.Modifiers |> Seq.toList
        | :? Syntax.FieldDeclarationSyntax as n -> n.Modifiers |> Seq.toList
        | :? Syntax.LocalDeclarationStatementSyntax as n -> n.Modifiers |> Seq.toList
        | _ -> []
        
    let hasModifier t n = getModifiers n |> List.exists (fun (m:SyntaxToken) -> m.ValueText = t)
    let privateText n = Text (if hasModifier "private" n then "private " else "") 
    let staticText n = Text (if hasModifier "static" n then "static " else "")
    let thisIfNotStatic n = (if hasModifier "static" n then "" else "this.")
    let mutableIfNotReadonly n = (if hasModifier "readonly" n then "" else "mutable ")
    
    let operatorRewrite =
        function
        | "==" -> "="
        | "!=" -> "<>"
        | x -> x
        
    let getConvertedType (n: SyntaxNode) =
        let t = model.GetTypeInfo(n)
        let typ = if t.Type <> t.ConvertedType then t.ConvertedType else t.Type 
        let typeName =
            match typ.SpecialType with
            | SpecialType.System_Object -> "obj"
            | SpecialType.System_String -> "string"
            | SpecialType.None -> typ.Name
            | _ -> typ.Name
        typeName
    
    let haveConvertedType (n: SyntaxNode) = 
        let t = model.GetTypeInfo(n)
        t.Type <> t.ConvertedType
    
    let implicitConv (n: SyntaxNode) =
        let ignoredConvs = ["IEnumerabe"] |> set
        match n with
        | null -> Text ""
        | _ ->
            let typeName = 
                if haveConvertedType n then 
                    let t = getConvertedType n
                    if Set.contains t ignoredConvs then None else Some t 
                else None
            Text (defaultArg (typeName |> Option.map (fun x -> "(" + x + ")")) "")
        
    implicitConv node |++|
    match node with
    | null -> Text ""
    
    | ParenthesizedExpressionSyntax(left,AssignmentExpressionSyntax(e1,_,e2),right) -> 
        [Text left.Text; descend e1; Text " <- "; descend e2; Text "; "; descend e1; Text right.Text] |> block
    | BinaryExpressionSyntax(e1,op,e2) when op.Text = "+" && getConvertedType e1 = "string" && getConvertedType e2 = "obj" -> 
        [descend e1; Text (" " + operatorRewrite op.Text + " "); Text "(string)"; descend e2] |> block
    
    | CompilationUnitSyntax(aliases, usings, attrs, members, _) ->
        if (Seq.isEmpty usings && members |> Seq.forall (fun n -> n :? Syntax.NamespaceDeclarationSyntax))
        then Text "" else LineText "namespace global"  
        |++| (usings |> Seq.map (descend) |> block)
        |++| (members |> Seq.map descend |> block)
    | UsingDirectiveSyntax(_, staticKeyword, alias, name, _) ->
        LineText ("open " + name.ToFullString())
    | NamespaceDeclarationSyntax(keyword, name, _, externs, usings, members, _, _) ->
        LineText ("namespace " + name.ToFullString())
        |++| (usings |> Seq.map (descend >> newline) |> block)
        |++| (members |> Seq.map (descend >> newline) |> block)
    | ClassDeclarationSyntax(attrs,keyword,ident,typePars,bases,constrs,_,members,_,_) as n ->
        privateText n
        |++| LineText ("type " + ident.Text + "() =") |+>| (members |> Seq.map descend |> block)
    | MethodDeclarationSyntax(arity,attrs,returnType,interfaceS,ident,typePars,pars,typeParsConstrs,block,arrowExpr,_) as n -> 
        privateText n |++| staticText n
        |++| LineText ("member " + thisIfNotStatic n + ident.Text + (printParamaterList pars) + " =") |+>| (descend block)
    | BlockSyntax(_x,stmts,_) -> 
        match stmts with
        | [] -> LineText "()"
        | _ -> stmts |> Seq.map (descend >> newline) |> block
    | ReturnStatementSyntax(_,e,_) -> descend e
    | InvocationExpressionSyntax(e, args) -> descend e |++| printArgumentList args
    | MemberAccessExpressionSyntax(e, op, name) -> descend e |++| Text (op.Text + name.ToFullString())
    | BinaryExpressionSyntax(e1,op,e2) -> [descend e1; Text (" " + operatorRewrite op.Text + " "); descend e2] |> block
    | AssignmentExpressionSyntax(e1,op,e2) -> [descend e1; Text (" <- "); descend e2] |> block
    | IdentifierNameSyntax(token) as n -> 
        let identInfo = model.GetSymbolInfo n
        let thisClassName = getParentOfType<Syntax.ClassDeclarationSyntax> n |> Option.get |> (fun c -> c.Identifier.Text)
        let isThis = identInfo.Symbol.ContainingSymbol.Name = thisClassName && not(token.Text.StartsWith("this."))
        Text <| (if isThis then "this." else "") +  token.Text
    | LiteralExpressionSyntax(token) as n -> implicitConv n |++| Text (token.Text)
    | ExpressionStatementSyntax(_,expr,_) -> descend expr
    | ObjectCreationExpressionSyntax(_, typ, args, init) -> 
        Text ("new " + printType typ) |++| printArgumentList args
    
    | ParenthesizedExpressionSyntax(left,e,right) -> Text left.Text |++| descend e |++| Text right.Text 
    | LocalDeclarationStatementSyntax(isConst,varDecl,_) as n->
        Text ("let " + mutableIfNotReadonly n) |++| descend varDecl
    | VariableDeclarationSyntax(typ, vars) ->
        vars |> Seq.map
            (function
             | VariableDeclaratorSyntax(ident, args, init) -> 
                 Text (ident.Text + printTypeAbbr typ) |++| descendOption init (Text (defInit typ))
             | x -> descend x)
        |> block
    | VariableDeclaratorSyntax(ident, args, init) -> Text ident.Text |++| descendOption init (Text "")
    | EqualsValueClauseSyntax(eqToken, value) -> Text (" " + eqToken.Text + " ") |++| descend value
    | PropertyDeclarationSyntax(attrs, typ, explicitInterface, ident, AccessorListSyntax(_, accessors, _), arrowExpr, equals, _) ->
        let accs = 
            accessors |> List.map (fun (AccessorDeclarationSyntax(attrs, keyword, block, _)) ->
                keyword.Text, Option.ofObj block)
        match accs with
        | [] -> Text ""
        | ["get", None] -> LineText ("member val " + ident.Text + defInit typ)
        | ["get", None; "set", None] -> LineText ("member val " + ident.Text + defInit typ + " with get, set")
        | ["get", Some getBlock] -> 
            LineText ("member this." + ident.Text)
                |+>| (LineText "with get() = " |+>| (descend getBlock))
        | ["get", Some getBlock; "set", Some setBlock] -> 
            LineText ("member this." + ident.Text)
                |+>| ((LineText "with get() = " |+>| descend getBlock) 
                      |++| (LineText "and set(value) = " |+>| descend setBlock))
    | FieldDeclarationSyntax(attrs,varDecl,_) as n -> 
        let accessors = " with get" + (if not (hasModifier "readonly" n) then ", set" else "") 
        Text "member val " |++| descend varDecl |++| Text accessors |> newline
    | UsingStatementSyntax(_, _, decl, e, _, stmt) ->
        LineText "let __ ="
        |+>| (Text "use " |++| descend decl |++| descend e |++| Line |++| descend stmt)
    | WhileStatementSyntax(_, _, e, _, stmt) ->
        Text "while " |++| descend e |++| Text " do" |++| Line |+>| descend stmt
    | ForEachStatementSyntax(_, _, typ, ident, _, e, _, stmt) ->
        Text "for " |++| Text (ident.Text + printTypeAbbr typ + " in ") |++| descend e |++| Text " do" |++| Line |+>| descend stmt
    | IfStatementSyntax(_, _, e, _, stmt, elseStmt) ->
        Text "if " |++| descend e |++| Text " then" |++| Line |+>| descend stmt
        |> (fun x -> if isNull elseStmt then x else x |++| (LineText "else" |+>| descend elseStmt))
    | _ -> LineText <| "[!" + node.GetType().ToString() + "!]"
    | :? Syntax.IdentifierNameSyntax -> Text ""

let convert debug (csTree: SyntaxTree) =
    let mscorlib = MetadataReference.CreateFromFile(typeof<obj>.Assembly.Location)
    let compilation = CSharpCompilation.Create("MyCompilation", syntaxTrees = [| csTree |], references = [| mscorlib |])
    let model = compilation.GetSemanticModel(csTree, true)
    csTree.GetRoot() |> convertNode debug model

let input = @"
    public class MyClass
    {
        public int Prop { get; set; }
        public int PropGet { get; }
        public readonly int Field;
        public int PropGet2 { get {return Field;} }
        public int PropGetSet { get {var x=1; return x;} set {Field = value;} }
        
        private int MyMethod(int x, string s)
        {
            var y = x+1;
            int z = y*2;
            return x+y+z;
        }
    }"

[<EntryPoint>]
let main argv =
    let tree = CSharpSyntaxTree.ParseText(System.IO.File.ReadAllText argv.[0])
    tree |> convert true |> printBlock |> (printfn "%s")
    tree |> convert false |> (printfn "%A")
    printfn "==========="
    let output = tree |> convert false |> printBlock
    if argv.Length > 1 then
        System.IO.File.WriteAllText(argv.[1], output) 
    output |> (printfn "%s")
    0 // return an integer exit code
