module cs2fs

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

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
            (if debug then "(" + node.GetType().Name + ")" else "")) 
        + (if debug then "§" else ""))
        |> Text
    let LineText = Text >> (fun x -> x |++| Line)
    let newline b = block [b; Line]

    let printType (n:Syntax.TypeSyntax) = n.ToString()
    let printTypeAbbr (n:Syntax.TypeSyntax) =
        let t = n.ToString()
        if n.IsVar then "" else (" : " + t)
    let printParmaterList (ParameterListSyntax(left, prms, right)) =
        let prms = 
            prms |> Seq.map (fun (ParameterSyntax(attrs, typ, ident, _)) -> 
                ident.Text + printTypeAbbr typ) |> delim ", "
        left.Text + prms + right.Text
    let defInit typ = (sprintf " = Unchecked.defaultof<%s>" <| printType typ)
        
    match node with
    | CompilationUnitSyntax(aliases, usings, attrs, members, _) ->
        members |> Seq.map descend |> block
    | ClassDeclarationSyntax(attrs,keyword,ident,typePars,bases,constrs,_,members,_,_) ->
        LineText ("type " + ident.Text + "() =") |+>| (members |> Seq.map descend |> block)
    | MethodDeclarationSyntax(arity,attrs,returnType,interfaceS,ident,typePars,pars,typeParsConstrs,block,arrowExpr,_) -> 
        LineText ("member this." + ident.Text + (printParmaterList pars) + " =") |+>| (descend block)
    | BlockSyntax(_x,stmts,_) -> 
        match stmts with
        | [] -> LineText "()"
        | _ -> stmts |> Seq.map (descend >> newline) |> block
    | ReturnStatementSyntax(_,e,_) -> descend e
    | BinaryExpressionSyntax(e1,op,e2) -> [descend e1; Text (" " + op.Text + " "); descend e2] |> block
    | AssignmentExpressionSyntax(e1,op,e2) -> [descend e1; Text (" <- "); descend e2] |> block
    | IdentifierNameSyntax(token) as n -> 
        let identInfo = model.GetSymbolInfo n
        let thisClassName = getParentOfType<Syntax.ClassDeclarationSyntax> n |> Option.get |> (fun c -> c.Identifier.Text)
        let isThis = identInfo.Symbol.ContainingSymbol.Name = thisClassName && not(token.Text.StartsWith("this."))
        Text <| (if isThis then "this." else "") +  token.Text
    | LiteralExpressionSyntax(token) -> Text (token.Text)
    | ExpressionStatementSyntax(_,expr,_) -> descend expr
    | LocalDeclarationStatementSyntax(isConst,varDecl,_) ->
        Text "let " |++| descend varDecl
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
    | FieldDeclarationSyntax(attrs,varDecl,_) -> 
        Text "member val " |++| descend varDecl |++| Text " with get, set" |> newline 
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
        public int Field;
        public int PropGet2 { get {return Field;} }
        public int PropGetSet { get {var x=1; return x;} set {Field = value;} }
        
        public int MyMethod(int x, string s)
        {
            var y = x+1;
            int z = y*2;
            return x+y+z;
        }
    }"

[<EntryPoint>]
let main argv =
    let tree = CSharpSyntaxTree.ParseText(input)
    tree |> convert true |> printBlock |> (printfn "%s")
    tree |> convert false |> (printfn "%A")
    tree |> convert false |> printBlock |> (printfn "%s")
    0 // return an integer exit code
