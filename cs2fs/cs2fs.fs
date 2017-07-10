module cs2fs.Main

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open cs2fs.AST

let sequence xs = xs |> Seq.toList |> ExprSequence
let (|++|) x y = ExprSequence [x;y]

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

let rec missingCaseTreePrinter (n : SyntaxNode) =
    "[!" + n.GetType().ToString() + "(" + (n.ChildNodes() |> Seq.map missingCaseTreePrinter |> String.concat "") + ")!]"

let misssingCaseExpr n = ExprVal (ValId <| missingCaseTreePrinter n)

let rec convertNode tryImplicitConv (model: SemanticModel) (node: SyntaxNode) =
    let descend n = convertNode true model n
    let descendOption n def = defaultArg (n |> Option.map (convertNode true model)) def
    let descendToOption n = n |> Option.map (convertNode true model)
    let descendNoImplicit n = convertNode false model n
    
    let getType (n:Syntax.TypeSyntax) = TypeId <| n.ToString()
    let getTypeAbbr n cons x =
        let t = getType n
        if n.IsVar then x else cons (TypType t, x)
    let getTypePat (n:Syntax.TypeSyntax) pat = getTypeAbbr n PatWithType pat
    let getExprWithType (n:Syntax.TypeSyntax) e = getTypeAbbr n ExprWithType e
    
    let printParamaterList = 
        function
        | null -> PatTuple [] 
        | ParameterListSyntax(_, prms, _) ->
            let prms = 
                if isNull prms then [] else 
                prms |> List.map (fun (ParameterSyntax(attrs, typ, ident, _)) -> 
                    ident.Text |> ValId |> PatBind |> getTypePat typ)
            prms |> PatTuple
    
    let printArgumentList (ArgumentListSyntax(_, args, _)) =
        let args = 
            args |> List.map (fun (ArgumentSyntax(_, refOrOut, e)) -> 
                descend e) |> ExprTuple
        args
    let defInit typ = 
        let (TypeId t) = getType typ
        //TODO: proper generic type
        ExprVal (ValId (sprintf "Unchecked.defaultof<%s>" t))
    
    let getTextModifiers (n:SyntaxNode) =
        match n with
        | :? Syntax.MethodDeclarationSyntax as n -> n.Modifiers |> Seq.toList
        | :? Syntax.FieldDeclarationSyntax as n -> n.Modifiers |> Seq.toList
        | :? Syntax.LocalDeclarationStatementSyntax as n -> n.Modifiers |> Seq.toList
        | _ -> []
        
    let hasModifier t n = getTextModifiers n |> List.exists (fun (m:SyntaxToken) -> m.ValueText = t)
    let getModifiersAll n =
        [
            hasModifier "private", Private
            hasModifier "static", Static
            hasModifier "readonly" >> not, Mutable
        ] |> List.choose (fun (f,m) -> Option.conditional (f n) m)
    let getModifiers n = getModifiersAll n |> List.filter ((<>) Mutable)
    let getMutableModifier n = getModifiersAll n |> List.filter ((=) Mutable)

    let thisIfNotStatic n = if hasModifier "static" n then None else Some (ValId "this")
    
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
        let ignoredConvs = ["IEnumerable"] |> set
        let typeName = 
           if haveConvertedType n then 
               let t = getConvertedType n
               if Set.contains t ignoredConvs then None else Some t 
           else None
        typeName |> Option.map TypeId

    let getAttributes attrs =
        attrs |> Seq.collect (fun (a: Syntax.AttributeListSyntax) -> a.Attributes |> Seq.map (fun x -> AttributeId <| x.Name.ToFullString())) |> Seq.toList
        |> Option.conditional (List.isEmpty attrs |> not)
    let applyAttributes attrs e =
        getAttributes attrs |> Option.map (fun a -> ExprAttribute (a, e)) |> Option.fill e

    let getVariableDeclarators n = 
        match n with
        | VariableDeclarationSyntax(typ, vars) ->
            vars |> Seq.map
                (function
                 | VariableDeclaratorSyntax(ident, args, init) -> 
                     ValId ident.Text |> PatBind |> getTypePat typ, descendOption init (defInit typ))
        | _ -> failwith <| missingCaseTreePrinter n

    let getMembers (n: SyntaxNode) =
        match n with
        | MethodDeclarationSyntax(arity,attrs,returnType,interfaceS,ident,typePars,pars,typeParsConstrs,block,arrowExpr,_) as n -> 
            [ ExprMember (ValId ident.Text, getModifiers n, thisIfNotStatic n, printParamaterList pars, descend block) |> applyAttributes attrs ]
            
        | PropertyDeclarationSyntax(attrs, typ, explicitInterface, ident, AccessorListSyntax(_, accessors, _), arrowExpr, equals, _) ->
            let accs = 
                accessors |> List.map (fun (AccessorDeclarationSyntax(attrs, keyword, block, _)) ->
                    keyword.Text, Option.ofObj block)
            let (propPat, init) = ValId ident.Text |> PatBind |> getTypePat typ, defInit typ
            match accs with
            | [] -> []
            | ["get", getBlock] -> [ExprMemberProperty (propPat, init, descendToOption getBlock) |> applyAttributes attrs]
            | ["get", getBlock; "set", setBlock] -> [ExprMemberPropertyWithSet (propPat, init, descendToOption getBlock, descendToOption setBlock) |> applyAttributes attrs]
            
        | FieldDeclarationSyntax(attrs,varDecl,_) as n -> 
            let binds = getVariableDeclarators varDecl
            binds |> Seq.map (fun (p,e) ->
                if hasModifier "readonly" n then
                    ExprMemberProperty (p, e, None)
                else ExprMemberPropertyWithSet (p, e, None, None)
                 |> applyAttributes attrs
            ) |> Seq.toList
        | _ -> failwith <| missingCaseTreePrinter n

    let exprF node =
        match node with
        | CompilationUnitSyntax(aliases, usings, attrs, members, _) ->
            (usings |> Seq.map descend |> sequence)
            |++| (members |> Seq.map descend |> sequence)
            |> applyAttributes attrs
        | UsingDirectiveSyntax(_, staticKeyword, alias, name, _) ->
            Expr.ExprInclude (ModuleId <| name.ToFullString())
        | NamespaceDeclarationSyntax(keyword, name, _, externs, usings, members, _, _) ->
            ExprNamespace <| (NamespaceId <| name.ToString(),
                ((usings |> Seq.map descend |> sequence)
                |++| (members |> Seq.map descend |> sequence)))
        | ClassDeclarationSyntax(attrs,keyword,ident,typePars,bases,constrs,_,members,_,_) as n ->
            ExprType (TypeId ident.Text,
                TypeDeclClass (getModifiers node, printParamaterList typePars, (members |> List.collect getMembers)))
            |> applyAttributes attrs
        
        | BlockSyntax(_x,stmts,_) -> 
            match stmts with
            | [] -> ExprVal (ValId "()")
            | _ -> stmts |> Seq.map descend |> sequence
        | ReturnStatementSyntax(_,e,_) -> descend e
        | InvocationExpressionSyntax(e, args) -> ExprApp (descend e, printArgumentList args)
        | MemberAccessExpressionSyntax(e, _, name) -> ExprDotApp (descend e, ExprVal (ValId <| name.ToFullString()))
        | BinaryExpressionSyntax(e1,op,e2) -> ExprInfixApp (descend e1, ValId (operatorRewrite op.Text), descend e2)
        | AssignmentExpressionSyntax(e1,op,e2) -> ExprInfixApp (descend e1, ValId "<-", descend e2)
        | IdentifierNameSyntax(token) as n -> 
            let identInfo = model.GetSymbolInfo (n:SyntaxNode)
            let thisClassName = getParentOfType<Syntax.ClassDeclarationSyntax> n |> Option.get |> (fun c -> c.Identifier.Text)
            let isThis = identInfo.Symbol.ContainingSymbol.Name = thisClassName && not(token.Text.StartsWith("this."))
            ExprVal <| (ValId <| (if isThis then "this." else "") +  token.Text)
        | LiteralExpressionSyntax(token) as n -> ExprConst <| ConstId (token.Text)
        | ExpressionStatementSyntax(_,expr,_) -> descend expr
        | ObjectCreationExpressionSyntax(_, typ, args, init) -> 
            ExprNew (getType typ, printArgumentList args)
        
        | ParenthesizedExpressionSyntax(_,e,_) -> descend e
        | LocalDeclarationStatementSyntax(isConst, varDecl, _) as n->
            let binds = getVariableDeclarators varDecl
            binds |> Seq.map (fun (p,e) -> ExprBind(getMutableModifier n, p, e)) |> sequence
        
        | EqualsValueClauseSyntax(_, value) -> descend value
        
        | UsingStatementSyntax(_, _, decl, e, _, stmt) ->
            let binds = getVariableDeclarators decl
            binds |> Seq.map (fun (p,e) -> ExprUseBind(p, e)) |> sequence
            |> (fun e -> ExprBind ([], PatBind(ValId "__"), [e; descend stmt] |> sequence))
        | WhileStatementSyntax(_, _, e, _, stmt) ->
            ExprWhile (descend e, descend stmt)
        | ForEachStatementSyntax(_, _, typ, ident, _, e, _, stmt) ->
            ExprFor (ValId ident.Text |> PatBind |> getTypePat typ, descend e, descend stmt)
        | IfStatementSyntax(_, _, e, _, stmt, elseStmt) ->
            ExprIf(descend e, descend stmt, elseStmt |> Option.ofObj |> Option.map descend)
        | _ -> misssingCaseExpr node

    if tryImplicitConv then
        implicitConv node |> Option.map (fun t -> ExprTypeConversion (t, descendNoImplicit node)) 
        |> Option.fill (exprF node)
    else exprF node

let convert (csTree: SyntaxTree) =
    let mscorlib = MetadataReference.CreateFromFile(typeof<obj>.Assembly.Location)
    let compilation = CSharpCompilation.Create("MyCompilation", syntaxTrees = [| csTree |], references = [| mscorlib |])
    let model = compilation.GetSemanticModel(csTree, true)
    csTree.GetRoot() |> convertNode true model

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
    let expr = tree |> convert |> Program
    let blockExpr = expr |> cs2fs.FSharpOutput.toFs
    let output = blockExpr |> cs2fs.FSharpOutput.printBlock
    expr |> (printfn "%A")
    //blockExpr |> (printfn "%A")
    printfn "==========="
    if argv.Length > 1 then
        System.IO.File.WriteAllText(argv.[1], output) 
    output |> (printfn "%s")
    0 // return an integer exit code
