module cs2fs.Main

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open cs2fs.AST
open cs2fs.CSharpActivePatternsExtra
open Microsoft.CodeAnalysis.CSharp.Syntax
let sequence xs = xs |> Seq.toList |> ExprSequence
let (|++|) x y = ExprSequence [x;y]
    
let rec getParentOfType<'t when 't :> SyntaxNode> (node: SyntaxNode) =
    match node.Parent with
    | null -> None
    | :? 't as p -> Some p
    | p -> getParentOfType p

let missingCaseTreePrinter (n : SyntaxNode) =
    let parents = 
        n |> Seq.unfold (fun x -> 
            x |> Option.ofObj |> Option.bind (fun x -> Option.ofObj x.Parent) |> Option.map (fun x -> x,x)) 
        |> Seq.rev |> Seq.map (fun x -> x.GetType().ToString()) |> String.concat " - "
    let rec f (n : SyntaxNode) =
        match n with
        | null -> "[!null!]"
        | _ -> 
            "[!" + n.GetType().ToString() + "(" + (n.ChildNodes() |> Seq.map f |> String.concat "") + ")!]"
    parents + " -- " + f n

let misssingCaseExpr n = ExprVal (ValId <| sprintf "Missing case: %A %s" n (missingCaseTreePrinter n))
let exceptionExpr (e:System.Exception) n = ExprVal (ValId (sprintf "Exception: %A %A %s" e e.StackTrace <| missingCaseTreePrinter n))

let fullName (n: ISymbol) =
    let rec f (n: ISymbol) = 
        if n.ContainingNamespace <> null && n.ContainingNamespace.Name <> "" then 
            (f n.ContainingNamespace) + n.ContainingNamespace.Name + "." 
        else ""
    f n + n.Name

let rec convertNode tryImplicitConv (model: SemanticModel) (node: SyntaxNode) =
    let descend n = convertNode true model n
    let descendOption n def = defaultArg (n |> Option.map (convertNode true model)) def
    let descendToOption n = n |> Option.map (convertNode true model)
    let descendNoImplicit n = convertNode false model n
    
    let getTypeInfoFromType (t: ITypeSymbol) =
        match t with
        | :? INamedTypeSymbol as x -> 
            let gs = x.TypeArguments |> Seq.map (fun t -> TypType (TypeId (fullName t))) |> Seq.toList
            fullName t, (gs |> Option.condition (List.isEmpty >> not))
        | :? IArrayTypeSymbol as x -> x.ToDisplayString(), None
        | _ -> fullName t, None
    let getTypeInfo (n: SyntaxNode) = getTypeInfoFromType (model.GetTypeInfo(n).Type) 
        
    let getType (n:Syntax.TypeSyntax) =  
        match n with
        | :? Syntax.IdentifierNameSyntax as x -> x.Identifier.Text |> TypeId |> TypType
        | _ ->
            let (t, gs) = getTypeInfo n
            gs |> Option.map (fun g -> TypWithGeneric(g, TypType (TypeId t))) |> Option.fill (TypType (TypeId t))
    let getTypeAbbr genericSet (n:Syntax.TypeSyntax) cons x =
        match n with
        | null -> x
        | _ -> 
            let (t, gs) = getTypeInfo n
            if n.IsVar then x else 
                if (Set.contains t genericSet) then cons (TypGeneric (GenericId t), x)
                else cons (getType n, x)
    let getTypePat genericSet (n:Syntax.TypeSyntax) pat = getTypeAbbr genericSet n PatWithType pat
    let getExprWithType genericSet (n:Syntax.TypeSyntax) e = getTypeAbbr genericSet n ExprWithType e
    
    let getParameterSyntax generics (ParameterSyntax(attrs, typ, ident, _)) = 
        let genericSet = generics |> Seq.choose (function | TypGeneric (GenericId g) -> Some g | _ -> None) |> set
        ident.Text |> ValId |> PatBind |> getTypePat genericSet typ
    
    let printParamaterList generics = 
        function
        | null -> PatTuple [] 
        | ParameterListSyntax(_, prms, _) ->
            let prms = 
                if isNull prms then [] else 
                prms |> List.map (getParameterSyntax generics) 
            prms |> PatTuple
    
    let printArgumentList =
        function
        | ArgumentListSyntax(_, args, _)
        | BracketedArgumentListSyntax args ->
            let args = 
                args |> List.map (fun (ArgumentSyntax(_, refOrOut, e)) -> 
                    descend e) |> ExprTuple
            args
    let defInit typ = 
        //let (TypeId t) = getType typ
        //TODO: proper generic type
        //ExprVal (ValId (sprintf "Unchecked.defaultof<%s>" t))
        ExprDefaultOf (getType typ)
    
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
        let (typeName,genPars) = getTypeInfoFromType typ
        let typeName =
            match typ.SpecialType with
            | SpecialType.System_Object -> "obj"
            | SpecialType.System_String -> "string"
            | SpecialType.None -> typeName
            | _ -> typeName
            
        typeName, genPars
    
    let haveConvertedType (n: SyntaxNode) = 
        let t = model.GetTypeInfo(n)
        t.Type <> null && t.Type <> t.ConvertedType
    
    let implicitConv (n: SyntaxNode) =
        let ignoredConvs = ["System.Collections.IEnumerable"; ""] |> set
        let typ = 
           if haveConvertedType n then 
               let (t,gs) = getConvertedType n
               if Set.contains t ignoredConvs then None else 
                   let tt = TypeId t |> TypType
                   Some (gs |> Option.map (fun g -> TypWithGeneric(g,tt)) |> Option.fill tt) 
           else None
        typ

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
                     ValId ident.Text |> PatBind |> getTypePat (set[]) typ, descendOption init (defInit typ))
        | _ -> seq [PatConst(ConstId "getVariableDeclarators"), misssingCaseExpr n] //<| "getVariableDeclarators " + missingCaseTreePrinter n
    
    let getGenerics p =
        match p with
        | TypeParameterListSyntax(_, l, _) ->
            l |> List.map (fun t -> GenericId t.Identifier.Text |> TypGeneric)
        | null 
        | _ -> []

    let rec getMembers classGenerics (n: SyntaxNode) =
        match n with
        | MethodDeclarationSyntax(arity,attrs,returnType,interfaceS,ident,typePars,pars,typeParsConstrs,block,arrowExpr,_) as n -> 
            let gs = getGenerics typePars
            [ 
                ExprMember (ValId ident.Text, gs, getModifiers n, thisIfNotStatic n, printParamaterList (classGenerics @ gs) pars, descend block) 
                    |> applyAttributes attrs 
            ]
            
        | PropertyDeclarationSyntax(attrs, typ, explicitInterface, ident, AccessorListSyntax(_, accessors, _), arrowExpr, equals, _) ->
            let accs = 
                accessors |> List.map (fun (AccessorDeclarationSyntax(attrs, keyword, block, _)) ->
                    keyword.Text, Option.ofObj block)
            let (propPat, init) = ValId ident.Text |> PatBind |> getTypePat (set[]) typ, defInit typ
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
        | ClassDeclarationSyntax _ as n -> [ exprF n ]
        | _ -> failwith <| "GetMembers " + missingCaseTreePrinter n

    and exprF (node: SyntaxNode) =
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
        | ClassDeclarationSyntax(attrs,keyword,ident,typePars, bases,constrs,_,members,_,_) as n ->
            let c = n :?> Syntax.ClassDeclarationSyntax
            let s = model.GetDeclaredSymbol(c)
            let baseT = s.BaseType |> Option.ofObj
            let gs = getGenerics typePars
            let interfaces = 
                match bases with 
                | BaseListSyntax bases -> 
                    bases |> List.filter (fun b -> baseT |> Option.forall (fun x -> x.Name <> b.ToFullString()))
                    |> List.map (fun b -> b.ToFullString().Trim())
                | _ -> []
            let interfaceMembers = 
                interfaces 
                |> Seq.map (fun x -> ExprInterfaceImpl (TypType (TypeId (sprintf "%A" x)), ExprVal (ValId "???"))) |> Seq.toList
            ExprType (TypeId ident.Text,
                TypeDeclClass (getModifiers node, gs, PatTuple[], (members |> List.collect (getMembers gs)) @ interfaceMembers))
            |> applyAttributes attrs

        | MethodDeclarationSyntax _ as n -> ExprType (TypeId "Tmp", TypeDeclClass (getModifiers node, [], PatTuple[], (getMembers [] n)))
        
        | BlockSyntax(_x,stmts,_) -> 
            match stmts with
            | [] -> ExprVal (ValId "()")
            | _ -> stmts |> Seq.map descend |> sequence
        | ReturnStatementSyntax(_,e,_) -> descend e
        | SimpleLambdaExpressionSyntax(_, par, _, e) -> ExprLambda([getParameterSyntax [] par], descend e)
        | ParenthesizedLambdaExpressionSyntax(_, pars, _, e) -> ExprLambda([printParamaterList [] pars], descend e)
        | InvocationExpressionSyntax(e, args) -> ExprApp (descend e, printArgumentList args)
        | MemberAccessExpressionSyntax(e, _, name) -> ExprDotApp (descend e, ExprVal (ValId <| name.ToFullString()))
        | ElementAccessExpressionSyntax(e, args) -> ExprItemApp (descend e, printArgumentList args)
        | BinaryExpressionSyntax(e1,op,e2) -> ExprInfixApp (descend e1, ValId (operatorRewrite op.Text), descend e2)
        | AssignmentExpressionSyntax(e1,op,e2) -> 
            let withOp o = ExprInfixApp (descend e1, ValId "<-", ExprInfixApp (descend e1, ValId o, descend e2)) 
            match op.Text with
            | "=" -> ExprInfixApp (descend e1, ValId "<-", descend e2)
            | "+=" -> withOp "+" 
            | "-=" -> withOp "-" 
        | PrefixUnaryExpressionSyntax(op,e) as n ->
            let withOp o c = [ExprInfixApp (descend e, ValId "<-", ExprInfixApp (descend e, ValId o, ExprConst (ConstId c))); descend e] |> sequence
            match op.Text with
            | "++" -> withOp "+" "1"
            | "--" -> withOp "-" "1"
            | "!" -> ExprApp(ExprVal(ValId "not"), descend e)
            | "-" -> ExprApp(ExprVal(ValId "-"), descend e)
            | x -> printfn "Unknown prefix operator: %s" x; misssingCaseExpr n
        | PostfixUnaryExpressionSyntax(e,op) as n ->
            //TODO: correct postfix operator sequence
            let withOp o c = [ExprInfixApp (descend e, ValId "<-", ExprInfixApp (descend e, ValId o, ExprConst (ConstId c))); descend e] |> sequence
            match op.Text with
            | "++" -> withOp "+" "1"
            | "--" -> withOp "-" "1"
            | x -> printfn "Unknown postfix operator: %s" x; misssingCaseExpr n
            
        | IdentifierNameSyntax(token) as n -> 
            let identInfo = model.GetSymbolInfo (n:SyntaxNode)
            let thisClassName = getParentOfType<Syntax.ClassDeclarationSyntax> n |> Option.get |> (fun c -> c.Identifier.Text)
            let isThis = Option.attempt (fun () -> identInfo.Symbol.ContainingSymbol.Name = thisClassName && not(token.Text.StartsWith("this."))) |> Option.fill false
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
            ExprFor (ValId ident.Text |> PatBind |> getTypePat (set[]) typ, descend e, descend stmt)
        | ForStatementSyntax(varDecl, initActions, cond, postActions, stmt) ->
            let binds = varDecl |> Option.ofObj |> Option.map getVariableDeclarators 
            let bindsExpr = binds |> Option.map (Seq.map (fun (p,e) -> ExprBind(getMutableModifier varDecl, p, e)) >> Seq.toList) |> Option.fill []
            let initExpr = bindsExpr @ (initActions |> Seq.map descend |> Seq.toList) |> sequence
            let bodyExpr = [descend stmt] @ (postActions |> Seq.map descend |> Seq.toList) |> sequence
            [initExpr; ExprWhile (descend cond, bodyExpr)] |> sequence |> ExprDo
        | IfStatementSyntax(_, _, e, _, stmt, elseStmt) ->
            ExprIf(descend e, descend stmt, elseStmt |> Option.ofObj |> Option.map descend)
        | ElseClauseSyntax(_,e) -> descend e
        | ConditionalExpressionSyntax(e1, _, e2, _, e3) ->
            ExprIf(descend e1, descend e2, Some (descend e3))
            
        | ArrayCreationExpressionSyntax(t, rs, InitializerExpressionSyntax([])) -> 
            ExprArrayInit (getType t, rs |> List.collect (fun r -> r.Sizes |> Seq.map descend |> Seq.toList))
        | ArrayCreationExpressionSyntax(_, _, InitializerExpressionSyntax(es)) 
        | ImplicitArrayCreationExpressionSyntax(_,_,_,InitializerExpressionSyntax(es))
        | InitializerExpressionSyntax(es) -> ExprArray(es |> List.map descend)
        //| OmittedArraySizeExpressionSyntax _ -> ExprVal(ValId "_")
        
        | TypeOfExpressionSyntax (_,_,t,_) -> ExprWithGeneric([getType t], ExprVal(ValId "typeof"))
        
        | _ -> misssingCaseExpr node

    try
    if tryImplicitConv then
        implicitConv node |> Option.map (fun t -> 
            ExprTypeConversion (t, descendNoImplicit node)) 
        |> Option.fill (exprF node)
    else exprF node
    with e -> 
        exceptionExpr e node

let convert (csTree: SyntaxTree) =
    let (@@) x y = System.IO.Path.Combine(x,y)
    let mscorlibPath = (System.AppContext.GetData("FX_DEPS_FILE") |> string |> System.IO.DirectoryInfo).Parent.FullName @@ "mscorlib.dll"
    let mscorlib = MetadataReference.CreateFromFile(mscorlibPath)
    let compilation = CSharpCompilation.Create("MyCompilation", syntaxTrees = [| csTree |], references = [| mscorlib |])
    let model = compilation.GetSemanticModel(csTree, true)
    csTree.GetRoot() |> convertNode true model

[<EntryPoint>]
let main argv =
    let tree = CSharpSyntaxTree.ParseText(System.IO.File.ReadAllText argv.[0])
    let expr = tree |> convert |> Program
    let blockExpr = expr |> cs2fs.FSharpOutput.toFs
    let output = blockExpr |> cs2fs.FSharpOutput.printBlock
    expr |> (printfn "%A")
    printfn "==========="
    if argv.Length > 1 then
        System.IO.File.WriteAllText(argv.[1], output) 
    output |> (printfn "%s")
    0 // return an integer exit code
