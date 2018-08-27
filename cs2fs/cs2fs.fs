module cs2fs.Main

open System.Runtime.CompilerServices
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open cs2fs.Utils
open cs2fs.AST
open cs2fs.CSharpActivePatternsExtra
open Microsoft.CodeAnalysis.CSharp.Syntax
open AST.Mk

exception MissingCase of string

let sequence xs = xs |> Seq.toList |> ExprSequence
let (|++|) x y = ExprSequence [x;y]
    
let rec getParentOfType<'t when 't :> SyntaxNode> (node: SyntaxNode) =
    match node.Parent with
    | null -> None
    | :? 't as p -> Some p
    | p -> getParentOfType p

type ErrorMsg =
    static member inline Error(msg: string, [<CallerFilePath>]?filePath: string, [<CallerLineNumber>]?line: int, [<CallerMemberName>]?memberName: string) =
        let filePath = defaultArg filePath ""
        let line = defaultArg line 0
        let memberName = defaultArg memberName ""
        let location = sprintf "at: %s:%i (%s)" filePath line memberName
        sprintf "%s %s" msg location

let missingCaseTreePrinter (n : SyntaxNode) =
    let parents = 
        n |> Seq.unfold (fun x -> 
            x |> Option.ofObj |> Option.bind (fun x -> Option.ofObj x.Parent) |> Option.map (fun x -> x,x)) 
        |> Seq.rev |> Seq.map (fun x -> x.GetType().ToString()) |> String.concat " - "
    let rec f (n : SyntaxNode) =
        match n with
        | null -> "[!null!]"
        | _ -> 
            "[!" + n.GetType().ToString() + "!]" // + "(" + (n.ChildNodes() |> Seq.map f |> String.concat "") + ")"
    parents + " -- " + f n

let inline misssingCaseExpr n = sprintf "Missing case: %A %s" n (missingCaseTreePrinter n)
let inline exceptionExpr (e:System.Exception) n = sprintf "Exception: %A %A %s" e e.StackTrace <| missingCaseTreePrinter n

let fullName (n: ISymbol) =
    match n with
    | null -> ""
    | _ ->
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
            let gs = x.TypeArguments |> Seq.map (fun t -> TypType (TypeId t.Name)) |> Seq.toList
            fullName t, (gs |> Option.condition (List.isEmpty >> not))
        | :? ITypeParameterSymbol as x -> x.Name, None
        | :? IArrayTypeSymbol as x -> x.ToDisplayString(), None
        | _ -> fullName t, None
    let getTypeInfo (n: SyntaxNode) = getTypeInfoFromType (model.GetTypeInfo(n).Type) 
        
    let rec getType (genericSet: #seq<_>) (n:Syntax.TypeSyntax) =  
        let genericSet = set genericSet
        let genericConvert = function | TypType (TypeId t) when Set.contains t genericSet -> TypGeneric (GenericId t) | t -> t
        let (t,gs) =
            match n with
            | :? Syntax.IdentifierNameSyntax as x -> 
                x.Identifier.ValueText.Trim(), None
            | :? Syntax.QualifiedNameSyntax as x -> 
                let rec f (n: NameSyntax) =
                    match n with
                    | :? Syntax.QualifiedNameSyntax as x -> f x.Left + "." + x.Right.Identifier.ValueText.Trim()
                    | :? Syntax.IdentifierNameSyntax as x -> x.Identifier.ValueText.Trim()
                f x, None
            | :? Syntax.GenericNameSyntax as x -> 
                let t = x.Identifier.ValueText.Trim()
                let gs = 
                    match x.TypeArgumentList with
                    | TypeArgumentListSyntax(_,args,_) -> args |> List.map (getType (Set.toSeq genericSet)) |> Some
                t, gs
            | _ ->
                getTypeInfo n
        let tt = genericConvert <| TypType (TypeId t)
        gs |> Option.map (fun g -> TypWithGeneric(List.map genericConvert g, tt)) |> Option.fill tt
    let getTypeAbbr genericSet (n:Syntax.TypeSyntax) cons x =
        match n with
        | null -> x
        | _ -> 
            if n.IsVar then x else
                cons (getType genericSet n, x)
    let getTypePat genericSet (n:Syntax.TypeSyntax) pat = getTypeAbbr genericSet n PatWithType pat
    let getExprWithType genericSet (n:Syntax.TypeSyntax) e = getTypeAbbr genericSet n ExprWithType e
    
    let getParameterSyntax generics (ParameterSyntax(attrs, typ, SyntaxToken ident, equalsValue)) = 
        let genericSet = generics |> Seq.choose (function | TypGeneric (GenericId g) -> Some g | _ -> None) |> set
        let optionalValueExpr = 
            if isNull equalsValue then None else
                ExprBind ([], ident |> mkPatBind, 
                    ExprApp( ExprApp (mkExprVal "defaultArg", mkExprVal ident), equalsValue.Value.ToFullString().Trim() |> ConstId |> ExprConst))
                |> Some
        let bind = mkPatBind ident 
        let bind = if isNull equalsValue then bind else match bind with |PatBind (ValId x) -> PatBind (ValId ("?"+x)) |_ -> bind
        bind |> getTypePat genericSet typ, optionalValueExpr
    
    let getParameters = function
        | ParameterListSyntax(_, prms, _) ->
            if isNull prms then [] else prms
        | _ -> [] 

    let printParamaterList generics ps = 
        let (pars, optionalExrs) = getParameters ps |> List.map (getParameterSyntax generics) |> List.unzip
        pars |> PatTuple, optionalExrs |> List.choose id
    
    let printArgumentList =
        function
        | ArgumentListSyntax(_, args, _)
        | BracketedArgumentListSyntax args ->
            let args = 
                args |> List.map (fun (ArgumentSyntax(_, refOrOut, e)) -> 
                    descend e) |> ExprTuple
            args
        | null -> ExprTuple []
        | _ as n -> raise (misssingCaseExpr n |> ErrorMsg.Error |> MissingCase)
    let defInit typ = 
        //TODO: proper generic type
        ExprDefaultOf (getType [] typ)
    
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
            hasModifier "override", Override
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
        match n with
        | null -> false
        | _ ->
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
        attrs |> Seq.collect (fun (a: Syntax.AttributeListSyntax) -> a.Attributes |> Seq.map (fun x -> AttributeId <| x.Name.ToFullString().Trim())) |> Seq.toList
        |> Option.conditional (List.isEmpty attrs |> not)
    let applyAttributes attrs e =
        getAttributes attrs |> Option.map (fun a -> ExprAttribute (a, e)) |> Option.fill e

    let getVariableDeclarators n = 
        match n with
        | VariableDeclarationSyntax(typ, vars) ->
            vars |> Seq.map
                (function
                 | VariableDeclaratorSyntax(SyntaxToken ident, args, init) -> 
                     mkPatBind ident |> getTypePat (set[]) typ, descendOption init (defInit typ))
        | _ -> raise (misssingCaseExpr n |> ErrorMsg.Error |> MissingCase)
    
    let getGenerics p =
        match p with
        | TypeParameterListSyntax(_, l, _) ->
            l |> List.map (fun t -> GenericId (t.Identifier.Text.Trim()) |> TypGeneric)
        | null 
        | _ -> []

    let rec getMembers classGenerics (n: SyntaxNode) =
        match n with
        | MethodDeclarationSyntax(arity,attrs,returnType,interfaceS,SyntaxToken ident,typePars,pars,typeParsConstrs,block,arrowExpr,_) as n -> 
            let gs = getGenerics typePars
            let (pars, optionalParExprs) = printParamaterList (classGenerics @ gs) pars
            [ 
                ExprMember (ValId ident, gs, getModifiers n, thisIfNotStatic n, pars, descend block |> fun b -> ExprSequence <| optionalParExprs @ [b]) 
                    |> applyAttributes attrs 
            ]
            
        | ConstructorDeclarationSyntax (attrs,_,pars,init,block,_) ->
            match getParameters pars with
            | [] -> []
            | _ ->
            let (pars, optionalParExprs) = printParamaterList (classGenerics) pars
            [ 
                ExprMemberConstructor (getModifiers n, pars, descend block |> fun b -> ExprSequence <| optionalParExprs @ [b]) 
                    |> applyAttributes attrs 
            ]
        
        | PropertyDeclarationSyntax(attrs, typ, explicitInterface, SyntaxToken ident, AccessorListSyntax(_, accessors, _), arrowExpr, equals, _) ->
            let accs = 
                accessors |> List.map (fun (AccessorDeclarationSyntax(attrs, SyntaxToken keyword, block, _)) ->
                    keyword, Option.ofObj block)
            let (propPat, init) = mkPatBind ident |> getTypePat (set[]) typ, defInit typ
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
        | _ -> raise (misssingCaseExpr n |> ErrorMsg.Error |> MissingCase)

    and exprF (node: SyntaxNode) =
        match node with
        | CompilationUnitSyntax(aliases, usings, attrs, members, _) ->
            (usings |> Seq.map descend |> sequence)
            |++| (members |> Seq.map descend |> sequence)
            |> applyAttributes attrs
        | UsingDirectiveSyntax(_, staticKeyword, alias, name, _) ->
            Expr.ExprInclude (ModuleId <| name.ToFullString().Trim())
        | NamespaceDeclarationSyntax(keyword, name, _, externs, usings, members, _, _) ->
            ExprNamespace <| (NamespaceId <| name.ToString(),
                ((usings |> Seq.map descend |> sequence)
                |++| (members |> Seq.map descend |> sequence)))
        | ClassDeclarationSyntax(attrs,keyword,SyntaxToken ident,typePars, bases,constrs,_,members,_,_) as n ->
            let c = n :?> Syntax.ClassDeclarationSyntax
            let s = model.GetDeclaredSymbol(c)
            let baseT = s.BaseType |> Option.ofObj
            let gs = getGenerics typePars
            let bases =
                match bases with
                | BaseListSyntax bases -> 
                    bases
                    |> List.map (fun b -> fst <| getTypeInfo b.Type)
                | _ -> []
            let interfaces = bases |> List.filter (fun b -> baseT |> Option.forall (fun x -> x.Name <> b)) |> set
            let interfaceMembers = 
                interfaces 
                |> Seq.map (fun x -> ExprInterfaceImpl (TypType (TypeId (sprintf "%s" x)), mkExprVal "???")) |> Seq.toList
            let inheritFrom = bases |> List.filter (fun b -> Set.contains b interfaces |> not)
            let inheritMembers = inheritFrom |> List.map (fun b -> ExprInherit (TypType (TypeId b)))
            ExprType (TypeId ident,
                TypeDeclClass (getModifiers node, gs, PatTuple[], inheritMembers @ (members |> List.collect (getMembers gs)) @ interfaceMembers))
            |> applyAttributes attrs

        | MethodDeclarationSyntax _ as n -> ExprType (TypeId "Tmp", TypeDeclClass (getModifiers node, [], PatTuple[], (getMembers [] n)))

        | BaseExpressionSyntax _ -> mkExprVal "base"
        
        | BlockSyntax(_x,stmts,_) -> 
            match stmts with
            | [] -> mkExprVal "()"
            | _ -> stmts |> Seq.map descend |> sequence
        | ReturnStatementSyntax(_,null,_) -> ExprConst (ConstId "()") |> ExprReturn
        | ReturnStatementSyntax(_,e,_) -> descend e |> ExprReturn
        | SimpleLambdaExpressionSyntax(_, par, _, e) -> ExprLambda([getParameterSyntax [] par |> fst], descend e)
        | ParenthesizedLambdaExpressionSyntax(_, pars, _, e) -> ExprLambda([printParamaterList [] pars |> fst], descend e)
        | AnonymousMethodExpressionSyntax(_, _, _, pars, body) -> ExprLambda ([printParamaterList [] pars |> fst], descend body)
        | InvocationExpressionSyntax(e, args) -> ExprApp (descend e, printArgumentList args)
        | MemberAccessExpressionSyntax(e, _, name) -> ExprDotApp (descend e, mkExprVal (name.ToFullString().Trim()))
        | MemberBindingExpressionSyntax(_, name) -> mkExprVal (name.ToFullString().Trim())
        | ElementAccessExpressionSyntax(e, args) -> ExprItemApp (descend e, printArgumentList args)
        | BinaryExpressionSyntax(e1,SyntaxToken op,e2) -> ExprInfixApp (descend e1, ValId (operatorRewrite op), descend e2)
        | AssignmentExpressionSyntax(e1,SyntaxToken op,e2) -> 
            let e1 = descend e1
            let e2 = descend e2
            let withOp o = ExprInfixApp (e1, ValId "<-", ExprInfixApp (e1, ValId o, e2)) 
            match op with
            | "=" -> ExprInfixApp (e1, ValId "<-", e2)
            | "+=" -> withOp "+" 
            | "-=" -> withOp "-" 
        | PrefixUnaryExpressionSyntax(SyntaxToken op,e) as n ->
            let e = descend e
            let withOp o c = [ExprInfixApp (e, ValId "<-", ExprInfixApp (e, ValId o, ExprConst (ConstId c))); e] |> sequence
            match op with
            | "++" -> withOp "+" "1"
            | "--" -> withOp "-" "1"
            | "!" -> ExprApp(mkExprVal "not", e)
            | "-" -> ExprApp(mkExprVal "-", e)
            | x -> raise (sprintf "Unknown prefix operator: %s %s" x (misssingCaseExpr n) |> ErrorMsg.Error |> MissingCase)
        | PostfixUnaryExpressionSyntax(e,SyntaxToken op) as n ->
            //TODO: correct postfix operator sequence
            let e = descend e
            let withOp o c = [ExprInfixApp (e, ValId "<-", ExprInfixApp (e, ValId o, ExprConst (ConstId c))); e] |> sequence
            match op with
            | "++" -> withOp "+" "1"
            | "--" -> withOp "-" "1"
            | x -> raise (sprintf "Unknown postfix operator: %s %s" x (misssingCaseExpr n) |> ErrorMsg.Error |> MissingCase)
            
        | InterpolatedStringExpressionSyntax(_, xs, _) as n -> 
            let parts = 
                xs |> Seq.map (function
                    | :? InterpolatedStringTextSyntax as x -> x.TextToken.Text, None
                    | :? InterpolationSyntax as x -> 
                        //TODO: correct handling of FormatClause - use String.Format?
                        "%O" + (if isNull x.FormatClause then "" else ":" + (x.FormatClause.ToString())), Some x.Expression
                    ) |> Seq.cache
            let formatString = parts |> Seq.map fst |> String.concat ""
            let exprs = parts |> Seq.choose snd
            exprs |> Seq.fold (fun e x -> ExprApp(e, descend x)) (mkExprVal <| "sprintf \"" + formatString + "\"")
        
        | IdentifierNameSyntax(SyntaxToken text) as n -> 
            let identInfo = model.GetSymbolInfo (n:SyntaxNode)
            let thisClassName = getParentOfType<Syntax.ClassDeclarationSyntax> n |> Option.get |> (fun c -> c.Identifier.Text.Trim())
            let isThis = Option.attempt (fun () -> identInfo.Symbol.ContainingSymbol.Name = thisClassName && not(text.StartsWith("this."))) |> Option.fill false
            mkExprVal <| (if isThis then "this." else "") +  text
        | LiteralExpressionSyntax(SyntaxToken text) -> ExprConst <| ConstId text
        | ExpressionStatementSyntax(_,expr,_) -> descend expr
        | ObjectCreationExpressionSyntax(_, typ, args, init) -> 
            match args, init with
            | null, null -> raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)
            | _,null -> ExprNew (getType [] typ, printArgumentList args)
            | null,_ -> ExprNew (getType [] typ, ExprTuple [descend init])
            | _, _ -> raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)
        
        | ParenthesizedExpressionSyntax(_,e,_) -> descend e
        | LocalDeclarationStatementSyntax(isConst, varDecl, _) as n->
            let binds = getVariableDeclarators varDecl
            binds |> Seq.map (fun (p,e) -> ExprBind(getMutableModifier n, p, e)) |> sequence
        
        | EqualsValueClauseSyntax(_, value) -> descend value
        
        | LockStatementSyntax(_, _, e, _, stmt) -> ExprApp (mkExprVal "lock", ExprApp (descend e, ExprLambda ([PatTuple []], descend stmt)))
        | UsingStatementSyntax(_, _, decl, e, _, stmt) ->
            let binds = getVariableDeclarators decl
            binds |> Seq.map (fun (p,e) -> ExprUseBind(p, e)) |> sequence
            |> (fun e -> ExprBind ([], mkPatBind "__", [e; descend stmt] |> sequence))
        | WhileStatementSyntax(_, _, e, _, stmt) ->
            ExprWhile (descend e, descend stmt)
        | ForEachStatementSyntax(_, _, typ, SyntaxToken ident, _, e, _, stmt) ->
            ExprFor (mkPatBind ident |> getTypePat (set[]) typ, descend e, descend stmt)
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
        | ConditionalAccessExpressionSyntax(e1, _, e2) -> 
            ExprInfixApp(descend e1, ValId "?.", descend e2)
        | TryStatementSyntax (_, body, catches, finallyBody) -> 
            let getMatch = function
                | CatchClauseSyntax (_, CatchDeclarationSyntax(_,t,tok,_), filter, block) ->
                    let exprFilter = match filter with |CatchFilterClauseSyntax(_,_,x,_) -> Some x |_ -> None
                    let ident = let x = tok.ValueText in if String.isNullOrEmpty x then PatWildcard else mkPatBind x
                    ident |> getTypePat (set[]) t, exprFilter |> Option.map descend, descend block
            ExprTry(descend body, catches |> List.map getMatch, finallyBody |> Option.ofNull |> Option.map descend)
        | FinallyClauseSyntax (_,body) -> descend body
        | ThrowStatementSyntax (_, e, _) -> ExprApp (mkExprVal "raise", descend e)
        | ArrayCreationExpressionSyntax(t, rs, InitializerExpressionSyntax([]))
        | ArrayCreationExpressionSyntax(t, rs, null) -> 
            ExprArrayInit (getType [] t, rs |> List.collect (fun r -> r.Sizes |> Seq.map descend |> Seq.toList))
        | ArrayCreationExpressionSyntax(_, _, InitializerExpressionSyntax(es)) 
        | ImplicitArrayCreationExpressionSyntax(_,_,_,InitializerExpressionSyntax(es))
        | InitializerExpressionSyntax(es) -> ExprArray(es |> List.map descend)
        
        | PredefinedTypeSyntax (SyntaxToken tok)
        | ThisExpressionSyntax (SyntaxToken tok) -> mkExprVal tok
        | CastExpressionSyntax(_,t,_,e) -> ExprTypeConversion (getType [] t, descend e)
        | TypeOfExpressionSyntax (_,_,t,_) -> ExprWithGeneric([getType [] t], mkExprVal "typeof")

        | SwitchStatementSyntax(_,_, e, _, _, cases, _) ->
            let matches = 
                cases |> List.collect (fun (SwitchSectionSyntax(labels, stmts)) -> 
                    labels |> List.map (function 
                        | :? CaseSwitchLabelSyntax as l -> l.Value.ToString().Trim()
                        | :? DefaultSwitchLabelSyntax -> "_")
                    |> List.map (fun x -> x |> mkPatBind, None, stmts |> List.map descend |> sequence)
                )
            ExprMatch (descend e, matches)

        // not supported syntax
        | BreakStatementSyntax _ -> mkExprVal "break"
        | ContinueStatementSyntax _ -> mkExprVal "continue"
        
        | _ -> raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)

    try
    if tryImplicitConv then
        implicitConv node |> Option.map (fun t -> 
            ExprTypeConversion (t, descendNoImplicit node)) 
        |> Option.fillWith (fun () -> exprF node)
    else exprF node
    with 
    | MissingCase msg -> eprintfn "%s" msg; reraise()
    | e -> 
        failwith (exceptionExpr e node)

let convert (csTree: SyntaxTree) =
    let (@@) x y = System.IO.Path.Combine(x,y)
    let mscorlibPath = (System.AppContext.GetData("FX_DEPS_FILE") |> string |> System.IO.DirectoryInfo).Parent.FullName @@ "mscorlib.dll"
    let mscorlib = MetadataReference.CreateFromFile(mscorlibPath)
    let compilation = CSharpCompilation.Create("MyCompilation", syntaxTrees = [| csTree |], references = [| mscorlib |])
    let model = compilation.GetSemanticModel(csTree, true)
    csTree.GetRoot() |> convertNode true model

[<EntryPoint>]
let main argv =
    eprintfn "Converting: %s" argv.[0]
    let tree = CSharpSyntaxTree.ParseText(System.IO.File.ReadAllText argv.[0])
    let expr = tree |> convert |> Program
    let blockExpr = expr |> cs2fs.FSharpOutput.toFs
    let output = blockExpr |> cs2fs.FSharpOutput.printBlock
    //expr |> (printfn "%A")
    //printfn "==========="
    if argv.Length > 1 then
        System.IO.File.WriteAllText(argv.[1], output) 
    output |> (printfn "%s")
    0 // return an integer exit code
