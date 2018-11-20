module cs2fs.Convert

open System.Runtime.CompilerServices
open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open cs2fs.Utils
open cs2fs.AST
open cs2fs.CSharpActivePatternsExtra
open Microsoft.CodeAnalysis.CSharp.Syntax
open AST.Mk

exception MissingCase of string

let sequence ctx xs = ExprSequence(ctx, xs |> Seq.toList) 
    
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

type ConversionResults =
    { Warnings : string list }

let rec convertNode tryImplicitConv (model: SemanticModel) (node: SyntaxNode) : Expr<SyntaxNode> =
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
        | _ -> 
            let name = let x = fullName t in if x = "" then "obj" else x
            name, None
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
                cons (n:>SyntaxNode, getType genericSet n, x)
    let getTypePat genericSet (n:Syntax.TypeSyntax) pat = getTypeAbbr genericSet n PatWithType pat
    let getExprWithType genericSet (n:Syntax.TypeSyntax) e = getTypeAbbr genericSet n ExprWithType e
    
    let getParameterSyntax generics (ParameterSyntax(attrs, typ, SyntaxToken ident, equalsValue) as node) = 
        let genericSet = generics |> Seq.choose (function | TypGeneric (GenericId g) -> Some g | _ -> None) |> set
        let optionalValueExpr = 
            if isNull equalsValue then None else
                ExprBind (node, [], ident |> mkPatBind node,  
                    ExprApp(node, ExprApp (node, mkExprVal node "defaultArg", mkExprVal node ident), (node, equalsValue.Value.ToFullString().Trim() |> ConstId) |> ExprConst))
                |> Some
        let bind = mkPatBind (node:SyntaxNode) ident 
        let bind = if isNull equalsValue then bind else match bind with |PatBind (_, ValId x) -> PatBind (node, ValId ("?"+x)) |_ -> bind
        bind |> getTypePat genericSet typ, optionalValueExpr
    
    let getParameters = function
        | ParameterListSyntax(_, prms, _) ->
            if isNull prms then [] else prms
        | _ -> [] 

    let printParamaterList generics ps = 
        let (pars, optionalExrs) = getParameters ps |> List.map (getParameterSyntax generics) |> List.unzip
        PatTuple(ps, pars), optionalExrs |> List.choose id
    
    let printArgumentList n =
        match n with
        | ArgumentListSyntax(_, args, _)
        | BracketedArgumentListSyntax args ->
            let args = 
                args |> List.map (fun (ArgumentSyntax(_, refOrOut, e)) -> 
                    descend e)
            ExprTuple(n, args)
        | null -> ExprTuple (n, [])
        | _ as n -> raise (misssingCaseExpr n |> ErrorMsg.Error |> MissingCase)
    let defInit typ = 
        //TODO: proper generic type
        ExprDefaultOf (typ :> SyntaxNode, getType [] typ)
    
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

    let getAttributes attrs : List<SyntaxNode * AttributeId> option =
        attrs
        |> Seq.collect (fun (a: Syntax.AttributeListSyntax) -> a.Attributes |> Seq.map (fun x -> x :> SyntaxNode, AttributeId <| x.Name.ToFullString().Trim()))
        |> Seq.toList
        |> Option.conditional (List.isEmpty attrs |> not)
    let applyAttributes (attrs) (e:Expr<'a>) =
        getAttributes attrs |> Option.map (fun l -> ExprAttribute (e.Context, l |> List.map snd, e)) |> Option.fill e

    let getVariableDeclarators n = 
        match n with
        | VariableDeclarationSyntax(typ, vars) ->
            vars |> Seq.map
                (function
                 | VariableDeclaratorSyntax(SyntaxToken ident, args, init) as var -> 
                     mkPatBind (var:>SyntaxNode) ident |> getTypePat (set[]) typ, descendOption init (defInit typ))
        | _ -> raise (misssingCaseExpr n |> ErrorMsg.Error |> MissingCase)
    
    let getGenerics p =
        match p with
        | TypeParameterListSyntax(_, l, _) ->
            l |> List.map (fun t -> GenericId (t.Identifier.Text.Trim()) |> TypGeneric)
        | null 
        | _ -> []

    let rec getMembers classGenerics (n: SyntaxNode) =
        match n with
        | MethodDeclarationSyntax(arity,attrs,returnType,interfaceS,SyntaxToken ident,typePars,parsIn,typeParsConstrs,block,arrowExpr,_) as n -> 
            let gs = getGenerics typePars
            let (pars, optionalParExprs) = printParamaterList (classGenerics @ gs) parsIn
            [ 
                ExprMember (n, ValId ident, gs, getModifiers n, thisIfNotStatic n, pars, descend block |> fun b -> ExprSequence(parsIn :> SyntaxNode, optionalParExprs @ [b])) 
                    |> applyAttributes attrs 
            ]
            
        | ConstructorDeclarationSyntax (attrs,_,parsIn,init,block,_) ->
            match getParameters parsIn with
            | [] -> []
            | _ ->
            let (pars, optionalParExprs) = printParamaterList (classGenerics) parsIn
            [ 
                ExprMemberConstructor (n, getModifiers n, pars, descend block |> fun b -> ExprSequence(parsIn :> SyntaxNode, optionalParExprs @ [b])) 
                    |> applyAttributes attrs 
            ]
        
        | PropertyDeclarationSyntax(attrs, typ, explicitInterface, SyntaxToken ident, AccessorListSyntax(_, accessors, _), arrowExpr, equals, _) ->
            let accs = 
                accessors |> List.map (fun (AccessorDeclarationSyntax(attrs, SyntaxToken keyword, block, _)) ->
                    keyword, Option.ofObj block)
            let (propPat, init) = mkPatBind n ident |> getTypePat (set[]) typ, defInit typ
            match accs with
            | [] -> []
            | ["get", getBlock] -> [ExprMemberProperty (n, propPat, init, descendToOption getBlock) |> applyAttributes attrs]
            | ["get", getBlock; "set", setBlock] -> [ExprMemberPropertyWithSet (n, propPat, init, descendToOption getBlock, descendToOption setBlock) |> applyAttributes attrs]
            
        | FieldDeclarationSyntax(attrs,varDecl,_) as n -> 
            let binds = getVariableDeclarators varDecl
            binds |> Seq.map (fun (p,e) ->
                if hasModifier "readonly" n then
                    ExprMemberProperty (varDecl:>SyntaxNode, p, e, None)
                else ExprMemberPropertyWithSet (varDecl:>SyntaxNode, p, e, None, None)
                 |> applyAttributes attrs
            ) |> Seq.toList
        
        | ClassDeclarationSyntax _ as n -> [ exprF n ]
        | _ -> raise (misssingCaseExpr n |> ErrorMsg.Error |> MissingCase)

    and exprF (node: SyntaxNode) =
        match node with
        | CompilationUnitSyntax(aliases, usings, attrs, members, _) ->
            [  (usings |> Seq.map descend |> sequence node)
               (members |> Seq.map descend |> sequence node) ]
            |> sequence node                   
            |> applyAttributes attrs
        | UsingDirectiveSyntax(_, staticKeyword, alias, name, _) ->
            Expr.ExprInclude (node, ModuleId <| name.ToFullString().Trim())
        | NamespaceDeclarationSyntax(keyword, name, _, externs, usings, members, _, _) ->
            ExprNamespace (node, NamespaceId <| name.ToString(),
                [ (usings |> Seq.map descend |> sequence node)
                  (members |> Seq.map descend |> sequence node) ] |> sequence node)
        | ClassDeclarationSyntax(attrs,keyword,SyntaxToken ident,typePars, basesIn,constrs,_,members,_,_) as n ->
            let c = n :?> Syntax.ClassDeclarationSyntax
            let s = model.GetDeclaredSymbol(c)
            let baseT = s.BaseType |> Option.ofObj
            let gs = getGenerics typePars
            let bases =
                match basesIn with
                | BaseListSyntax bases -> 
                    bases
                    |> List.map (fun b -> fst <| getTypeInfo b.Type)
                | _ -> []
            let interfaces = bases |> List.filter (fun b -> baseT |> Option.forall (fun x -> x.Name <> b)) |> set
            let interfaceMembers = 
                interfaces 
                |> Seq.map (fun x -> ExprInterfaceImpl (n, TypType (TypeId (sprintf "%s" x)), mkExprVal n "???")) |> Seq.toList
            let inheritFrom = bases |> List.filter (fun b -> Set.contains b interfaces |> not)
            let inheritMembers = inheritFrom |> List.map (fun b -> ExprInherit (basesIn :> SyntaxNode, TypType (TypeId b)))
            ExprType (n, TypeId ident,
                TypeDeclClass (n, getModifiers node, gs, PatTuple(n, []), inheritMembers @ (members |> List.collect (getMembers gs)) @ interfaceMembers))
            |> applyAttributes attrs

        | MethodDeclarationSyntax _ as n -> ExprType (n, TypeId "Tmp", TypeDeclClass (n, getModifiers node, [], PatTuple(n, []), (getMembers [] n)))

        | BaseExpressionSyntax _  -> mkExprVal node "base"
        
        | BlockSyntax(_x,stmts,_) -> 
            match stmts with
            | [] -> mkExprVal node "()"
            | _ -> stmts |> Seq.map descend |> sequence node
        | ReturnStatementSyntax(_,null,_) -> ExprReturn(node, ExprConst (node, ConstId "()")) 
        | ReturnStatementSyntax(_,e,_) -> ExprReturn(node, descend e) 
        | SimpleLambdaExpressionSyntax(_, par, _, e) -> ExprLambda(node, [getParameterSyntax [] par |> fst], descend e)
        | ParenthesizedLambdaExpressionSyntax(_, pars, _, e) -> ExprLambda(node, [printParamaterList [] pars |> fst], descend e)
        | AnonymousMethodExpressionSyntax(_, _, _, pars, body) -> ExprLambda (node, [printParamaterList [] pars |> fst], descend body)
        | InvocationExpressionSyntax(e, args) -> ExprApp (node, descend e, printArgumentList args)
        | MemberAccessExpressionSyntax(e, _, name) -> ExprDotApp (node, descend e, mkExprVal (name:>SyntaxNode) (name.ToFullString().Trim()))
        | MemberBindingExpressionSyntax(_, name) -> mkExprVal node (name.ToFullString().Trim())
        | ElementAccessExpressionSyntax(e, args) -> ExprItemApp (node, descend e, printArgumentList args)
        | BinaryExpressionSyntax(e1,SyntaxToken op,e2) -> ExprInfixApp (node, descend e1, ValId (operatorRewrite op), descend e2)
        | AssignmentExpressionSyntax(e1,SyntaxToken op,e2) -> 
            let e1 = descend e1
            let e2 = descend e2
            let withOp o = ExprInfixApp (node, e1, ValId "<-", ExprInfixApp (node, e1, ValId o, e2)) 
            match op with
            | "=" -> ExprInfixApp (node, e1, ValId "<-", e2)
            | "+=" -> withOp "+" 
            | "-=" -> withOp "-" 
        | PrefixUnaryExpressionSyntax(SyntaxToken op,e) as n ->
            let e = descend e
            let withOp o c = [ExprInfixApp (node, e, ValId "<-", ExprInfixApp (node, e, ValId o, ExprConst (node, ConstId c))); e] |> sequence node
            match op with
            | "++" -> withOp "+" "1"
            | "--" -> withOp "-" "1"
            | "!" -> ExprApp(node, mkExprVal node "not", e)
            | "-" -> ExprApp(node, mkExprVal node "-", e)
            | x -> raise (sprintf "Unknown prefix operator: %s %s" x (misssingCaseExpr n) |> ErrorMsg.Error |> MissingCase)
        | PostfixUnaryExpressionSyntax(e,SyntaxToken op) as n ->
            //TODO: correct postfix operator sequence
            let e = descend e
            let withOp o c = [ExprInfixApp (node, e, ValId "<-", ExprInfixApp (node, e, ValId o, ExprConst (node, ConstId c))); e] |> sequence node
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
            exprs |> Seq.fold (fun e x -> ExprApp(node, e, descend x)) (mkExprVal node <| "sprintf \"" + formatString + "\"")
        
        | IdentifierNameSyntax(SyntaxToken text) as n -> 
            let identInfo = model.GetSymbolInfo (n:SyntaxNode)
            let thisClassName = getParentOfType<Syntax.ClassDeclarationSyntax> n |> Option.get |> (fun c -> c.Identifier.Text.Trim())
            let isThis = Option.attempt (fun () -> identInfo.Symbol.ContainingSymbol.Name = thisClassName && not(text.StartsWith("this."))) |> Option.fill false
            let prefix = if isThis then (if identInfo.Symbol.IsStatic then thisClassName+"." else "this.") else ""
            mkExprVal node <| prefix +  text
        | LiteralExpressionSyntax(SyntaxToken text) -> ExprConst (node, ConstId text)
        | ExpressionStatementSyntax(_,expr,_) -> descend expr
        | ObjectCreationExpressionSyntax(_, typ, args, init) -> 
            match args, init with
            | null, null -> raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)
            | _,null -> ExprNew (node, getType [] typ, printArgumentList args)
            | null,_ -> ExprNew (node, getType [] typ, ExprTuple (node, [descend init]))
            | _, _ -> raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)
        
        | ParenthesizedExpressionSyntax(_,e,_) -> descend e
        | LocalDeclarationStatementSyntax(isConst, varDecl, _) as n->
            let binds = getVariableDeclarators varDecl
            binds |> Seq.map (fun (p,e) -> ExprBind(varDecl :> SyntaxNode, getMutableModifier n, p, e)) |> sequence node
        
        | EqualsValueClauseSyntax(_, value) -> descend value
        
        | LockStatementSyntax(_, _, e, _, stmt) -> ExprApp (node, ExprApp (node, mkExprVal node "lock", descend e), ExprLambda (node, [PatTuple (node,[])], descend stmt))
        | UsingStatementSyntax(_, _, decl, e, _, stmt) ->
            let binds = getVariableDeclarators decl
            binds |> Seq.map (fun (p,e) -> ExprUseBind(decl :> SyntaxNode, p, e)) |> sequence node
            |> (fun e -> ExprBind (node, [], mkPatBind node "__", [e; descend stmt] |> sequence node))
        | WhileStatementSyntax(_, _, e, _, stmt) ->
            ExprWhile (node, descend e, descend stmt)
        | ForEachStatementSyntax(_, _, typ, SyntaxToken ident, _, e, _, stmt) ->
            ExprFor (node, mkPatBind node ident |> getTypePat (set[]) typ, descend e, descend stmt)
        | ForStatementSyntax(varDecl, initActions, cond, postActions, stmt) ->
            let binds = varDecl |> Option.ofObj |> Option.map getVariableDeclarators 
            let bindsExpr = binds |> Option.map (Seq.map (fun (p,e) -> ExprBind(node, getMutableModifier varDecl, p, e)) >> Seq.toList) |> Option.fill []
            let initExpr = bindsExpr @ (initActions |> Seq.map descend |> Seq.toList) |> sequence node
            let bodyExpr = [descend stmt] @ (postActions |> Seq.map descend |> Seq.toList) |> sequence node
            (node, [initExpr; ExprWhile (node, descend cond, bodyExpr)] |> sequence node) |> ExprDo
        | IfStatementSyntax(_, _, e, _, stmt, elseStmt) ->
            ExprIf(node, descend e, descend stmt, elseStmt |> Option.ofObj |> Option.map descend)
        | ElseClauseSyntax(_,e) -> descend e
        | ConditionalExpressionSyntax(e1, _, e2, _, e3) ->
            ExprIf(node, descend e1, descend e2, Some (descend e3))
        | ConditionalAccessExpressionSyntax(e1, _, e2) -> 
            ExprInfixApp(node, descend e1, ValId "?.", descend e2)
        | TryStatementSyntax (_, body, catches, finallyBody) -> 
            let getMatch = function
                | CatchClauseSyntax (_, CatchDeclarationSyntax(_,t,tok,_), filter, block) as catchNode ->
                    let exprFilter = match filter with |CatchFilterClauseSyntax(_,_,x,_) -> Some x |_ -> None
                    let ident = let x = tok.ValueText in if String.isNullOrEmpty x then PatWildcard catchNode else mkPatBind catchNode x
                    let typeCheckPat = function 
                        | PatWithType(ctx, t, PatWildcard ctx1) -> PatWithType(ctx, t, PatWildcard ctx1)
                        | PatWithType(ctx, t, PatBind (ctx1, x)) -> PatBindAs(ctx, x, PatWithType(ctx1, t, PatWildcard ctx1))
                        | x -> failwithf "Unexpected case %A" x
                    catchNode, ident |> getTypePat (set[]) t |> typeCheckPat, exprFilter |> Option.map descend, descend block
            ExprTry(node, descend body, catches |> List.map getMatch, finallyBody |> Option.ofNull |> Option.map descend)
        | FinallyClauseSyntax (_,body) -> descend body
        | ThrowStatementSyntax (_, e, _) -> ExprApp (node, mkExprVal node "raise", descend e)
        | ArrayCreationExpressionSyntax(t, rs, InitializerExpressionSyntax([]))
        | ArrayCreationExpressionSyntax(t, rs, null) -> 
            ExprArrayInit (node, getType [] t, rs |> List.collect (fun r -> r.Sizes |> Seq.map descend |> Seq.toList))
        | ArrayCreationExpressionSyntax(_, _, InitializerExpressionSyntax(es)) 
        | ImplicitArrayCreationExpressionSyntax(_,_,_,InitializerExpressionSyntax(es))
        | InitializerExpressionSyntax(es) -> ExprArray(node, es |> List.map descend)
        
        | PredefinedTypeSyntax (SyntaxToken tok)
        | ThisExpressionSyntax (SyntaxToken tok) -> mkExprVal node tok
        | CastExpressionSyntax(_,t,_,e) -> ExprTypeConversion (node, getType [] t, descend e)
        | TypeOfExpressionSyntax (_,_,t,_) -> ExprWithGeneric(node, [getType [] t], mkExprVal node "typeof")

        | SwitchStatementSyntax(_,_, e, _, _, cases, _) ->
            let matches = 
                cases |> List.collect (fun (SwitchSectionSyntax(labels, stmts) as switchNode) -> 
                    labels |> List.map (function 
                        | :? CaseSwitchLabelSyntax as l -> l :> SyntaxNode, l.Value.ToString().Trim()
                        | :? DefaultSwitchLabelSyntax as l -> l :> SyntaxNode, "_")
                    |> List.map (fun (l, x) -> switchNode :> SyntaxNode, x |> mkPatBind l, None, stmts |> List.map descend |> sequence node)
                )
            ExprMatch (node, descend e, matches)

        // not supported syntax
        | BreakStatementSyntax _ -> mkExprVal node "break"
        | ContinueStatementSyntax _ -> mkExprVal node "continue"
        
        | _ ->
            mkExprVal node (sprintf "// UNKNOWN(%A)"  (misssingCaseExpr node |> ErrorMsg.Error))
            //raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)

    try
    if tryImplicitConv then
        implicitConv node |> Option.map (fun t -> 
            ExprTypeConversion (node, t, descendNoImplicit node)) 
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

let convertText (csharp:string) =
    let tree = CSharpSyntaxTree.ParseText(csharp)
    let expr = tree |> convert |> Program
    // expr |> (printfn "%A")
    // printfn "==========="
    let blockExpr = expr |> cs2fs.FSharpOutput.toFs
    let output = blockExpr |> cs2fs.FSharpOutput.printBlock

    output
