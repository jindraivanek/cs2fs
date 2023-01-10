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

type ErrorType =
    | UnknownAssignmentOperator of string
    | UnknownPrefixOperator of string
    | UnknownPostfixOperator of string
    | BreakNotSupported
    | ContinueNotSupported
    | GotoNotSupported
    | UnknownNode

type ConvertError =
    { ProblematicNode : SyntaxNode
      Type : ErrorType }

type ConvertResults =
    { Warnings : string list
      Errors : ConvertError list }
    static member Empty = { Warnings = []; Errors = [] }

let createError node tp = { ProblematicNode = node; Type = tp }
let addError res e = { res with Errors = e :: res.Errors }
let fromError e = { ConvertResults.Empty with Errors = [ e ] }

let unknownNode n = ErrorType.UnknownNode |> createError n |> fromError, Mk.mkError n

let combineResults (r1:ConvertResults) (r2:ConvertResults) =
    { Warnings = r1.Warnings @ r2.Warnings
      Errors = r1.Errors @ r2.Errors }

let collectResults (s: seq<ConvertResults>) =
    Seq.fold combineResults ConvertResults.Empty s
    
let sequenceTree ctx (xs : seq<ConvertResults * Expr<'a>>) =
    let t = xs |> Seq.toList
    let nodes = t |> Seq.map snd
    t |> Seq.map fst |> collectResults, nodes |> sequence ctx

let rec convertNode tryImplicitConv (model: SemanticModel) (node: SyntaxNode) : ConvertResults * Expr<SyntaxNode>=
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
        gs |> Option.map (fun g -> TypWithGeneric(List.map genericConvert g, tt)) |> Option.defaultValue tt
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
                ExprBind (node, [], [ident |> mkPatBind node],  
                    ExprApp(node, ExprApp (node, mkExprVal node "defaultArg", mkExprVal node ident), (node, equalsValue.Value.ToFullString().Trim() |> ConstId) |> ExprConst))
                |> Some
        let bind = mkPatBind (node:SyntaxNode) ident 
        let bind = if isNull equalsValue then bind else match bind with |PatBind (_, ValId x) -> PatBind (node, ValId ("?"+x)) |_ -> bind
        bind |> getTypePat genericSet typ, optionalValueExpr
    
    let getParameters = function
        | ParameterListSyntax(_, prms, _) ->
            //if isNull prms then [] else 
            prms
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
            args |> Seq.map fst |> collectResults,                
            ExprTuple(n, args |> List.map snd)
        | null -> ConvertResults.Empty, ExprTuple (n, [])
        | _ as n -> unknownNode n
        // raise (misssingCaseExpr n |> ErrorMsg.Error |> MissingCase)
    let defInit typ = 
        //TODO: proper generic type
        ConvertResults.Empty, ExprDefaultOf (typ :> SyntaxNode, getType [] typ)
    
    let getTextModifiers (n:SyntaxNode) =
        match n with
        | :? Syntax.MethodDeclarationSyntax as n -> n.Modifiers |> Seq.toList
        | :? Syntax.FieldDeclarationSyntax as n -> n.Modifiers |> Seq.toList
        | :? Syntax.LocalDeclarationStatementSyntax as n -> n.Modifiers |> Seq.toList
        | :? Syntax.PropertyDeclarationSyntax as n -> n.Modifiers |> Seq.toList
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
                   Some (gs |> Option.map (fun g -> TypWithGeneric(g,tt)) |> Option.defaultValue tt) 
           else None
        typ

    let getAttributes attrs : List<SyntaxNode * AttributeId> option =
        attrs
        |> Seq.collect (fun (a: Syntax.AttributeListSyntax) -> a.Attributes |> Seq.map (fun x -> x :> SyntaxNode, AttributeId <| x.Name.ToFullString().Trim()))
        |> Seq.toList
        |> Option.conditional (List.isEmpty attrs |> not)
    let applyAttributes (attrs) (e:Expr<'a>) : Expr<'a> =
        getAttributes attrs |> Option.map (fun l -> ExprAttribute (e.Context, l |> List.map snd, e)) |> Option.defaultValue e

    let getVariableDeclarators n = 
        match n with
        | VariableDeclarationSyntax(typ, vars) ->
            let results = 
                vars |> List.map
                    (function
                     | VariableDeclaratorSyntax(SyntaxToken ident, args, init) as var ->
                        let res, o = descendOption init (defInit typ)
                        res, mkPatBind (var:>SyntaxNode) ident |> getTypePat (set[]) typ, o)
            results             
        | _ -> 
            let res, n = unknownNode n //raise (misssingCaseExpr n |> ErrorMsg.Error |> MissingCase)
            [ res, mkPatBind node "ERROR", n ]
    
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
            let body = if not (isNull arrowExpr) then arrowExpr.Expression :> SyntaxNode else block :> SyntaxNode
            let blockRes, block = descend body

            blockRes,
            [ 
                ExprMember (n, ValId ident, gs, getModifiers n, thisIfNotStatic n, pars, block |> fun b -> ExprSequence(parsIn :> SyntaxNode, optionalParExprs @ [b])) 
                    |> applyAttributes attrs 
            ]
            
        | ConstructorDeclarationSyntax (attrs,_,parsIn,init,block,_) ->
            match getParameters parsIn with
            | [] -> ConvertResults.Empty, []
            | _ ->
            let (pars, optionalParExprs) = printParamaterList (classGenerics) parsIn
            let blockRes, block = descend block

            blockRes,
            [ 
                ExprMemberConstructor (n, getModifiers n, pars, block |> fun b -> ExprSequence(parsIn :> SyntaxNode, optionalParExprs @ [b])) 
                    |> applyAttributes attrs 
            ]
        
        | PropertyDeclarationSyntax(attrs, typ, explicitInterface, SyntaxToken ident, AccessorListSyntax(_, accessors, _), arrowExpr, equals, _) ->
            let accs = 
                accessors |> List.map (fun (AccessorDeclarationSyntax(attrs, SyntaxToken keyword, block, _)) ->
                    keyword, Option.ofObj block)
            let (propPat, (r, init)) = mkPatBind n ident |> getTypePat (set[]) typ, defInit typ
            match accs with
            | [] -> ConvertResults.Empty, []
            | ["get", getBlock] -> 
                let getBlockO = descendToOption getBlock
                getBlockO |> Option.map fst |> Option.defaultValue ConvertResults.Empty |> combineResults r,
                [ExprMemberProperty (n, getModifiers n, propPat, init, getBlockO |> Option.map snd) |> applyAttributes attrs]
            | ["get", getBlock; "set", setBlock] -> 
                let getBlockO = descendToOption getBlock
                let setBlockO = descendToOption setBlock

                [ yield getBlockO |> Option.map fst; yield setBlockO |> Option.map fst; yield Some r ] |> Seq.choose id |> collectResults,
                [ExprMemberPropertyWithSet (n, getModifiers n, propPat, init, getBlockO |> Option.map snd, setBlockO |> Option.map snd) |> applyAttributes attrs]
            | _ -> let r, e = unknownNode n in r, [ e ]

            
        | FieldDeclarationSyntax(attrs,varDecl,_) -> 
            let binds = getVariableDeclarators varDecl
            let results =
                binds |> Seq.map (fun (r, p, e) ->
                    r, 
                    if hasModifier "readonly" n then
                        ExprMemberProperty (varDecl:>SyntaxNode, getModifiers n, p, e, None)
                    else ExprMemberPropertyWithSet (varDecl:>SyntaxNode, getModifiers n, p, e, None, None)
                     |> applyAttributes attrs
                ) |> Seq.toList
            results |> List.map fst |> collectResults,
            results |> List.map snd           
        
        | ClassDeclarationSyntax _ as n -> let res, e = exprF n in res, [ e ]
        | StructDeclarationSyntax _ as n -> let res, e = exprF n in res, [ e ]
        | _ -> let r, e = unknownNode n in r, [ e ]

    and exprF (node: SyntaxNode) : ConvertResults * Expr<SyntaxNode> =
        match node with
        | CompilationUnitSyntax(aliases, usings, attrs, members, _) ->
            let results1, uses = usings |> Seq.map descend |> sequenceTree node
            let results2, mems = members |> Seq.map descend |> sequenceTree node

            combineResults results1 results2,
            [  uses; mems ] |> sequence node
            |> applyAttributes attrs
        | UsingDirectiveSyntax(_, staticKeyword, alias, name, _) ->
            ConvertResults.Empty,
            Expr.ExprInclude (node, ModuleId <| name.ToFullString().Trim())
        | NamespaceDeclarationSyntax(keyword, name, _, externs, usings, members, _, _) ->
            let results1, usings = usings |> Seq.map descend |> sequenceTree node
            let results2, members = members |> Seq.map descend |> sequenceTree node
        
            combineResults results1 results2,
            ExprNamespace (node, NamespaceId <| name.ToString(), [ usings; members ] |> sequence node)
        | StructDeclarationSyntax(attrs,keyword,SyntaxToken ident,typePars, basesIn,constrs,_,members,_,_) as n ->
            let c = n :?> Syntax.StructDeclarationSyntax
            let s = model.GetDeclaredSymbol(c)
            let gs = getGenerics typePars
            
            let members = members |> List.map (getMembers gs)

            members |> Seq.map fst |> collectResults,
            ExprType (n, TypeId ident,
                TypeDeclClass (n, getModifiers node, gs, PatTuple(n, []), (members |> List.collect snd)))
            |> applyAttributes attrs
            |> function
                | ExprAttribute (c, attrs, e) -> ExprAttribute (c, AttributeId "Struct" :: attrs, e)
                | e -> ExprAttribute (e.Context, AttributeId "Struct" :: [], e)
                
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
            
            let members = members |> List.map (getMembers gs)

            // Constructor is tricky, first let's check if there is a default constructor
            //members |> Seq.tryFind(fun (_, exp) -> exp.)


            members |> Seq.map fst |> collectResults,
            ExprType (n, TypeId ident,
                TypeDeclClass (n, getModifiers node, gs, PatTuple(n, []), inheritMembers @ (members |> List.collect snd) @ interfaceMembers))
            |> applyAttributes attrs
        
        
        | MethodDeclarationSyntax _ as n -> 
            let results, members = getMembers [] n
            results,
            ExprType (n, TypeId "Tmp", TypeDeclClass (n, getModifiers node, [], PatTuple(n, []), members))

        | BaseExpressionSyntax _  -> ConvertResults.Empty, mkExprVal node "base"
        
        | BlockSyntax(_x,stmts,_) -> 
            match stmts with
            | [] -> ConvertResults.Empty, mkExprVal node "()"
            | _ -> stmts |> Seq.map descend |> sequenceTree node
        | ReturnStatementSyntax(_,null,_) -> ConvertResults.Empty, ExprReturn(node, ExprConst (node, ConstId "()")) 
        | ReturnStatementSyntax(_,e,_) -> let res, desc = descend e in res, ExprReturn(node, desc) 
        | SimpleLambdaExpressionSyntax(_, par, _, e) -> let res, desc = descend e in res, ExprLambda(node, [getParameterSyntax [] par |> fst], desc)
        | ParenthesizedLambdaExpressionSyntax(_, pars, _, e) -> let res, desc = descend e in res, ExprLambda(node, [printParamaterList [] pars |> fst], desc)
        | AnonymousMethodExpressionSyntax(_, _, _, pars, body) -> let res, desc = descend body in res, ExprLambda (node, [printParamaterList [] pars |> fst], desc)
        | LocalFunctionStatementSyntax(SyntaxToken ident, typ, typPar, pars, clauses, body, arrowExpr) ->
            let modifiers = getModifiers node
            let res, desc = if not (isNull arrowExpr) then descend arrowExpr else descend body
            res, ExprBind (node, modifiers, mkPatBind node ident :: [printParamaterList [] pars |> fst], desc)
        | InvocationExpressionSyntax(e, args) -> 
            let res, desc = descend e 
            let res2, args = printArgumentList (args :> SyntaxNode)
            combineResults res res2, ExprApp (node, desc, args)
        | MemberAccessExpressionSyntax(e, _, name) -> let res, desc = descend e in res, ExprDotApp (node, desc, mkExprVal (name:>SyntaxNode) (name.ToFullString().Trim()))
        | MemberBindingExpressionSyntax(_, name) -> ConvertResults.Empty, mkExprVal node (name.ToFullString().Trim())
        | ElementAccessExpressionSyntax(e, args) ->
            let res, desc = descend e
            let res2, args = printArgumentList (args :> SyntaxNode)
            
            combineResults res res2, ExprItemApp (node, desc, args)
        | BinaryExpressionSyntax(e1,SyntaxToken op,e2) ->
            let res1, desc1 = descend e1
            let res2, desc2 = descend e2
            
            combineResults res1 res2, ExprInfixApp (node, desc1, ValId (operatorRewrite op), desc2)
        | AssignmentExpressionSyntax(e1,SyntaxToken op,e2) -> 
            let res1, e1 = descend e1
            let res2, e2 = descend e2
            let withOp o = ExprInfixApp (node, e1, ValId "<-", ExprInfixApp (node, e1, ValId o, e2))

            let res = combineResults res1 res2

            match op with
            | "=" -> res, ExprInfixApp (node, e1, ValId "<-", e2)
            | "+=" -> res, withOp "+" 
            | "-=" -> res, withOp "-"
            | _ -> ErrorType.UnknownAssignmentOperator op |> createError node |> addError res, Mk.mkError node

        | PrefixUnaryExpressionSyntax(SyntaxToken op,e) as n ->
            let res, e = descend e
            let withOp o c = [ExprInfixApp (node, e, ValId "<-", ExprInfixApp (node, e, ValId o, ExprConst (node, ConstId c))); e] |> sequence node
            match op with
            | "++" -> res, withOp "+" "1"
            | "--" -> res, withOp "-" "1"
            | "!" -> res, ExprApp(node, mkExprVal node "not", e)
            | "-" -> res, ExprApp(node, mkExprVal node "-", e)
            | x -> ErrorType.UnknownPrefixOperator x |> createError node |> addError res, Mk.mkError node
        | PostfixUnaryExpressionSyntax(e,SyntaxToken op) as n ->
            //TODO: correct postfix operator sequence
            let res, e = descend e
            let withOp o c = [ExprInfixApp (node, e, ValId "<-", ExprInfixApp (node, e, ValId o, ExprConst (node, ConstId c))); e] |> sequence node
            match op with
            | "++" -> res, withOp "+" "1"
            | "--" -> res, withOp "-" "1"
            | x -> ErrorType.UnknownPostfixOperator x |> createError node |> addError res, Mk.mkError node
            
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
            let childs = exprs |> Seq.map (fun e -> descend e) |> Seq.toList
            childs |> Seq.map fst |> collectResults,
            childs |> Seq.map snd |> Seq.fold (fun e x -> ExprApp(node, e, x)) (mkExprVal node <| "sprintf \"" + formatString + "\"")
        
        | IdentifierNameSyntax(SyntaxToken text) as n -> 
            let identInfo = model.GetSymbolInfo (n:SyntaxNode)
            let thisClassName = getParentOfType<Syntax.TypeDeclarationSyntax> n |> Option.get |> (fun c -> c.Identifier.Text.Trim())
            let isThis = 
                identInfo.Symbol |> Option.ofObj
                |> Option.bind (fun symbol -> Option.ofObj symbol.ContainingSymbol)
                |> Option.map (fun containing -> containing.Name = thisClassName && not(text.StartsWith("this.")))
                |> Option.defaultValue false
            let prefix = if isThis then (if identInfo.Symbol.IsStatic then thisClassName+"." else "this.") else ""
            
            ConvertResults.Empty,
            mkExprVal node <| prefix +  text
        | LiteralExpressionSyntax(SyntaxToken text) -> ConvertResults.Empty, ExprConst (node, ConstId text)
        | ExpressionStatementSyntax(_,expr,_) -> descend expr
        | ObjectCreationExpressionSyntax(_, typ, args, init) -> 
            match args, init with
            | null, null -> unknownNode node // raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)
            | _,null -> let res, e = printArgumentList (args :> SyntaxNode) in res, ExprNew (node, getType [] typ, e)
            | null,_ ->  let res, desc = descend init in res, ExprNew (node, getType [] typ, ExprTuple (node, [desc]))
            | _, _ -> unknownNode node // raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)
        
        | ParenthesizedExpressionSyntax(_,e,_) -> descend e
        | LocalDeclarationStatementSyntax(isConst, varDecl, _) as n->
            let binds = getVariableDeclarators varDecl
            binds |> Seq.map (fun (r, p, e) -> r, ExprBind(varDecl :> SyntaxNode, getMutableModifier n, [p], e)) |> sequenceTree node
        
        | EqualsValueClauseSyntax(_, value) -> descend value
        
        | LockStatementSyntax(_, _, e, _, stmt) ->
            let res1, stmt = descend stmt
            let res2, e = descend e

            combineResults res1 res2,
            ExprApp (node, ExprApp (node, mkExprVal node "lock", e), ExprLambda (node, [PatTuple (node,[])], stmt))
        | UsingStatementSyntax(_, _, decl, e, _, stmt) ->
            let binds = getVariableDeclarators decl
            binds |> Seq.map (fun (r, p, e) -> r, ExprUseBind(decl :> SyntaxNode, [p], e)) |> sequenceTree node
            |> (fun (r, e) -> 
                let res, stmt = descend stmt
                combineResults res r,
                ExprBind (node, [], [mkPatBind node "__"], [e; stmt] |> sequence node))
        | WhileStatementSyntax(_, _, e, _, stmt) ->
            let res1, stmt = descend stmt
            let res2, e = descend e

            combineResults res1 res2,
            ExprWhile (node, e, stmt)
        | ForEachStatementSyntax(_, _, typ, SyntaxToken ident, _, e, _, stmt) ->
            let res1, stmt = descend stmt
            let res2, e = descend e

            combineResults res1 res2,
            ExprFor (node, mkPatBind node ident |> getTypePat (set[]) typ, e, stmt)
        | ForStatementSyntax(varDecl, initActions, cond, postActions, stmt) ->
            let binds = varDecl |> Option.ofObj |> Option.map getVariableDeclarators 
            let bindsExpr = binds |> Option.map (Seq.map (fun (r, p, e) -> r, ExprBind(node, getMutableModifier varDecl, [p], e)) >> Seq.toList) |> Option.defaultValue []
            let initExpr = bindsExpr @ (initActions |> Seq.map descend |> Seq.toList) |> sequenceTree node
            let whileExpr =
                let bodyRes, bodyExpr = [descend stmt] @ (postActions |> Seq.map descend |> Seq.toList) |> sequenceTree node
                let condRes, cond = descend cond
                combineResults bodyRes condRes, ExprWhile (node, cond, bodyExpr)
            let finalRes, finalExpr = [initExpr; whileExpr ] |> sequenceTree node
            finalRes,
            ExprDo (node, finalExpr)
        | IfStatementSyntax(_, _, e, _, stmt, elseStmt) ->
            let res1, stmt = descend stmt
            let res2, e = descend e
            let elseStmtDesc = elseStmt |> Option.ofObj |> Option.map descend
            let elseStmt = elseStmtDesc |> Option.map snd
            [ yield Some res1; yield Some res2; yield elseStmtDesc |> Option.map fst ] |> Seq.choose id |> collectResults,
            ExprIf(node, e, stmt, elseStmt)
        | ElseClauseSyntax(_,e) -> descend e
        | ConditionalExpressionSyntax(e1, _, e2, _, e3) ->
            let res1, e1 = descend e1
            let res2, e2 = descend e2
            let res3, e3 = descend e3
            collectResults [ res1; res2; res3 ],
            ExprIf(node, e1, e2, Some e3)
        | ConditionalAccessExpressionSyntax(e1, _, e2) -> 
            let res1, e1 = descend e1
            let res2, e2 = descend e2
            combineResults res1 res2,
            ExprInfixApp(node, e1, ValId "?.", e2)
        | TryStatementSyntax (_, body, catches, finallyBody) -> 
            let getMatch = function
                | CatchClauseSyntax (_, catchDecl, filter, block) as catchNode ->
                    let exprFilter = match filter with |CatchFilterClauseSyntax(_,_,x,_) -> Some x |_ -> None
                    let basePat =
                        match catchDecl with
                        | CatchDeclarationSyntax(_,t,tok,_) ->
                            let ident =
                                let x = tok.ValueText in
                                if String.isNullOrEmpty x then PatWildcard catchNode
                                else mkPatBind catchNode x
                            let typeCheckPat = function 
                                | PatWithType(ctx, t, PatWildcard ctx1) -> PatWithType(ctx, t, PatWildcard ctx1)
                                | PatWithType(ctx, t, PatBind (ctx1, x)) -> PatBindAs(ctx, x, PatWithType(ctx1, t, PatWildcard ctx1))
                                | x -> failwithf "Unexpected case %A" x
                            ident |> getTypePat (set[]) t |> typeCheckPat
                        | null -> PatWildcard catchNode

                    let exprFilterO = exprFilter |> Option.map descend
                    let blockRes, block = descend block
                    [ yield Some blockRes; yield exprFilterO |> Option.map fst ] |> Seq.choose id |> collectResults,
                    (catchNode, basePat, exprFilterO |> Option.map snd, block)

            let catches = catches |> List.map getMatch
            let finallyBodyO = finallyBody |> Option.ofObj |> Option.map descend
            let bodyRes, body = descend body
            [ yield! catches |> Seq.map (fst >> Some); yield finallyBodyO |> Option.map fst; yield Some bodyRes ] |> Seq.choose id |> collectResults,
            ExprTry(node, body, catches |> List.map snd, finallyBodyO |> Option.map snd)
        | FinallyClauseSyntax (_,body) -> descend body
        | ThrowStatementSyntax (_, null, _) -> ConvertResults.Empty, ExprApp (node, mkExprVal node "reraise", mkExprVal node "()")
        | ThrowStatementSyntax (_, e, _) -> let res, desc = descend e in res, ExprApp (node, mkExprVal node "raise", desc)
        | ArrayCreationExpressionSyntax(t, rs, InitializerExpressionSyntax([]))
        | ArrayCreationExpressionSyntax(t, rs, null) ->
            let results = rs |> List.collect (fun r -> r.Sizes |> Seq.map descend |> Seq.toList)
            
            results |> Seq.map fst |> collectResults,
            ExprArrayInit (node, getType [] t, results |> List.map snd)
        | ArrayCreationExpressionSyntax(_, _, InitializerExpressionSyntax(es)) 
        | ImplicitArrayCreationExpressionSyntax(_,_,_,InitializerExpressionSyntax(es))
        | InitializerExpressionSyntax(es) ->
            let results = es |> List.map descend

            results |> Seq.map fst |> collectResults,
            ExprArray(node, results |> List.map snd)
        
        | PredefinedTypeSyntax (SyntaxToken tok)
        | ThisExpressionSyntax (SyntaxToken tok) -> ConvertResults.Empty, mkExprVal node tok
        | CastExpressionSyntax(_,t,_,e) -> let res, e = descend e in res,  ExprTypeConversion (node, getType [] t, e)
        | TypeOfExpressionSyntax (_,_,t,_) -> ConvertResults.Empty, ExprWithGeneric(node, [getType [] t], mkExprVal node "typeof")

        | SwitchStatementSyntax(_,_, e, _, _, cases, _) ->
            let matches = 
                cases |> List.collect (fun (SwitchSectionSyntax(labels, stmts) as switchNode) -> 
                    labels |> List.map (function 
                        | :? CaseSwitchLabelSyntax as l -> l :> SyntaxNode, l.Value.ToString().Trim()
                        | :? DefaultSwitchLabelSyntax as l -> l :> SyntaxNode, "_"
                        | :? CasePatternSwitchLabelSyntax as l -> l :> SyntaxNode, l.Pattern.ToString()
                        | _ as l ->  l :> SyntaxNode, Mk.mkError node |> sprintf "%A")
                    |> List.map (fun (l, x) -> 
                        let results, expr = stmts |> List.map descend |> sequenceTree node
                        results,
                        (switchNode :> SyntaxNode, x |> mkPatBind l, None, expr))
                )
            let res, e = descend e

            matches |> Seq.map fst |> collectResults |> combineResults res,            
            ExprMatch (node, e, matches |> List.map snd)

        // not supported syntax
        | BreakStatementSyntax _ -> ErrorType.BreakNotSupported |> createError node |> fromError, Mk.mkError node
        | ContinueStatementSyntax _ -> ErrorType.ContinueNotSupported |> createError node |> fromError, Mk.mkError node
        | GotoStatementSyntax _ -> ErrorType.GotoNotSupported |> createError node |> fromError, Mk.mkError node
        
        | _ -> unknownNode node
            //raise (misssingCaseExpr node |> ErrorMsg.Error |> MissingCase)

    try
    if tryImplicitConv then
        implicitConv node |> Option.map (fun t ->
            let res, desc = descendNoImplicit node
            res, ExprTypeConversion (node, t, desc)) 
        |> Option.defaultWith (fun () -> exprF node)
    else exprF node
    with 
    | MissingCase msg -> eprintfn "%s" msg; reraise()
    | e -> 
        failwith (exceptionExpr e node)

let convert (csTree: SyntaxTree) =
    let (@@) x y = System.IO.Path.Combine(x,y)
    //let mscorlibPath = (System.AppContext.GetData("FX_DEPS_FILE") |> string |> System.IO.DirectoryInfo).Parent.FullName @@ "mscorlib.dll"
    //let mscorlib = MetadataReference.CreateFromFile(mscorlibPath)
    let compilation = CSharpCompilation.Create("MyCompilation", syntaxTrees = [| csTree |], references = [| |])
    let model = compilation.GetSemanticModel(csTree, true)
    csTree.GetRoot() |> convertNode true model

let convertText (csharp:string) =
    let tree = CSharpSyntaxTree.ParseText(csharp)
    let results, expr = tree |> convert
#if DEBUG
    printfn "Results %A" results
#endif
    let expr = expr |> Program
    // expr |> (printfn "%A")
    // printfn "==========="
    let resultErrorsMap = results.Errors |> Seq.groupBy (fun e -> e.ProblematicNode) |> dict
    let errorPrinter node =
        resultErrorsMap |> Dict.tryFind node |> Option.map (fun xs -> 
            match xs |> Seq.map (fun x -> x.Type) |> Seq.toList with
            | [x] -> sprintf "%A" x
            | xs -> sprintf "%A" xs)
        |> Option.defaultValue ""
    
    let blockExpr = expr |> cs2fs.FSharpOutput.toFs (fun node -> sprintf "%A %A %A" (resultErrorsMap.[node] |> Seq.head |> fun x -> x.Type) (node.GetType().Name) (resultErrorsMap.[node] |> Seq.head |> fun x -> x.ProblematicNode))
    let output = blockExpr |> cs2fs.FSharpOutput.printBlock

    output
