module cs2fs.AST
open cs2fs.Utils

type NamespaceId = NamespaceId of string
type ModuleId = ModuleId of string
type TypeId = TypeId of string
type GenericId = GenericId of string
type ConstId = ConstId of string
type ValId = ValId of string
type FieldId = FieldId of string
type AttributeId = AttributeId of string

type Modifier =
| Private
| Static
| Mutable
| Override

// type abbrevation, type definition in Decl module
type Typ =
| TypType of TypeId
| TypGeneric of GenericId
| TypWithGeneric of Typ list * Typ
| TypFun of Typ * Typ
| TypTuple of Typ list

// Pattern
type Pat<'TContext> =
    | PatConst of 'TContext * ConstId
    | PatWildcard of 'TContext
    | PatBind of 'TContext * ValId //binding to identificator
    | PatCons of 'TContext * ValId * Pat<'TContext> list
    | PatInfixCons of 'TContext * Pat<'TContext> * ValId * Pat<'TContext>
    | PatTuple of 'TContext * Pat<'TContext> list
    | PatList of 'TContext * Pat<'TContext> list
    | PatRecord of 'TContext * (FieldId * Pat<'TContext>) list
    | PatWithType of 'TContext * Typ * Pat<'TContext>
    | PatBindAs of 'TContext * ValId * Pat<'TContext>
    member x.Context =
        match x with
        | PatConst (ctx, _)
        | PatWildcard ctx
        | PatBind (ctx, _)
        | PatCons (ctx, _, _)
        | PatInfixCons (ctx, _, _, _)
        | PatTuple  (ctx, _)
        | PatList  (ctx, _)
        | PatRecord  (ctx, _)
        | PatWithType  (ctx, _, _)
        | PatBindAs  (ctx, _, _) -> ctx

type TypeDecl<'TContext> = 
    | TypeDeclRecord of 'TContext * (FieldId * TypeDecl<'TContext>) list
    | TypeDeclUnion of 'TContext * (ValId * TypeDecl<'TContext> option) list
    | TypeDeclTuple of 'TContext * TypeDecl<'TContext> list
    /// 'type ... Type<..>(...) ='
    | TypeDeclClass of ctx:'TContext *  typeModifiers:Modifier list * genericArgs:Typ list * parameters:Pat<'TContext> * members:Expr<'TContext> list
    | TypeDeclId of 'TContext * TypeId
    member x.Context =
        match x with
        | TypeDeclRecord (ctx, _)
        | TypeDeclUnion (ctx, _)
        | TypeDeclTuple (ctx, _)
        | TypeDeclClass(ctx, _, _, _, _)
        | TypeDeclId (ctx, _) -> ctx

/// An F# expression
/// 'TContext is context specific information like the source range in the C# code and similar information.
and Expr<'TContext> =
    /// Marker for places we couldn't translate
    | ExprError of 'TContext
    | ExprConst of 'TContext * ConstId
    | ExprVal of 'TContext * ValId
    | ExprApp of 'TContext * Expr<'TContext> * Expr<'TContext> //application
    | ExprInfixApp of 'TContext * Expr<'TContext> * ValId * Expr<'TContext>
    | ExprDotApp of 'TContext * Expr<'TContext> * Expr<'TContext>
    | ExprItemApp of 'TContext * Expr<'TContext> * Expr<'TContext> // e1.[e2]
    | ExprTuple of 'TContext * Expr<'TContext> list
    | ExprList of 'TContext * Expr<'TContext> list
    | ExprArray of 'TContext * Expr<'TContext> list
    | ExprRecord of 'TContext * Expr<'TContext> option * (FieldId * Expr<'TContext>) list // recordToCopy, fields
    | ExprSequence of 'TContext * Expr<'TContext> list // command1; commmand2; Expr
    | ExprBind of 'TContext * Modifier list * Pat<'TContext> list * Expr<'TContext> // let x = expr1
    | ExprUseBind of 'TContext * Pat<'TContext> list * Expr<'TContext>
    | ExprRecBind of 'TContext * (Pat<'TContext> list * Expr<'TContext>) list
    | ExprMatch of 'TContext * Expr<'TContext> * Match<'TContext> list
    | ExprMatchLambda of 'TContext * Match<'TContext> list
    | ExprLambda of 'TContext * Pat<'TContext> list * Expr<'TContext>
    | ExprWithType of 'TContext *  Typ * Expr<'TContext>
    | ExprModule of 'TContext * ModuleId * Expr<'TContext>
    | ExprNamespace of 'TContext * NamespaceId * Expr<'TContext>
    | ExprType of 'TContext * TypeId * TypeDecl<'TContext>
    | ExprNew of 'TContext * Typ * Expr<'TContext>
    | ExprDefaultOf of 'TContext * Typ
    /// open 'moduleId'
    | ExprInclude of 'TContext * ModuleId
    | ExprIf of 'TContext * Expr<'TContext> * Expr<'TContext> * Expr<'TContext> option
    | ExprFor of 'TContext * Pat<'TContext> * Expr<'TContext> * Expr<'TContext>
    | ExprWhile of 'TContext * cond: Expr<'TContext> * body: Expr<'TContext>
    | ExprDo of 'TContext * Expr<'TContext> // do block
    | ExprWithGeneric of 'TContext * Typ list * Expr<'TContext>
    | ExprTry of 'TContext * Expr<'TContext> * Match<'TContext> list * Expr<'TContext> option // try body, with matches, finally body

    | ExprMember of 'TContext * ValId * Typ list * Modifier list * ValId option * Pat<'TContext> * Expr<'TContext>
    | ExprMemberConstructor of 'TContext * Modifier list * Pat<'TContext> * Expr<'TContext>
    | ExprMemberProperty of 'TContext * Modifier list * Pat<'TContext> * Expr<'TContext> * Expr<'TContext> option
    | ExprMemberPropertyWithSet of 'TContext * Modifier list * Pat<'TContext> * Expr<'TContext> * Expr<'TContext> option * Expr<'TContext> option
    | ExprInterfaceImpl of 'TContext * Typ * Expr<'TContext>
    | ExprInherit of 'TContext * Typ

    | ExprAttribute of 'TContext * AttributeId list * Expr<'TContext>

    | ExprTypeConversion of 'TContext * Typ * Expr<'TContext>
    | ExprArrayInit of 'TContext * Typ * Expr<'TContext> list // array type, array sizes
    | ExprReturn of 'TContext * Expr<'TContext>
    member x.Context =
        match x with
        | ExprConst (ctx, _)
        | ExprVal (ctx, _)
        | ExprApp (ctx, _, _)
        | ExprInfixApp (ctx, _, _, _)
        | ExprDotApp  (ctx, _, _)
        | ExprItemApp  (ctx, _, _)
        | ExprTuple (ctx, _)
        | ExprList (ctx, _)
        | ExprArray (ctx, _)
        | ExprRecord(ctx, _, _)
        | ExprSequence (ctx, _)
        | ExprBind(ctx, _, _, _)
        | ExprUseBind  (ctx, _, _)
        | ExprRecBind  (ctx, _)
        | ExprMatch (ctx, _, _)
        | ExprMatchLambda (ctx, _)
        | ExprLambda (ctx, _, _)
        | ExprWithType (ctx, _, _)
        | ExprModule (ctx, _, _)
        | ExprNamespace (ctx, _, _)
        | ExprType (ctx, _, _)
        | ExprNew  (ctx, _, _)
        | ExprDefaultOf (ctx, _)
        /// open 'moduleId'
        | ExprInclude (ctx, _)
        | ExprIf (ctx, _, _, _)
        | ExprFor (ctx, _, _, _)
        | ExprWhile (ctx, _, _)
        | ExprDo (ctx, _)
        | ExprWithGeneric (ctx, _, _)
        | ExprTry (ctx, _, _, _)

        | ExprMember (ctx, _, _, _, _, _, _)
        | ExprMemberConstructor(ctx, _, _, _)
        | ExprMemberProperty(ctx, _, _, _, _)
        | ExprMemberPropertyWithSet (ctx, _, _, _, _, _)
        | ExprInterfaceImpl (ctx, _, _)
        | ExprInherit(ctx, _)

        | ExprAttribute (ctx, _, _)

        | ExprTypeConversion  (ctx, _, _)
        | ExprArrayInit (ctx, _, _)
        | ExprReturn(ctx, _) -> ctx

and Match<'TContext> = 'TContext * Pat<'TContext> * Expr<'TContext> option * Expr<'TContext>

type Program<'TContext> =
    | Program of Expr<'TContext>
    member x.Expr =
        match x with
        | Program exp -> exp  
    member x.Context = x.Expr.Context
type ASTmapF<'TContext> = {
    ExprF : Expr<'TContext> -> Expr<'TContext> option
    TypF : Typ -> Typ option
    PatF : Pat<'TContext> -> Pat<'TContext> option
    TypeDeclF : TypeDecl<'TContext> -> TypeDecl<'TContext> option
    RecurseIntoChanged: bool
} with
    static member Default : ASTmapF<'TContext> = {
        ExprF = fun _ -> None
        TypF = fun _ -> None
        PatF = fun _ -> None
        TypeDeclF = fun _ -> None
        RecurseIntoChanged = true
    }

let constIsString (ConstId c) = String.startsWith "\"" c && String.endsWith "\"" c

let rec exprIsValue =
    function
    | ExprApp _
    | ExprConst _
    | ExprDotApp _
    | ExprIf(_,_,_,Some _)
    | ExprInfixApp _
    | ExprList _
    | ExprArray _
    | ExprMatch _
    | ExprMatchLambda _
    | ExprNew _
    | ExprDefaultOf _
    | ExprRecord _
    | ExprTuple _
    | ExprVal _ -> true
    | ExprTry(_,e,_,_)
    | ExprWithType(_,_,e)
    | ExprTypeConversion(_,_,e) -> exprIsValue e
    | ExprSequence (_,es) -> es |> List.last |> exprIsValue
    | _ -> false

let applyAstF recurse f recF n = f n |> Option.map (if recurse then recF else id) |> Option.defaultWith (fun () -> recF n) 

module rec Transforms =
    let recFuncs astF = 
        let apply f recF n = applyAstF astF.RecurseIntoChanged f recF n
        let eF n = n |> apply astF.ExprF (transformExpr astF)
        let tF n = n |> apply astF.TypF (transformTyp astF)
        let pF n = n |> apply astF.PatF (transformPat astF)
        let dF n = n |> apply astF.TypeDeclF (transformTypeDecl astF)
        eF, tF, pF, dF
    let transformExpr astF e =
        let (eF, tF, pF, dF) = recFuncs astF
        match e with
        | ExprError (ctx) -> ExprError (ctx)
        | ExprApp(ctx, e1, e2) -> ExprApp(ctx, eF e1, eF e2)
        | ExprInfixApp(ctx, e1, op, e2) -> ExprInfixApp(ctx, eF e1, op, eF e2)
        | ExprDotApp(ctx, e1, e2) -> ExprDotApp(ctx, eF e1, eF e2)
        | ExprItemApp(ctx, e1, e2) -> ExprItemApp(ctx, eF e1, eF e2)
        | ExprConst (ctx, c) -> ExprConst (ctx, c)
        | ExprVal (ctx, v) -> ExprVal (ctx, v)
        | ExprInclude (ctx, m) -> ExprInclude (ctx, m)
        | ExprTuple (ctx, es) -> ExprTuple(ctx, es |> List.map eF)
        | ExprList (ctx, es) -> ExprList(ctx, es |> List.map eF)
        | ExprArray (ctx, es) -> ExprArray(ctx, es |> List.map eF)
        | ExprRecord (ctx, me, fields) -> (ctx, (Option.map eF me), (fields |> List.map (fun (f, e) -> f, eF e))) |> ExprRecord
        | ExprSequence (ctx, es) -> ExprSequence(ctx, es |> List.map eF) 
        | ExprBind (ctx, m, p, e) -> (ctx, m, List.map pF p, eF e) |> ExprBind
        | ExprUseBind (ctx, p, e) -> (ctx, List.map pF p, eF e) |> ExprUseBind
        | ExprRecBind (ctx, xs) -> (ctx, xs |> List.map (fun (p, e) -> p, eF e)) |> ExprRecBind
        | ExprMatch (ctx, e, m) -> (ctx, eF e, (m |> List.map (fun (c, p, eo, e) -> c, pF p, Option.map eF eo, eF e))) |> ExprMatch
        | ExprMatchLambda (ctx, m) -> ExprMatchLambda (ctx, m |> List.map (fun (c, p, eo, e) -> c, pF p, Option.map eF eo, eF e))
        | ExprLambda (ctx, ps, e) -> ExprLambda (ctx, List.map pF ps, eF e)
        | ExprWithType (ctx, t, e) -> ExprWithType (ctx, tF t, eF e)
        | ExprNamespace (ctx, m, e) -> ExprNamespace (ctx, m, eF e)
        | ExprModule (ctx, m, e) -> ExprModule (ctx, m, eF e)
        | ExprType (ctx, t, d) -> ExprType (ctx, t, dF d)
        | ExprNew (ctx, t, e) -> ExprNew (ctx, tF t, eF e)
        | ExprDefaultOf (ctx, t) -> ExprDefaultOf (ctx, tF t)
        | ExprIf (ctx, e1,e2,eo) -> ExprIf(ctx, eF e1, eF e2, Option.map eF eo)
        | ExprFor (ctx, p,e1,e2) -> ExprFor(ctx, pF p, eF e1, eF e2)
        | ExprWhile (ctx, e1,e2) -> ExprWhile(ctx, eF e1, eF e2)
        | ExprDo (ctx, e) -> ExprDo (ctx, eF e)
        | ExprAttribute (ctx, a,e) -> ExprAttribute (ctx, a, eF e)
        | ExprMember (ctx, v, gs, ms, vo, p, e) -> ExprMember(ctx, v, gs, ms, vo, pF p, eF e)
        | ExprMemberConstructor (ctx, ms, p, e) -> ExprMemberConstructor(ctx, ms, pF p, eF e)
        | ExprMemberProperty (ctx, ms, p, e, eo) -> ExprMemberProperty (ctx, ms, pF p, eF e, Option.map eF eo)
        | ExprMemberPropertyWithSet (ctx, ms, p, e, eo, eo2) -> ExprMemberPropertyWithSet (ctx, ms, pF p, eF e, Option.map eF eo, Option.map eF eo2)
        | ExprInterfaceImpl (ctx, t,e) -> ExprInterfaceImpl (ctx, tF t, eF e)
        | ExprInherit (ctx, t) -> ExprInherit (ctx, tF t)
        | ExprWithGeneric (ctx, g,e) -> ExprWithGeneric (ctx, List.map tF g, eF e)
        | ExprTry (ctx, e, m, ef) -> ExprTry (ctx, eF e, (m |> List.map (fun (c, p, eo, e) -> c, pF p, Option.map eF eo, eF e)), Option.map eF ef)

        | ExprTypeConversion(ctx, t,e) -> ExprTypeConversion(ctx, tF t, eF e)
        | ExprArrayInit(ctx, t,rs) -> ExprArrayInit(ctx, tF t, List.map eF rs)
        | ExprReturn (ctx, e) -> ExprReturn (ctx, eF e)

    let transformPat astF n = 
        let (eF, tF, pF, dF) = recFuncs astF
        match n with
        | PatConst (ctx, c) -> PatConst (ctx, c)
        | PatWildcard ctx -> PatWildcard ctx
        | PatBind (ctx, v) -> PatBind (ctx, v)
        | PatCons (ctx, v, ps) -> PatCons (ctx, v, List.map pF ps)
        | PatInfixCons (ctx, p1, v, p2) -> PatInfixCons (ctx, pF p1, v, pF p2)
        | PatTuple (ctx, ps) -> PatTuple (ctx, List.map pF ps)
        | PatList (ctx, ps) -> PatList (ctx, List.map pF ps)
        | PatRecord (ctx, xs) -> (ctx, xs |> List.map (fun (fId, p) -> fId, pF p)) |> PatRecord
        | PatWithType (ctx, t, p) -> PatWithType (ctx, tF t, pF p)
        | PatBindAs (ctx, v, p) -> PatBindAs (ctx, v, pF p)
                
    let transformTyp astF n = 
        let (eF, tF, pF, dF) = recFuncs astF
        match n with
        | TypType t -> TypType t
        | TypGeneric g -> TypGeneric g
        | TypWithGeneric (g, t) -> TypWithGeneric (g |> List.map tF, tF t)
        | TypFun (t1, t2) -> TypFun (tF t1, tF t2)
        | TypTuple xs -> xs |> List.map tF |> TypTuple
    
    let transformTypeDecl astF n = 
        let (eF, tF, pF, dF) = recFuncs astF
        match n with
        | TypeDeclRecord (ctx, xs) -> (ctx, xs |> List.map (fun (fId, t) -> fId, dF t)) |> TypeDeclRecord
        | TypeDeclUnion (ctx, xs) -> (ctx, xs |> List.map (fun (fId, t) -> fId, Option.map dF t)) |> TypeDeclUnion
        | TypeDeclTuple (ctx, xs) -> (ctx, xs |> List.map dF) |> TypeDeclTuple
        | TypeDeclClass (ctx, mods, generics, p, membs) -> (ctx, mods, generics, pF p, (membs |> List.map eF)) |> TypeDeclClass 
        | TypeDeclId (ctx, t) -> TypeDeclId (ctx, t)
        
    let exprMap f =
        { ASTmapF.Default with
            ExprF = f
        } |> transformExpr 
        
    let typMap f =
        { ASTmapF.Default with
            TypF = f
        } |> transformExpr

    let exprMapOnce f =
        { ASTmapF.Default with
            ExprF = f
            RecurseIntoChanged = false
        } |> transformExpr
    let globalNamespace =
        function
        | ExprSequence (ctx, e::es) as program ->
            match e with
            | ExprNamespace _
            | ExprModule _ -> program
            | _ -> ExprNamespace (ctx, NamespaceId "global", program)
        | e -> e
    
    let rec simplify e =
        let f =
            function
            | ExprSequence (ctx : 'a, [e]) -> Some e
            | ExprSequence (ctx, es) -> 
                let r = 
                    es
                    |> List.collect (function | ExprSequence (ctx, es2) -> es2 | e -> [e])
                    |> List.map simplify
                ExprSequence(ctx, r)
                |> Some
            | _ -> None
        exprMap f e

    let assignmentAsExpr e =
        let f =
            function
            | ExprInfixApp(ctx1, (ExprInfixApp(ctx2, e1, ValId "<-", e2) as assignment), op, e3) -> 
                Some <| ExprSequence (ctx1, [assignment; ExprInfixApp(ctx2, e1, op, e3)])
            | _ -> None
        exprMap f e

    let binaryOpWithString e =
        let f =
            function
            | ExprInfixApp(ctx1, ExprConst (ctxC, c), op, ExprTypeConversion(ctx2, TypType (TypeId "obj"), e)) when constIsString c -> 
                Some <| ExprInfixApp(ctx1, ExprConst (ctxC, c), op, ExprTypeConversion(ctx2, TypType (TypeId "string"), e))
            | _ -> None
        exprMap f e

    let entryPoint e =
        let isMainMember =
            function
            | ExprMember (ctx1, ValId "Main", [], [Static], None, PatTuple (ctx2, [PatWithType(ctx3, TypType (TypeId t), PatBind (ctx4, ValId args))]), _) 
                when t = "string[]" || t = "String[]" -> 
                    Some (ctx1, ctx3, Some (ExprVal (ctx3, ValId args)))
            | ExprMember (ctx1, ValId "Main", [], [Static], None, PatTuple (ctx2, []), _) -> Some (ctx1, ctx2, None)
            | _ -> None
        let f =
            function
            | (ExprType (ctx1, TypeId mainClass, TypeDeclClass (ctx2, _, _, _, members))) as e ->
                members |> Seq.choose isMainMember |> Seq.tryHead |> Option.map (fun (mainCtx, ctx, callArgs) -> 
                    let callArgsVal = function
                        | ExprVal (ctx3, ValId x) -> ctx, ValId x
                        | _ -> ctx, ValId "args"
                    let callArgsPat = callArgs |> Option.map (callArgsVal >> PatBind) |> Option.toList
                    let mainCall = ExprApp (mainCtx, ExprDotApp (mainCtx, ExprVal (ctx1, ValId mainClass), ExprVal (mainCtx, ValId "Main")), ExprTuple(ctx, callArgs |> Option.toList))
                    let mainBind = ExprAttribute(mainCtx, [AttributeId "EntryPoint"], ExprBind (mainCtx, [], [PatCons (mainCtx, ValId "main", callArgsPat)], ExprSequence (mainCtx, [mainCall; ExprConst (mainCtx, ConstId "0")])))
                    Some <| ExprSequence (mainCtx, [e; ExprModule (mainCtx, ModuleId (mainClass + "__run"), mainBind)])
                ) |> Option.defaultValue None
            | _ -> None
        exprMapOnce f e
        
    let unitAfterSequenceWithoutValue e =
        let f =
            function
            | ExprMember (ctx, v,t,m,v2,p,e) -> 
                let e' = if not(exprIsValue e) then ExprSequence (ctx, [e; ExprVal (ctx, ValId "()")]) else e
                Some <| ExprMember (ctx, v,t,m,v2,p,e')
            | _ -> None
        exprMapOnce f e

    let lastReturn e =
        let replaceLastExpr =
            function
            | ExprSequence (ctx, (es:Expr<'a> list)) ->
                match List.tryLast es with
                | Some (ExprReturn(ctx2, e)) ->
                    let (take: Expr<'a> list -> Expr<'a> list) = List.take ((List.length es) - 1)
                    let (exps:Expr<'a> list) = take es @ [e]
                    Some <| ExprSequence(ctx, exps)
                | _ -> None
            | ExprReturn (ctx, e) -> Some e
            | _ -> None
        let f =            
            function
            | ExprMember _
            | ExprMemberProperty _
            | ExprMemberPropertyWithSet _
            | ExprLambda _ as e -> (exprMapOnce replaceLastExpr) e |> Some
            | _ -> None
        exprMap f e

    let removeUnnecessaryTypeConversion e =
        let f =
            function
            | ExprBind (ctx, modifiers, [PatWithType(_, t,_) as p], ExprTypeConversion(_, t2, e)) when t=t2 ->
                ExprBind (ctx, modifiers, [p], e) |> Some
            | _ -> None
        exprMap f e
    
    let typeReplacement e =
        let isOneOf xs x = xs |> Seq.exists ((=)x)
        let tupleIfMulti = function | [t] -> t | ts -> TypTuple ts
        let f =
            function
            | TypWithGeneric(gs, TypType (TypeId t)) when t |> isOneOf ["System.Func"; "Func"] -> 
                let (t::tup) = gs |> List.rev
                let inputTypes = tupleIfMulti (List.rev tup)
                TypFun (inputTypes, t) |> Some
            | TypType (TypeId t) when t |> isOneOf ["System.Action"; "Action"] -> 
                TypFun (tupleIfMulti [], TypType (TypeId "unit")) |> Some
            | TypWithGeneric(gs, TypType (TypeId t)) when t |> isOneOf ["System.Action"; "Action"] -> 
                TypFun (tupleIfMulti gs, TypType (TypeId "unit")) |> Some
            | TypTuple [] -> TypType (TypeId "unit") |> Some
            | TypType (TypeId "System.String") -> TypType (TypeId "string") |> Some
            | TypType (TypeId "System.Int32") -> TypType (TypeId "int") |> Some
            | TypType (TypeId "System.Double") -> TypType (TypeId "float") |> Some
            | _ -> None
        typMap f e

    let constReplacement e =
        let f =
            function
            | ExprConst (ctx, ConstId "null") -> 
                ExprConst (ctx, ConstId "Unchecked.defaultof<_>") |> Some
            | ExprInfixApp (ctx, e1, ValId "as" , e2) -> ExprInfixApp (ctx, e1, ValId ":?>" , e2) |> Some
            | ExprInfixApp (ctx, e1, ValId "is" , e2) -> ExprInfixApp (ctx, e1, ValId ":?" , e2) |> Some
            | _ -> None
        exprMap f e

module Mk =
    open cs2fs.FSharpDefs
    let mkValId id =
        let id = if Set.contains id fsharpKeywords then "``" + id + "``" else id
        ValId id
    let mkExprVal ctx n = ExprVal(ctx, mkValId n)
    let mkPatBind ctx n = PatBind(ctx, mkValId n)

    let mkError ctx = ExprError(ctx)