module cs2fs.AST

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

// type abbrevation, type definition in Decl module
type Typ =
| TypType of TypeId
| TypGeneric of GenericId
| TypWithGeneric of GenericId * Typ
| TypFun of Typ * Typ
| TypTuple of Typ list

// Pattern
type Pat =
| PatConst of ConstId
| PatWildcard
| PatBind of ValId //binding to identificator
| PatCons of ValId * Pat list
| PatInfixCons of Pat * ValId * Pat
| PatTuple of Pat list
| PatList of Pat list
| PatRecord of (FieldId * Pat) list
| PatWithType of Typ * Pat
| PatBindAs of ValId * Pat

type TypeDecl = 
| TypeDeclRecord of (FieldId * TypeDecl) list
| TypeDeclUnion of (ValId * TypeDecl option) list
| TypeDeclTuple of TypeDecl list
| TypeDeclClass of Modifier list * Pat * Expr list
| TypeDeclId of TypeId
| TypeDeclWithGeneric of GenericId list * TypeDecl

and Expr =
| ExprConst of ConstId
| ExprVal of ValId
| ExprApp of Expr * Expr //application
| ExprInfixApp of Expr * ValId * Expr
| ExprDotApp of Expr * Expr
| ExprTuple of Expr list
| ExprList of Expr list
| ExprRecord of Expr option * (FieldId * Expr) list // recordToCopy, fields
| ExprSequence of Expr list // command1; commmand2; Expr
| ExprBind of Modifier list * Pat * Expr // let x = expr1
| ExprUseBind of Pat * Expr
| ExprRecBind of (Pat * Expr) list
| ExprMatch of Expr * Match list
| ExprMatchLambda of Match list
| ExprLambda of Pat list * Expr
| ExprWithType of Typ * Expr
| ExprModule of ModuleId * Expr
| ExprNamespace of NamespaceId * Expr
| ExprType of TypeId * TypeDecl
| ExprNew of TypeId * Expr
| ExprInclude of ModuleId
| ExprIf of Expr * Expr * Expr option
| ExprFor of Pat * Expr * Expr
| ExprWhile of Expr * Expr

| ExprMember of ValId * GenericId list * Modifier list * ValId option * Pat * Expr
| ExprMemberProperty of Pat * Expr * Expr option
| ExprMemberPropertyWithSet of Pat * Expr * Expr option * Expr option

| ExprAttribute of AttributeId list * Expr

| ExprTypeConversion of TypeId * Expr

and Match = Pat * Expr option * Expr

type Program = Program of Expr

type ASTmapF = {
    ExprF : Expr -> Expr option
    TypF : Typ -> Typ option
    PatF : Pat -> Pat option
    TypeDeclF : TypeDecl -> TypeDecl option
    RecurseIntoChanged: bool
} with
    static member Default = {
        ExprF = fun _ -> None
        TypF = fun _ -> None
        PatF = fun _ -> None
        TypeDeclF = fun _ -> None
        RecurseIntoChanged = true
    }

let rec simplify =
    function
    | ExprSequence es -> 
        es |> List.collect (function | ExprSequence es2 -> es2 | e -> [e])
        |> List.map simplify
        |> ExprSequence
    | e -> e

let constIsString (ConstId c) = String.startsWith "\"" c && String.endsWith "\"" c

let applyAstF recurse f recF n = f n |> Option.map (if recurse then recF else id) |> Option.fillWith (fun () -> recF n) 

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
        | ExprApp(e1, e2) -> ExprApp(eF e1, eF e2)
        | ExprInfixApp(e1, op, e2) -> ExprInfixApp(eF e1, op, eF e2)
        | ExprDotApp(e1, e2) -> ExprDotApp(eF e1, eF e2)
        | ExprConst c -> ExprConst c
        | ExprVal v -> ExprVal v
        | ExprInclude m -> ExprInclude m
        | ExprTuple es -> es |> List.map eF |> ExprTuple
        | ExprList es -> es |> List.map eF |> ExprList
        | ExprRecord (me, fields) -> ((Option.map eF me), (fields |> List.map (fun (f, e) -> f, eF e))) |> ExprRecord
        | ExprSequence es -> es |> List.map eF |> ExprSequence
        | ExprBind (m, p, e) -> (m, pF p, eF e) |> ExprBind
        | ExprUseBind (p, e) -> (pF p, eF e) |> ExprUseBind
        | ExprRecBind xs ->  xs |> List.map (fun (p, e) -> p, eF e) |> ExprRecBind
        | ExprMatch (e, m) -> (eF e, (m |> List.map (fun (p, eo, e) -> pF p, Option.map eF eo, eF e))) |> ExprMatch
        | ExprMatchLambda m -> ExprMatchLambda (m |> List.map (fun (p, eo, e) -> pF p, Option.map eF eo, eF e))
        | ExprLambda (ps, e) -> ExprLambda (List.map pF ps, eF e)
        | ExprWithType (t, e) -> ExprWithType (tF t, eF e)
        | ExprNamespace (m, e) -> ExprNamespace (m, eF e)
        | ExprModule (m, e) -> ExprModule (m, eF e)
        | ExprType (t, d) -> ExprType (t, dF d)
        | ExprNew (t, e) -> ExprNew (t, eF e)
        | ExprIf (e1,e2,eo) -> ExprIf(eF e1, eF e2, Option.map eF eo)
        | ExprFor (p,e1,e2) -> ExprFor(pF p, eF e1, eF e2)
        | ExprWhile (e1,e2) -> ExprWhile(eF e1, eF e2)
        | ExprAttribute (a,e) -> ExprAttribute (a, eF e)
        | ExprMember (v, gs, ms, vo, p, e) -> ExprMember(v, gs, ms, vo, pF p, eF e)
        | ExprMemberProperty (p, e, eo) -> ExprMemberProperty (pF p, eF e, Option.map eF eo)
        | ExprMemberPropertyWithSet (p, e, eo, eo2) -> ExprMemberPropertyWithSet (pF p, eF e, Option.map eF eo, Option.map eF eo2)

        | ExprTypeConversion(t,e) -> ExprTypeConversion(t, eF e)

    let transformPat astF n = 
        let (eF, tF, pF, dF) = recFuncs astF
        match n with
        | PatConst c -> PatConst c
        | PatWildcard -> PatWildcard
        | PatBind v -> PatBind v
        | PatCons (v, ps) -> PatCons (v, List.map pF ps)
        | PatInfixCons (p1, v, p2) -> PatInfixCons (pF p1, v, pF p2)
        | PatTuple ps -> PatTuple (List.map pF ps)
        | PatList ps -> PatList (List.map pF ps)
        | PatRecord xs -> xs |> List.map (fun (fId, p) -> fId, pF p) |> PatRecord
        | PatWithType (t, p) -> PatWithType (tF t, pF p)
        | PatBindAs (v, p) -> PatBindAs (v, pF p)
                
    let transformTyp astF n = 
        let (eF, tF, pF, dF) = recFuncs astF
        match n with
        | TypType t -> TypType t
        | TypGeneric g -> TypGeneric g
        | TypWithGeneric (g, t) -> TypWithGeneric (g, tF t)
        | TypFun (t1, t2) -> TypFun (tF t1, tF t2)
        | TypTuple xs -> xs |> List.map tF |> TypTuple
    
    let transformTypeDecl astF n = 
        let (eF, tF, pF, dF) = recFuncs astF
        match n with
        | TypeDeclRecord xs -> xs |> List.map (fun (fId, t) -> fId, dF t) |> TypeDeclRecord
        | TypeDeclUnion xs -> xs |> List.map (fun (fId, t) -> fId, Option.map dF t) |> TypeDeclUnion
        | TypeDeclTuple xs -> xs |> List.map dF |> TypeDeclTuple
        | TypeDeclClass (mods, p, membs) -> (mods, pF p, (membs |> List.map eF)) |> TypeDeclClass 
        | TypeDeclId t -> TypeDeclId t
        | TypeDeclWithGeneric (g,t) -> TypeDeclWithGeneric (g, dF t)
        
    let exprMap f =
        { ASTmapF.Default with
            ExprF = f
        } |> transformExpr

    let exprMapOnce f =
        { ASTmapF.Default with
            ExprF = f
            RecurseIntoChanged = false
        } |> transformExpr
    let globalNamespace =
        function
        | ExprSequence (e::es) as program ->
            match e with
            | ExprNamespace _
            | ExprModule _ -> program
            | _ -> ExprNamespace (NamespaceId "global", program)
        | e -> e

    let assignmentAsExpr =
        function
        | ExprInfixApp(ExprInfixApp(e1, ValId "<-", e2) as assignment, op, e3) -> 
            Some <| ExprSequence [assignment; ExprInfixApp(e1, op, e3)]
        | _ -> None
        |> exprMap

    let binaryOpWithString =
        function
        | ExprInfixApp(ExprConst c, op, ExprTypeConversion(TypeId "obj", e)) when constIsString c -> 
            Some <| ExprInfixApp(ExprConst c, op, ExprTypeConversion(TypeId "string", e))
        | _ -> None
        |> exprMap

    let entryPoint =
        let isMainMember =
            function
            | ExprMember (ValId "Main", [], [Static], None, PatTuple [PatWithType(TypType (TypeId "string[]"), PatBind (ValId _))], _) -> true
            | _ -> false
        function
        | (ExprType (TypeId mainClass, TypeDeclClass (_, _, members))) as e ->
            printfn "EntryPoint"
            members |> List.tryFind isMainMember |> Option.map (fun _ -> 
                printfn "EntryPoint"
                let mainCall = ExprApp (ExprDotApp (ExprVal (ValId mainClass), ExprVal (ValId "Main")), ExprTuple [ExprVal (ValId "args")])
                let mainBind = ExprAttribute([AttributeId "EntryPoint"], ExprBind ([], PatCons (ValId "main", [PatBind (ValId "args")]), ExprSequence [mainCall; ExprConst (ConstId "0")]))
                Some <| ExprSequence [e; ExprModule (ModuleId (mainClass + "__run"), mainBind)]
            ) |> Option.fill None
        | _ -> None
        |> exprMapOnce