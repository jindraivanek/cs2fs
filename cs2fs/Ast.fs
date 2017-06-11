module cs2fs.AST

type NamespaceId = NamespaceId of string
type ModuleId = ModuleId of string
type TypeId = TypeId of string
type GenericId = GenericId of string
type ConstId = ConstId of string
type ValId = ValId of string
type FieldId = FieldId of string

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
| TypeDeclClass of Modifier list * Pat * Member list
| TypeDeclId of TypeId
| TypeDeclWithGeneric of GenericId * TypeDecl

and Member = 
| Member of ValId * Modifier list * ValId option * Pat * Expr
| MemberProperty of Pat * Expr * Expr option
| MemberPropertyWithSet of Pat * Expr * Expr option * Expr option

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

| ExprTypeConversion of TypeId * Expr

and Match = Pat * Expr option * Expr

type Program = Program of Expr

type ASTmapF = {
    ExprF : Expr -> Expr
    TypF : Typ -> Typ
    PatF : Pat -> Pat
    TypeDeclF : TypeDecl -> TypeDecl
    MemberF : Member -> Member
} with
    static member Default = {
        ExprF = id
        TypF = id
        PatF = id
        TypeDeclF = id
        MemberF = id
    }

let rec simplify =
    function
    | ExprSequence es -> 
        es |> List.collect (function | ExprSequence es2 -> es2 | e -> [e])
        |> List.map simplify
        |> ExprSequence
    | e -> e

module rec Transforms =
    let transformF descendF astF n =
        let rec inner n =
            descendF astF (fun g -> inner (g n))
        inner n

    let recFuncs astF = 
        let eF n = n |> astF.ExprF |> transformExpr astF
        let tF n = n |> astF.TypF |> transformTyp astF        
        let pF n = n |> astF.PatF |> transformPat astF
        let dF n = n |> astF.TypeDeclF |> transformTypeDecl astF
        let mF n = n |> astF.MemberF |> transformMember astF
        eF, tF, pF, dF, mF
    let transformExpr astF e =
        let (eF, tF, pF, dF, mF) = recFuncs astF
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

        | ExprTypeConversion(t,e) -> ExprTypeConversion(t, eF e)

    let transformPat astF n = 
        let (eF, tF, pF, dF, mF) = recFuncs astF
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
        let (eF, tF, pF, dF, mF) = recFuncs astF
        match n with
        | TypType t -> TypType t
        | TypGeneric g -> TypGeneric g
        | TypWithGeneric (g, t) -> TypWithGeneric (g, tF t)
        | TypFun (t1, t2) -> TypFun (tF t1, tF t2)
        | TypTuple xs -> xs |> List.map tF |> TypTuple
    
    let transformTypeDecl astF n = 
        let (eF, tF, pF, dF, mF) = recFuncs astF
        match n with
        | TypeDeclRecord xs -> xs |> List.map (fun (fId, t) -> fId, dF t) |> TypeDeclRecord
        | TypeDeclUnion xs -> xs |> List.map (fun (fId, t) -> fId, Option.map dF t) |> TypeDeclUnion
        | TypeDeclTuple xs -> xs |> List.map dF |> TypeDeclTuple
        | TypeDeclClass (mods, p, membs) -> (mods, pF p, (membs |> List.map mF)) |> TypeDeclClass 
        | TypeDeclId t -> TypeDeclId t
        | TypeDeclWithGeneric (g,t) -> TypeDeclWithGeneric (g, dF t)
        
    let transformMember astF n = 
        let (eF, tF, pF, dF, mF) = recFuncs astF
        match n with
        | Member (v, ms, vo, p, e) -> Member(v, ms, vo, pF p, eF e)
        | MemberProperty (p, e, eo) -> MemberProperty (pF p, eF e, Option.map eF eo)
        | MemberPropertyWithSet (p, e, eo, eo2) -> MemberPropertyWithSet (pF p, eF e, Option.map eF eo, Option.map eF eo2)

    let globalNamespace program =
        match program with
        | ExprSequence (e::es) ->
            match e with
            | ExprNamespace _
            | ExprModule _ -> ExprSequence (e::es)
            | _ -> ExprNamespace (NamespaceId "global", program)
        | p -> p

    let assignmentAsExpr =
        { ASTmapF.Default with
            ExprF =
            function
            | ExprInfixApp(ExprInfixApp(e1, ValId "<-", e2) as assignment, op, e3) -> 
                ExprSequence [assignment; ExprInfixApp(e1, op, e3)]
            | e -> e
        } |> transformExpr