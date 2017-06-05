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

and Match = Pat * Expr option * Expr

type Program = Program of Expr

let rec simplify =
    function
    | ExprSequence es -> 
        es |> List.collect (function | ExprSequence es2 -> es2 | e -> [e])
        |> List.map simplify
        |> ExprSequence
    | e -> e

module Transforms =
    let globalNamespace program =
        match program with
        | ExprSequence (e::es) ->
            match e with
            | ExprNamespace _
            | ExprModule _ -> ExprSequence (e::es)
            | _ -> ExprNamespace (NamespaceId "global", program)
        | p -> p