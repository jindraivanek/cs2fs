module cs2fs.CSharpActivePatternsExtra

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Microsoft.CodeAnalysis.CSharp.Syntax

let (|SyntaxToken|) (tok: Microsoft.CodeAnalysis.SyntaxToken) =
    tok.Text.Trim()

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

let (|TypeParameterListSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.TypeParameterListSyntax as node ->
      Some (node.LessThanToken, node.Parameters |> Seq.toList, node.GreaterThanToken)
    | _ -> None

let (|TypeArgumentListSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.TypeArgumentListSyntax as node ->
      Some (node.LessThanToken, node.Arguments |> Seq.toList, node.GreaterThanToken)
    | _ -> None


let (|ArgumentListSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.ArgumentListSyntax as node ->
      Some (node.OpenParenToken, node.Arguments |> Seq.toList, node.CloseParenToken)
    | _ -> None

let (|BracketedArgumentListSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.BracketedArgumentListSyntax as node ->
      Some (node.Arguments |> Seq.toList)
    | _ -> None

let (|BaseListSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.BaseListSyntax as node ->
      Some (node.Types |> Seq.toList)
    | _ -> None

let (|FieldDeclarationSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.FieldDeclarationSyntax as node ->
      Some (node.AttributeLists |> Seq.toList, node.Declaration, node.Modifiers |> Seq.toList)
    | _ -> None

let (|InitializerExpressionSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.InitializerExpressionSyntax as node ->
      Some (node.Expressions |> Seq.toList)
    | _ -> None

let (|ArrayCreationExpressionSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.ArrayCreationExpressionSyntax as node ->
      Some (node.Type.ElementType, node.Type.RankSpecifiers |> Seq.toList, node.Initializer)
    | _ -> None

let (|ForStatementSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.ForStatementSyntax as node ->
      Some (node.Declaration, node.Initializers |> Seq.toList, node.Condition, node.Incrementors |> Seq.toList, node.Statement)
    | _ -> None
