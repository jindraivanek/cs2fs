module cs2fs

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp
open Fantomas
open Microsoft.FSharp.Compiler

let pick f xs =
    let rec pick' f xs acc =
        match xs with
        | [] -> None
        | x::tail -> if f x then Some (x, (List.rev acc @ tail)) else pick' f tail (x::acc)
    pick' f xs []

let concat s2 (s1,l1) = s1 + s2, l1 

let newline = System.Environment.NewLine

let surround head tail body = head + body + tail

let delim sep xs = xs |> String.concat sep

let rec convertNode debug (tabs: int) (node: SyntaxNode) =
    let descend n = convertNode debug tabs n
    let descendInd n = convertNode debug (tabs+1) n
    let print' indent nl s postfix = 
        let spaces = ([1..tabs] |> Seq.map (fun _ -> "    ") |> String.concat "")
        (sprintf "%s%s%s"
            (if nl then newline+spaces else "") 
            (if debug then "(" + node.GetType().Name + ")" else "") 
            s) 
        + postfix
        + if debug then "§" else ""
    let print = print' 0 false
    let printnl = print' 0 true

    match node with
    | ClassDeclarationSyntax(attrs,keyword,ident,typePars,bases,constrs,_,members,_,_) -> 
        printnl <| "type " + ident.Text + "() =" <| (members |> Seq.map descendInd |> delim newline)
    | MethodDeclarationSyntax(arity,attrs,returnType,interfaceS,ident,typePars,pars,typeParsConstrs,block,arrowExpr,_) -> 
        printnl <| "member this." + ident.Text + (descend pars) + (descend block) <| ""
    // | :? ParameterListSyntax as x -> printJoin ", " <| "(" <| ")"
    // | :? ParameterSyntax as x -> print <| x.Identifier.Text <| ""
    // | :? PredefinedTypeSyntax as x -> print <| " : " + x.Keyword.Text <| ""
    // | :? BlockSyntax as x -> print <| " =" <| ""
    // | :? ReturnStatementSyntax as x -> printnl "" ""
    // | :? BinaryExpressionSyntax as x -> printJoin (x.OperatorToken.Text) "" ""
    // | :? IdentifierNameSyntax as x -> print (if x.Parent :? VariableDeclarationSyntax then "" else x.Identifier.Text) ""
    // | :? LiteralExpressionSyntax as x -> print (x.Token.Text) ""
    // | :? LocalDeclarationStatementSyntax as x -> printnl "let " ""
    // | :? VariableDeclarationSyntax as x -> print "" ""
    // | :? VariableDeclaratorSyntax as x -> print (x.Identifier.Text) ""
    // | :? EqualsValueClauseSyntax as x -> print " = " ""
    | _ -> printnl <| "[!" + node.GetType().ToString() + "!]" <| ""

let convert debug (csTree: SyntaxTree) =
    csTree.GetRoot().ChildNodes() |> Seq.map (convertNode debug 0) |> String.concat ""

let input = @"
    public class MyClass
    {
        public void MyMethod(int x, string s)
        {
            var y = x+1;
            int z = y*2;
            return x+y+z;
        }
    }"

[<EntryPoint>]
let main argv =
    printfn "%A" argv
    CSharpSyntaxTree.ParseText(input) |> convert true |> (printfn "%s")
    CSharpSyntaxTree.ParseText(input) |> convert false |> (printfn "%s")
    0 // return an integer exit code
