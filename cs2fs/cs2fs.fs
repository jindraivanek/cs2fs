module cs2fs

open Microsoft.CodeAnalysis
open Microsoft.CodeAnalysis.CSharp

let newline = System.Environment.NewLine

let surround head tail body = head + body + tail

let delim sep xs = xs |> String.concat sep

let (|VariableDeclarationSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.VariableDeclarationSyntax as node ->
      Some (node.Type, node.Variables |> Seq.toList)
    | _ -> None
    
let (|ParameterListSyntax|_|) (node:Microsoft.CodeAnalysis.SyntaxNode) =
    match node with
    | :? Microsoft.CodeAnalysis.CSharp.Syntax.ParameterListSyntax as node ->
      Some (node.OpenParenToken, node.Parameters |> Seq.toList, node.CloseParenToken)
    | _ -> None

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
    let print = print' 0 false ""
    let printnl = print' 0 true ""
    let printnlAndThen = print' 0 true

    let printType (n:Syntax.TypeSyntax) =
        let t = n.ToString()
        if n.IsVar then "" else (" : " + t)

    match node with
    | CompilationUnitSyntax(aliases, usings, attrs, members, _) ->
         print (members |> Seq.map descend |> delim "")
    | ClassDeclarationSyntax(attrs,keyword,ident,typePars,bases,constrs,_,members,_,_) ->
        printnlAndThen <| "type " + ident.Text + "() =" <| (members |> Seq.map descendInd |> delim newline)
    | MethodDeclarationSyntax(arity,attrs,returnType,interfaceS,ident,typePars,pars,typeParsConstrs,block,arrowExpr,_) -> 
        printnlAndThen <| "member this." + ident.Text + (descend pars) + " = " <| (descendInd block)
    | ParameterListSyntax(left, prms, right) as x ->
        print <| left.Text + (prms |> Seq.map descend |> delim ", ") + right.Text
    | ParameterSyntax(attrs, typ, ident, _) ->
        print <| ident.Text + printType typ
    | BlockSyntax(_x,stmts,_) -> stmts |> Seq.map (fun x -> printnl (descend x)) |> delim ""
    | ReturnStatementSyntax(_,e,_) -> print (descend e)
    | BinaryExpressionSyntax(e1,op,e2) -> print <| ([descend e1; op.Text; descend e2] |> delim " ")
    | IdentifierNameSyntax(token) -> print token.Text
    | LiteralExpressionSyntax(token) -> print (token.Text)
    | LocalDeclarationStatementSyntax(isConst,varDecl,_) ->
        print <| "let " + descend varDecl
    | VariableDeclarationSyntax(typ, vars) ->
        vars |> Seq.map
            (function
             | VariableDeclaratorSyntax(ident, args, init) -> ident.Text + printType typ + descend init
             | x -> descend x)
        |> delim ", " |> print
    | VariableDeclaratorSyntax(ident, args, init) -> print <| ident.Text + descend init
    | EqualsValueClauseSyntax(eqToken, value) -> print <| " " + eqToken.Text + " " + descend value
    | _ -> printnl <| "[!" + node.GetType().ToString() + "!]"

let convert debug (csTree: SyntaxTree) =
    csTree.GetRoot() |> convertNode debug 0

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
    //CSharpSyntaxTree.ParseText(input) |> convert true |> (printfn "%s")
    CSharpSyntaxTree.ParseText(input) |> convert false |> (printfn "%s")
    0 // return an integer exit code
