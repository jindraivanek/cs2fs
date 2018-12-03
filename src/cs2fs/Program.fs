module cs2fs.Program

open cs2fs.Convert

[<EntryPoint>]
let main argv =
    eprintfn "Converting: %s" argv.[0]
    let output = System.IO.File.ReadAllText argv.[0] |> convertText
    //expr |> (printfn "%A")
    //printfn "==========="
    if argv.Length > 1 then
        System.IO.File.WriteAllText(argv.[1], output) 
    output |> (printfn "%s")
    0 // return an integer exit code
