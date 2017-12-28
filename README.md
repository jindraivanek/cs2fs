# Cs2Fs
This project is in experimental stage.

This project aim to be tool that *helps* with rewrite C# code to F#.

## Requirements

[DotNet Core 2.0](https://www.microsoft.com/net/download)

## Usage

From project main directory:

`dotnet run -p cs2fs input.cs [output.fs]`

## Known limitation
What is not supported, and it's not planned at this stage:

* early `return`s, `break`, `continue`.
* non-explicit interface implementation.

What *cannot* be supported due to limitations of F#:

* `protected` keyword.

## TODO

* [ ] comments
* [ ] explicit interfaces implementation

* [ ] use Argu
* [ ] better error handling
* [ ] tests
