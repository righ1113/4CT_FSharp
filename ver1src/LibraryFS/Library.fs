namespace LibraryFS

open System
open System.IO
open FSharp.Data

module LibFS =
  type TpConfmat = JsonProvider<"[[[1]]]">
  type TpDiConfs = JsonProvider<"""[{"a":[0], "b":[0], "c":[8], "d":[6]}]""">
  type TpDiRules = JsonProvider<"[[[1]]]">

  let readFileGoodConfsR =
    File.ReadAllText "4ctdata/goodConfs.txt" // VSCode
    //File.ReadAllText "../../../../4ctdata/goodConfs.txt" // Visual Studio
    |> TpConfmat.Parse

    //printfn "%d" hoge2.[0].[0].[1]
    //let hoge = str.Split ' '
    //printfn "%s" hoge.[0]
    //"ok"

//    |> String.
//    |> TpConfmat.Parse
//    |> List.map Tail

  let readFileGoodConfsD =
    let mutable out = [||] 
    let ind = TpDiConfs.Parse <| File.ReadAllText "4ctdata/DiGoodConfs.txt" // VSCode
    //let ind = TpDiConfs.Parse <| File.ReadAllText "../../../../4ctdata/DiGoodConfs.txt" // Visual Studio
    for indLine in ind do
      out <- Array.append out [|(indLine.A, indLine.B, indLine.C, indLine.D)|]
    out

  let readFileRulesD =
    File.ReadAllText "4ctdata/DiRules07.txt" // VSCode
    //File.ReadAllText "../../../../4ctdata/DiRules07.txt" // Visual Studio
    |> TpDiRules.Parse

  let readFileTacticsD =
    File.ReadAllLines "4ctdata/DiTactics07.txt" // VSCode
    //File.ReadAllText "../../../../4ctdata/DiTactics07.txt" // Visual Studio
    |> Array.map ((fun str -> str.Split " ")
                  >> (Array.filter (not << String.IsNullOrEmpty)))



