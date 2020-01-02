namespace LibraryFS

open System.IO
open FSharp.Data

module LibFS =
  type TpConfmat = JsonProvider<"[[[1]]]">
  type TpDiConfs = JsonProvider<"""[{"a":[0], "b":[0], "c":[8], "d":[6]}]""">

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
    File.ReadAllText "4ctdata/DiGoodConfs.txt" // VSCode
    //File.ReadAllText "../../../../4ctdata/DiGoodConfs.txt" // Visual Studio
    |> TpDiConfs.Parse



