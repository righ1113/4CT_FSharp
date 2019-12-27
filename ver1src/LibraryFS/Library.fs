namespace LibraryFS

open System.IO
open FSharp.Data

module LibFS =
  type TpConfmat = JsonProvider<"[[[1]]]">

  let readFileGoodConfsR =
    // Visual Studio‚ÅŽÀs‚µ‚Ä‚­‚¾‚³‚¢
    File.ReadAllText "../../../../4ctdata/goodConfs.txt"
    |> TpConfmat.Parse

    //printfn "%d" hoge2.[0].[0].[1]
    //let hoge = str.Split ' '
    //printfn "%s" hoge.[0]
    //"ok"

//    |> String.
//    |> TpConfmat.Parse
//    |> List.map Tail



