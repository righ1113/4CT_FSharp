namespace Library

open System.IO
open FSharp.Data

module Lib =
  type TpConfmat = JsonProvider<"[[[1]]]">

  let readFileGoodConfsR =
    File.ReadAllText "4ctdata/goodConfs.txt"
    |> TpConfmat.Parse
    //printfn "%d" hoge2.[0].[0].[1]
    //let hoge = str.Split ' '
    //printfn "%s" hoge.[0]
    //"ok"

//    |> String.
//    |> TpConfmat.Parse
//    |> List.map Tail



