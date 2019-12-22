// ◆author: righ1113
// ◆動かし方
// 1. $ cd ver0src
// 2. $ code .
// 3. $ cd src/App
// 4. $ dotnet run

open System
open Reduce
//open Library

[<EntryPoint>]
let main argv =
  printfn "これは四色定理を解くプログラムです。"

  printfn "1: reduce 2: dischrge  please select."
  Console.ReadLine()
  |> fun str ->
    match str with
      | "1" -> Re.reduce
      | _   -> true
  |> fun retB ->
    if retB
      then printfn "プログラムは正常終了しました。"
      else printfn "プログラムは途中終了しました。"

  0 // return an integer exit code



