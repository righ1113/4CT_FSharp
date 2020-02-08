namespace LibraryFS

open System
open System.IO
open FSharp.Data

module LibFS =
  type TpConfmat = JsonProvider<"[[[1]]]">
  type TpDiConfs = JsonProvider<"""[{"a":[0], "b":[0], "c":[8], "d":[6]}]""">
  type TpPosout  = {number: int array; nolines: int array; value: int array; pos: int array array; plow: int array array; pupp: int array array; xx: int array}
  type TpDiRules = JsonProvider<"""{"a":[0], "b":[0], "c":[8], "d":[[6]], "e":[[6]], "f":[[6]], "g":[6]}""">

  type TpAxle        = {low: int array array; upp: int array array; lev: int}
  type TpAdjmat      = {adj: int array array}
  type TpReducePack1 = {axle: TpAxle; bLow: int array; bUpp: int array; adjmat: TpAdjmat}
  type TpEdgelist    = {edg: int array array array}
  type TpVertices    = {ver: int array}
  type TpQuestion    = {qa: int array; qb: int array; qc: int array; qd: int array}
  type TpReducePack2 = {edgelist: TpEdgelist; used: bool array; image: TpVertices; redquestions: TpQuestion array}


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
      out <- Array.append out [|{qa = indLine.A; qb = indLine.B; qc = indLine.C; qd = indLine.D}|]
    out

  let readFileRulesD =
    let ind = TpDiRules.Parse <| File.ReadAllText "4ctdata/DiRules07.txt" // VSCode
    //let ind = TpDiRules.Parse <| File.ReadAllText "../../../../4ctdata/DiRules07.txt" // Visual Studio
    {number = ind.A; nolines = ind.B; value = ind.C; pos = ind.D; plow = ind.E; pupp = ind.F; xx = ind.G}

  let readFileTacticsD =
    File.ReadAllLines "4ctdata/DiTactics07.txt" // VSCode
    //File.ReadAllText "../../../../4ctdata/DiTactics07.txt" // Visual Studio
    |> Array.map ((fun str -> str.Split " ")
                  >> (Array.filter (not << String.IsNullOrEmpty)))



