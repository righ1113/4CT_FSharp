namespace Discharge

open LibraryFS
open LibraryCS2

module Di =

  // main routine
  let discharge =
    printfn "start Dischage.fs"

    let graphs = LibFS.readFileGoodConfsD
    printfn "%d" graphs.[5].C.[1]

    let rules = LibFS.readFileRulesD
    printfn "%d" rules.[1].[8].[3]

    let tactics = LibFS.readFileTacticsD
    printfn "%s" tactics.[13].[19]

    LibDischarge.Hoge (1, 2, 3)

    true



