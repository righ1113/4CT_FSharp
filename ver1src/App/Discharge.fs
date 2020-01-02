namespace Discharge

open LibraryFS
open LibraryCS2

module Di =

  // main routine
  let discharge =
    printfn "start Dischage.fs"

    LibDischarge.Hoge (1, 2, 3)

    true



