namespace Reduce

open System
open Library

module Re =
  let MVERTS        = 27 // max number of vertices in a free completion + 1
  let DEG           = 13 // max degree of a vertex in a free completion + 1
  // must be at least 13 because of row 0
  let EDGES         = 62 // max number of edges in a free completion + 1
  let MAXRING       = 14 // max ring-size
                   // 3^(i-1)
  let POWER         = [0; 1; 3; 9; 27; 81; 243; 729; 2187; 6561; 19683; 59049; 177147; 531441; 1594323; 4782969; 14348907]
  let SIMATCHNUMBER = [0; 0; 1; 3; 10; 30; 95; 301; 980; 3228; 10797; 36487; 124542; 428506; 1485003]

  exception MyException of string

  // 1. strip()
  let strip graph =
    1

  // 2. findangles()
  let findangles graph edgeno =
    let angle     = List.replicate EDGES (List.replicate 5 0)
    let diffangle = List.replicate EDGES (List.replicate 5 0)
    let sameangle = List.replicate EDGES (List.replicate 5 0)
    let contract  = List.replicate (EDGES + 1) 0
    (angle, diffangle, sameangle, contract)

  // 3. findlive()
  let findlive live0 ncodes angle power extentclaim =
    let nlive1 = ncodes
    (nlive1, live0)

  // 4. updatelive()
  let updatelive ring real0 power live1 nchar ncodes nlive1 =
    (nlive1, live1)

  // 5. checkContract()
  let checkContract live2 nlive2 diffangle sameangle contract power =
    ()

  let reduce =
    try
      printfn "Reduce.fs"

      let graphs = Lib.readFileGoodConfsR
      //printfn "%d" graphs.[1].[1].[0]

      let mutable i = 0
      for graph in Array.take 3 graphs do
        printfn "%d" i
        i <- i + 1

        // 1. strip()
        let edgeno = strip graph

        // 2. findangles()
        (* "findangles" fills in the arrays "angle","diffangle","sameangle" and
            "contract" from the input "graph". "angle" will be used to compute
            which colourings of the ring edges extend to the configuration; the
            others will not be used unless a contract is specified, and if so
            they will be used in "checkcontract" below to verify that the
            contract is correct. *)
        let (angle, diffangle, sameangle, contract) = findangles graph edgeno

        // 3. findlive()
        let ring   = graph.[0+1].[1] // ring-size
        let ncodes = POWER.[ring + 1] / 2 // number of codes of colorings of R
        let live0  = List.replicate ncodes 1
        let real0  = List.replicate (SIMATCHNUMBER.[MAXRING] / 8 + 2) 255
        let nchar  = SIMATCHNUMBER.[ring] / 8 + 1
        let (nlive1, live1) = findlive live0 ncodes angle POWER graph.[0+1].[2]

        // 4. updatelive()
        // computes {\cal M}_{i+1} from {\cal M}_i, updates the bits of "real"
        let (nlive2, live2) = updatelive ring real0 POWER live1 nchar ncodes nlive1
        // computes {\cal C}_{i+1} from {\cal C}_i, updates "live"

        // 5. checkContract()
        (* This verifies that the set claimed to be a contract for the
           configuration really is. *)
        let z = checkContract live2 nlive2 diffangle sameangle contract POWER
        ()

      //raise (MyException ("test error" + (Convert.ToString 7))) //|> ignore
      true
    with
      | MyException str -> printfn "exception: %s" str; false
      | _               -> printfn "unknown";           false



