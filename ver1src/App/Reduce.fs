namespace Reduce

//open System
open System.Diagnostics
open LibraryFS
//open FSharpPlus.Lens
open LibraryCS

module Re =
  let MVERTS        = 27 // max number of vertices in a free completion + 1
  let DEG           = 13 // max degree of a vertex in a free completion + 1
                         // must be at least 13 because of row 0
  let EDGES         = 62 // max number of edges in a free completion + 1
  let MAXRING       = 14 // max ring-size
                         // 3^(i-1)
  let POWER         = [|0; 1; 3; 9; 27; 81; 243; 729; 2187; 6561; 19683; 59049; 177147; 531441; 1594323; 4782969; 14348907|]
  let SIMATCHNUMBER = [0; 0; 1; 3; 10; 30; 95; 301; 980; 3228; 10797; 36487; 124542; 428506; 1485003]

  type TpAngle      = int array array
  type TpEdgeno     = int array array

  // 1. strip()
  let strip (graph : int array array) =
    let verts  = graph.[0+1].[0]
    let ring   = graph.[0+1].[1] // ring-size
    let edgeno = Array.replicate EDGES (Array.replicate EDGES 0)

    // ★★★ stripSub1
    let mutable u = 0
    for v in 1..ring do
      u <- if v > 1 then v - 1 else ring
      edgeno.[u].[v] <- v
      edgeno.[v].[u] <- v

    let done0 = Array.replicate MVERTS false
    let mutable term  = 3 * (verts - 1) - ring

    // ★★★ stripSub2
    // edgeno, done0に破壊的代入をおこなう
    term <- LibReduceStrip.StripSub2 (MVERTS, graph, verts, ring, edgeno, done0, term)
    // This eventually lists all the internal edges of the configuration

    (* let r4 = setl (_2 << _1) 42 ("hello", ("world", "!!!"))
    printfn "%A" r4
    let r6 = setl (items) 100 [0..4]
    printfn "%A" r6 *)

    // ★★★ stripSub3
    // Now we must list the edges between the interior and the ring
    let mutable maxint = 0
    for _ in 1..ring do
      maxint <- 0

      let mutable best = 0
      let rec loop4 v =
        if v <= ring then
          if done0.[v] then
            loop4 (v + 1)
          else
            let u       = if v > 1    then v - 1 else ring
            let w       = if v < ring then v + 1 else 1
            let doneInt = if done0.[u] || done0.[w] then 1 else 0
            let inter   = 3 * graph.[v+1].[0] + 4 * doneInt
            if inter > maxint then
              maxint <- inter
              best   <- v
            else ()
            loop4 (v + 1)
        else ()
      loop4 1

      let grav = graph.[best+3]
      let u    = if best > 1 then best - 1 else ring
      if done0.[u] then
        for h in (grav.[0+1] - 1) .. -1 .. 2 do
          edgeno.[best].[grav.[h+1]] <- term
          edgeno.[grav.[h+1]].[best] <- term
          term <- term - 1
      else
        for h in 2..(grav.[0+1] - 1) do
          edgeno.[best].[grav.[h+1]] <- term
          edgeno.[grav.[h+1]].[best] <- term
          term <- term - 1
      done0.[best] <- true

    edgeno : TpEdgeno // return

  // 2. findangles()
  let findangles (graph : int array array) (edgeno : int array array) =
    let edge      = 3 * graph.[0+1].[0] - 3 - graph.[0+1].[1]

    let contract  = Array.replicate (EDGES + 1) 0
    contract.[0]     <- graph.[1+1].[0] // number of edges in contract
    contract.[EDGES] <- graph.[0+1].[3]
    for i in 1..contract.[0] do
      let u = graph.[1+1].[2 * i - 1]
      let v = graph.[1+1].[2 * i]
      Debug.Assert((edgeno.[u].[v+1] >= 1),
        "         ***  ERROR: CONTRACT CONTAINS NON-EDGE  ***\n\n")
      contract.[edgeno.[u].[v+1]] <- 1

    let angle     = Array.replicate EDGES (Array.replicate 5 0)
    let diffangle = Array.replicate EDGES (Array.replicate 5 0)
    let sameangle = Array.replicate EDGES (Array.replicate 5 0)
    diffangle.[0].[0] <- 0 //graph.[0+1].[0]
    diffangle.[0].[1] <- graph.[0+1].[1]
    diffangle.[0].[2] <- edge
    angle.[0].[0]     <- diffangle.[0].[0]
    angle.[0].[1]     <- diffangle.[0].[1]
    angle.[0].[2]     <- diffangle.[0].[2]

    // ★★★ findanglesSub2
    // angle, diffangle, sameangleに破壊的代入をおこなう
    LibReduceAngle.FindanglesSub2 (graph, edgeno, contract, angle, diffangle, sameangle)

    // ★★★ findanglesSub3
    LibReduceAngle.FindanglesSub3 (MVERTS, graph, contract)

    (angle, diffangle, sameangle, contract) : TpAngle * TpAngle * TpAngle * int array

  // 3. findlive()
  (* computes {\cal C}_0 and stores it in live. That is, computes codes of
     colorings of the ring that are not restrictions of tri-colorings of the
     free extension. Returns the number of such codes *)
  let findlive ring live0 ncodes (angle : int array array) extentclaim =
    //let ring      = angle.[0].[1] // ring-size
    let ed        = angle.[0].[2]
    let bigno     = (POWER.[ring + 1] - 1) / 2 // number of codes of colorings of R
    let c         = Array.replicate EDGES 0
    let j         = ed - 1
    c.[ed]        <- 1
    c.[j]         <- 2
    let forbidden = Array.replicate EDGES 0
    forbidden.[j] <- 5

    let structureTuple = LibReduceLive.FindliveSub (bigno, angle, POWER, ring, ed, extentclaim, ncodes, live0, j, c, forbidden)
    // 構造体タプルのパターンマッチ
    match structureTuple with
      | struct (ncodes1, live1) -> (ncodes1, live1)

  // 4. updatelive()
  let updatelive ring real0 live1 nchar ncodes nlive1 =
    (nlive1, live1)

  // 5. checkContract()
  let checkContract live2 nlive2 diffangle sameangle contract =
    ()

  let reduce =
    printfn "Reduce.fs"

    let graphs = LibFS.readFileGoodConfsR
    printfn "%d" graphs.[1].[1].[0]

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
      let live0  = Array.replicate ncodes 1
      let real0  = Array.replicate (SIMATCHNUMBER.[MAXRING] / 8 + 2) 255
      let nchar  = SIMATCHNUMBER.[ring] / 8 + 1
      let (nlive1, live1) = findlive ring live0 ncodes angle graph.[0+1].[2]

      // 4. updatelive()
      // computes {\cal M}_{i+1} from {\cal M}_i, updates the bits of "real"
      let (nlive2, live2) = updatelive ring real0 live1 nchar ncodes nlive1
      // computes {\cal C}_{i+1} from {\cal C}_i, updates "live"

      // 5. checkContract()
      (* This verifies that the set claimed to be a contract for the
         configuration really is. *)
      checkContract live2 nlive2 diffangle sameangle contract

    true



