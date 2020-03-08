namespace Reduce

//open System
open System.Diagnostics
open LibraryFS
open LibraryCS
//open FSharpPlus.Lens

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
    let edgeno = Array.init EDGES (fun _ -> Array.zeroCreate EDGES)

    // ★★★ stripSub1
    let mutable u = 0
    for v in 1..ring do
      u <- if v > 1 then v - 1 else ring
      edgeno.[u].[v] <- v
      edgeno.[v].[u] <- v

    let done0 = Array.replicate MVERTS false
    let mutable term  = 3 * (verts - 1) - ring

    // stripSub2
    // edgeno, done0に破壊的代入をおこなう
    term <- LibReduceStrip.StripSub2 (MVERTS, graph, verts, ring, edgeno, done0, term)
    // This eventually lists all the internal edges of the configuration

    // stripSub3
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
            let u        = if v > 1    then v - 1 else ring
            let w        = if v < ring then v + 1 else 1
            let doneIntU = if done0.[u] then 1 else 0
            let doneIntW = if done0.[w] then 1 else 0
            let inter    = 3 * graph.[v+2].[0+1] + 4 * (doneIntU + doneIntW)
            if inter > maxint then
              maxint <- inter
              best   <- v
            else ()
            loop4 (v + 1)
        else ()
      loop4 1

      let grav = graph.[best+2]
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
  let findangles
        (graph     : int array array)
        (angle     : TpAngle)
        (diffangle : TpAngle)
        (sameangle : TpAngle)
        (edgeno    : TpEdgeno) =

    let edge      = 3 * graph.[0+1].[0] - 3 - graph.[0+1].[1]

    let contract  = Array.replicate (EDGES + 1) 0
    contract.[0]     <- graph.[1+1].[0] // number of edges in contract
    contract.[EDGES] <- graph.[0+1].[3]
    for i in 1..contract.[0] do
      let u = graph.[2].[2 * i - 1]
      let v = graph.[2].[2 * i]
      Debug.Assert((edgeno.[u].[v] >= 1),
        "         ***  ERROR: CONTRACT CONTAINS NON-EDGE  ***\n\n")
      contract.[edgeno.[u].[v]] <- 1

    for i in 0..(EDGES-1) do
      angle.[i].[0]     <- 0
      diffangle.[i].[0] <- 0
      sameangle.[i].[0] <- 0
    diffangle.[0].[0] <- graph.[0+1].[0]
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
  let findlive ring bigno live0 ncodes (angle : TpAngle) extentclaim =
    //let ring      = angle.[0].[1] // ring-size
    let ed        = angle.[0].[2]
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

  // 4. update()
  let rec augment
            n
            (interval : int array)
            depth
            (weight : int array array)
            (matchweight : int array array array)
            live
            real
            (pnreal : byref<int>)
            ring
            basecol
            on
            (pbit : byref<sbyte>)
            (prealterm : byref<int>)
            nchar =
    (* Finds all matchings such that every match is from one of the given
     * intervals. (The intervals should be disjoint, and ordered with smallest
     * first, and lower end given first.) For each such matching it examines all
     * signings of it, and adjusts the corresponding entries in "real" and
     * "live". *)
    let newinterval = Array.replicate 10 0

    LibReduceUpdate.Checkreality (depth, weight, live, real, &pnreal, ring, basecol, on, &pbit, &prealterm, nchar)
    let depth1 = depth + 1
    for r in 1..n do
      let lower = interval.[2 * r - 1]
      let upper = interval.[2 * r]
      for i in (lower + 1)..upper do
        for j in lower..(i-1) do
          weight.[depth1] <- matchweight.[i].[j]
          for h in 1..(2 * r - 2) do
            newinterval.[h] <- interval.[h]
          let mutable newn = r - 1
          let mutable h2   = 2 * r - 1
          if j > lower + 1 then
            newn <- newn + 1
            newinterval.[h2] <- lower
            h2 <- h2 + 1
            newinterval.[h2] <- j - 1
            h2 <- h2 + 1
          if i > j + 1 then
            newn <- newn + 1
            newinterval.[h2] <- j + 1
            h2 <- h2 + 1
            newinterval.[h2] <- i - 1
            h2 <- h2 + 1
          augment newn newinterval depth1 weight matchweight live real &pnreal ring basecol on &pbit &prealterm nchar
    ()
  let testmatch ring real live nchar =
    (* This generates all balanced signed matchings, and for each one, tests
     * whether all associated colourings belong to "live". It writes the answers
     * in the bits of the characters of "real". *)

    let mutable nreal = 0
    (* "nreal" will be the number of balanced signed matchings such that all
    * associated colourings belong to "live"; ie the total number of nonzero
    * bits in the entries of "real" *)
    let mutable bit = 1y
    let mutable realterm = 0
    // First, it generates the matchings not incident with the last ring edge

    let matchweight = Array.init 16 (fun _ -> (Array.init 16 (fun _ -> Array.zeroCreate 4)))
    let interval    = Array.replicate 10 0
    let weight      = Array.init 16 (fun _ -> Array.zeroCreate 4)
    for a in 2..ring do
      for b in 1..(a-1) do
        matchweight.[a].[b].[0] <- 2 * (POWER.[a] + POWER.[b])
        matchweight.[a].[b].[1] <- 2 * (POWER.[a] - POWER.[b])
        matchweight.[a].[b].[2] <- POWER.[a] + POWER.[b]
        matchweight.[a].[b].[3] <- POWER.[a] - POWER.[b]
    for a in 2..(ring-1) do
      for b in 1..(a-1) do
        let mutable n = 0
        weight.[1] <- matchweight.[a].[b]
        if b >= 3 then
          n <- 1
          interval.[1] <- 1
          interval.[2] <- b - 1
        if a >= b + 3 then
          n <- n + 1
          interval.[2 * n - 1] <- b + 1
          interval.[2 * n]     <- a - 1
        augment n interval 1 weight matchweight live real &nreal ring 0 0 &bit &realterm nchar

    // now, the matchings using an edge incident with "ring"
    for a in 2..ring do
      for b in 1..(a-1) do
        matchweight.[a].[b].[0] <-  POWER.[a] + POWER.[b]
        matchweight.[a].[b].[1] <-  POWER.[a] - POWER.[b]
        matchweight.[a].[b].[2] <- -POWER.[a] - POWER.[b]
        matchweight.[a].[b].[3] <- -POWER.[a] - 2 * POWER.[b]
    for b in 1..(ring-1) do
      let mutable n = 0
      weight.[1] <- matchweight.[ring].[b]
      if b >= 3 then
        n <- 1
        interval.[1] <- 1
        interval.[2] <- b - 1
      if ring >= b + 3 then
        n <- n + 1
        interval.[2 * n - 1] <- b + 1
        interval.[2 * n]     <- ring - 1
      augment n interval 1 weight matchweight live real &nreal ring ((POWER.[ring + 1] - 1) / 2) 1 &bit &realterm nchar
    printfn "                       %d" nreal //right

    ()

  let updateSub (live : int array) ncols (p : byref<int>) =
    (* runs through "live" to see which colourings still have `real' signed
     * matchings sitting on all three pairs of colour classes, and updates "live"
     * accordingly; returns 1 if nlive got smaller and stayed >0, and 0 otherwise *)

    let nlive = p
    let mutable newnlive = 0

    if live.[0] > 1 then
      live.[0] <- 15

    for i in 0..(ncols-1) do
      if live.[i] <> 15 then
        live.[i] <- 0
      else
        newnlive <- newnlive + 1
        live.[i] <- 1

    p <- newnlive
    printf "             %4d" newnlive

    if (newnlive < nlive) && (newnlive > 0) then
      true
    else
      if newnlive = 0 then
        printfn "\n\n\n                  ***  D-reducible  ***\n"
      else
        printfn "\n\n\n                ***  Not D-reducible  ***"
      false

  let update ring real live nchar ncodes (nlive : int) =
    let mutable nlive1 = nlive
    // stillreal()でliveに破壊的代入をおこなう
    testmatch ring real live nchar
    // nlive1、liveに破壊的代入をおこなう
    while (updateSub live ncodes &nlive1) do
      // stillreal()でliveに破壊的代入をおこなう
      testmatch ring real live nchar
      // computes {\cal M}_{i+1} from {\cal M}_i, updates the bits of "real" */
    (nlive1, live)

  // 5. checkContract()
  // checks that no colouring in live is the restriction to E(R) of a
  // tri-coloring of the free extension modulo the specified contract
  let checkContract ring bigno live2 nlive2 (diffangle : TpAngle) (sameangle : TpAngle) (contract : int array) =
    Debug.Assert((contract.[0] <> 0),
      "       ***  ERROR: NO CONTRACT PROPOSED  ***\n\n")
    Debug.Assert((nlive2 = contract.[EDGES]),
      "       ***  ERROR: DISCREPANCY IN EXTERIOR SIZE  ***\n\n")

    let mutable start = diffangle.[0].[2]
    let c = Array.replicate EDGES 0
    let forbidden = Array.replicate EDGES 0 // called F in the notes
    while contract.[start] <> 0 do
      start <- start - 1
    c.[start] <- 1
    let mutable j = start - 1
    while contract.[j] <> 0 do
      j <- j - 1
    let dm = diffangle.[j]
    let sm = sameangle.[j]
    c.[j] <- 1
    let mutable u = 4
    let imax1 = if dm.[0] >= 4 then 4 else dm.[0]
    for i in 1..imax1 do
      u <- u ||| c.[dm.[i]]
    let imax2 = if sm.[0] >= 4 then 4 else sm.[0]
    for i in 1..imax2 do
      u <- u ||| ~~~c.[sm.[i]]
    forbidden.[j] <- u

    LibReduceContract.CheckContractSub (forbidden, c, contract, j, start, diffangle, sameangle, bigno, ring, live2, POWER)


  // main routine
  let reduce =
    printfn "start Reduce.fs"

    let graphs = LibFS.readFileGoodConfsR
    let mutable angle     = Array.init EDGES (fun _ -> Array.zeroCreate 5)
    let mutable diffangle = Array.init EDGES (fun _ -> Array.zeroCreate 5)
    let mutable sameangle = Array.init EDGES (fun _ -> Array.zeroCreate 5)

    let mutable i = 0
    for graph in Array.take 11 (graphs) do
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
      let (angle2, diffangle2, sameangle2, contract) = findangles graph angle diffangle sameangle edgeno
      angle     <- angle2
      diffangle <- diffangle2
      sameangle <- sameangle2

      // 3. findlive()
      let ring   = graph.[0+1].[1] // ring-size
      let ncodes = (POWER.[ring    ] + 1) / 2 // number of codes of colorings of R
      let bigno  = (POWER.[ring + 1] - 1) / 2 // needed in "inlive"
      let live0  = Array.replicate ncodes 1
      let real0  = Array.replicate (SIMATCHNUMBER.[MAXRING] / 8 + 2) 255
      let nchar  = SIMATCHNUMBER.[ring] / 8 + 1
      let (nlive1, live1) = findlive ring bigno live0 ncodes angle graph.[0+1].[2]

      // 4. update()
      // computes {\cal M}_{i+1} from {\cal M}_i, updates the bits of "real"
      let (nlive2, live2) = update ring real0 live1 nchar ncodes nlive1
      // computes {\cal C}_{i+1} from {\cal C}_i, updates "live"

      // 5. checkContract()
      (* This verifies that the set claimed to be a contract for the
         configuration really is. *)
      if nlive2 = 0 then
        if contract.[0] = 0 then
          ()  // D可約のときは、checkContract()へ行かない
        else
          Debug.Assert(false,
            "         ***  ERROR: CONTRACT PROPOSED  ***\n\n")
      else
        checkContract ring bigno live2 nlive2 diffangle sameangle contract

    true



