namespace Reduce

open System
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
  let POWER         = [0; 1; 3; 9; 27; 81; 243; 729; 2187; 6561; 19683; 59049; 177147; 531441; 1594323; 4782969; 14348907]
  let SIMATCHNUMBER = [0; 0; 1; 3; 10; 30; 95; 301; 980; 3228; 10797; 36487; 124542; 428506; 1485003]

  type TpAngle      = int array array
  type TpEdgeno     = int array array

  exception MyException of string

  // 1. strip()
  let ininterval grav done0 =
    (*let d = grav.[0+1]

    let first = 1 //for (first = 1; (first < d) && (not done0.[grav.[first]]); first++);
    if first = d then
      if done0.[grav.[d+1]] then 1 else 0
    else
      let last = first //for (last = first; (last < d) && (done0[grav[last + 1]]); last++);
      let mutable length = last - first + 1
      if last = d then
        length
      else
        if first > 1 then
          for (j = last + 2; j <= d; j++)
            if done0.[grav.[j+1]] then
              return 0
            else ()
          length
        else
          let mutable worried = 0
          for (j = last + 2; j <= d; j++) {
            if done0.[grav.[j+1]] then
              length <- length + 1
              worried <- 1
            else
              if worried then
                return ((long) 0);
              else ()
          length*)
    1
  let strip (graph : int array array) =
    let verts  = graph.[0+1].[0]
    let ring   = graph.[0+1].[1] // ring-size
    let edgeno = Array.replicate EDGES (Array.replicate EDGES 0)

    // ★★★ stripSub1
    (*let mutable u = 0
    for v in 1..ring do
      u <- if v > 1 then v - 1 else ring
      edgeno.[u].[v] <- v
      edgeno.[v].[u] <- v

    let done0 = Array.replicate MVERTS false
    let mutable term  = 3 * (verts - 1) - ring

    // ★★★ stripSub2
    let mutable maxint = 0
    let mutable maxes  = 0
    let max = Array.replicate MVERTS 0
    for _ in (ring + 1) .. (verts) do
      // First we find all vertices from the interior that meet the "done"
      // vertices in an interval, and write them in max[1] .. max[maxes]

      let rec loop1 v =
        if v <= verts then
          if done0.[v] then
            loop1 (v + 1)
          else
            let inter = ininterval graph.[v+1] done0
            if inter > maxint then
              maxint  <- inter
              maxes   <- 1
              max.[1] <- v
            else
              if inter = maxint then
                if maxes+1 < max.Length then
                  maxes <- maxes + 1
                  max.[maxes] <- v
                else ()
              else ()
            loop1 (v + 1)
        else ()
      loop1 (ring + 1)

      // From the terms in max we choose the one of maximum degree
      let mutable d      = 0
      let mutable maxdeg = 0
      let mutable best   = 0
      for h  in 1..maxes do
        d <- graph.[max.[h]+1].[0+1]
        if d > maxdeg then
          maxdeg <- d
          best   <- max.[h]
        else ()
      // So now, the vertex "best" will be the next vertex to be done

      let grav = graph.[best+3]
      d <- grav.[0+1]
      let mutable first = 1
      let mutable previous = done0.[grav.[d+1]]
      let rec loop2 () =
        if previous || not done0.[grav.[first+1]] then
          first    <- first + 1
          previous <- done0.[grav.[first+1]]
          if first >= d then
            first <- 1
            ()
          else loop2 ()
        else ()
      loop2 ()

      let mutable h = 0
      let rec loop3 (index : int) =
        if done0.[grav.[h+1]] then
          edgeno.[best].[grav.[h+1]] <- term
          edgeno.[grav.[h+1]].[best] <- term
          term <- term - 1
          if h = d then
            if first = 1 then ()
            else
              h <- 0
              loop3 (index + 1)
          else loop3 (index + 1)
        else ()
      loop3 first

      done0.[best] <- true*)
    // This eventually lists all the internal edges of the configuration

    (* let r4 = setl (_2 << _1) 42 ("hello", ("world", "!!!"))
    printfn "%A" r4
    let r6 = setl (items) 100 [0..4]
    printfn "%A" r6 *)

    // ★★★ stripSub3
    // Now we must list the edges between the interior and the ring
    (*for _ in 1..ring do
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
      done0.[best] <- true*)

    // return
    edgeno : TpEdgeno

  // 2. findangles()
  let findangles graph edgeno =
    let angle     = Array.replicate EDGES (Array.replicate 5 0)
    let diffangle = Array.replicate EDGES (Array.replicate 5 0)
    let sameangle = Array.replicate EDGES (Array.replicate 5 0)
    let contract  = Array.replicate (EDGES + 1) 0
    (angle, diffangle, sameangle, contract) : TpAngle * TpAngle * TpAngle * int array

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

      let ret = LibCSStrip.Add (2, 3)
      printfn "2+3=%d" ret

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
        checkContract live2 nlive2 diffangle sameangle contract POWER

      //raise (MyException ("test error" + (Convert.ToString 7))) //|> ignore
      true
    with
      | MyException str -> printfn "MyException: %s" str; false
      | _               -> printfn "unknown Exception";   false



