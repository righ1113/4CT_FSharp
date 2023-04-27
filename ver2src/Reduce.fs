namespace Reduce

// open System
open System.IO
open System.Diagnostics
open FSharp.Data


module Const =
  let MVERTS         = 27 // max number of vertices in a free completion + 1
  let DEG            = 13 // max degree of a vertex in a free completion + 1
                          // must be at least 13 because of row 0
  let EDGES          = 62 // max number of edges in a free completion + 1
  let MAXRING        = 14 // max ring-size
                         // 3^(i-1)
  let POWER          = [|0; 1; 3; 9; 27; 81; 243; 729; 2187; 6561; 19683; 59049; 177147; 531441; 1594323; 4782969; 14348907|]
  let SIMATCHNUMBER  = [0; 0; 1; 3; 10; 30; 95; 301; 980; 3228; 10797; 36487; 124542; 428506; 1485003]

  type TpAngle       = int array array
  type TpedgeNo      = int array array
  type TpGConfMajor  = {verts: int; ring: int; term: int; edges: int; claim: int; cont0: int; contE: int; bigno: int; ncodes: int; nchar: int;}
  type TpAnglePack   = int array array * TpedgeNo * TpAngle * TpAngle * TpAngle * int array
  type TpLiveTwin    = int array * int
  type TpLiveState   = TpLiveTwin * int array * int * int8 * int * TpGConfMajor * TpAnglePack * bool * bool

  type TpConfFmt     = JsonProvider<"[[[1]]]">


module EdgeNo =
  exception Continue
  exception Break
  exception Return of int
  let private inInterval (grav: int array) (don: bool array) =
    try
      let d = grav.[1] in
      let mutable first = 1 in
      while first < d && not don.[grav.[first + 1]] do first <- first + 1
      if first = d then raise (Return (if don.[grav.[d + 1]] then 1 else 0));
      let mutable last = first in
      while last < d && don.[grav.[last + 2]] do last <- last + 1
      let mutable length = last - first + 1 in
      if last  = d then raise (Return length);
      if first > 1 then
        for j = last + 2 to d do if don.[grav.[j + 1]] then raise (Return 0)
        raise (Return length)
      let mutable worried = false in
      for j = last + 2 to d do
        if don.[grav.[j + 1]] then length <- length + 1; worried <- true
        else if worried then raise (Return 0)
      length
    with
    | Return x -> x;
  // 1. strip()
  let run (gConf: int array array) (major: Const.TpGConfMajor) =
    let verts  = major.verts
    let ring   = major.ring
    let edgeNo: Const.TpedgeNo = Array.init Const.EDGES (fun _ -> Array.zeroCreate Const.EDGES)

    // stripSub1
    let mutable u = 0
    for v in 1..ring do
      u <- if v > 1 then v - 1 else ring
      edgeNo.[u].[v] <- v
      edgeNo.[v].[u] <- v
    let done0 = Array.replicate Const.MVERTS false
    let mutable term  = major.term

    // stripSub2
    let mutable best = 1
    let max = Array.replicate Const.MVERTS 0
    (* 2. *)
    for _ = (ring + 1) to verts do
      let mutable maxint = 0
      let mutable maxes  = 0
      (* 2_1. *)
      for v = (ring + 1) to verts do
        try
          if done0.[v] then raise Continue;
          let inter = inInterval gConf.[v + 2] done0 in
          if inter > maxint then
            maxint <- inter; maxes <- 1; max.[1] <- v
          else
            if inter = maxint then maxes <- maxes + 1; max.[maxes] <- v
        with
        | Continue -> ()
      let mutable maxdeg = 0
      (* 2_2. *)
      for h = 1 to maxes do
        let d = gConf.[max.[h] + 2].[1] in
        if d > maxdeg then maxdeg <- d; best <- max.[h]
      let grav = gConf.[best + 2] in
      let d = grav.[1]
      let mutable first = 1
      let mutable previous = done0.[grav.[d + 1]]
      (* 2_3. *)
      try
        while previous || not done0.[grav.[first + 1]] do
          previous <- done0.[grav.[first + 1]]
          first    <- first + 1;
          if first > d then first <- 1; raise Break
      with
      | Break -> ()
      let mutable h = first
      (* 2_4. *)
      try
        while done0.[grav.[h + 1]] do
          edgeNo.[best].[grav.[h+1]] <- term
          edgeNo.[grav.[h+1]].[best] <- term
          term <- term - 1
          if h = d then
            if first = 1 then raise Break
            h <- 0
          h <- h + 1
      with
      | Break -> ()
      done0.[best] <- true

    // stripSub3
    // Now we must list the edges between the interior and the ring
    let mutable maxint = 0
    for _ = 1 to ring do
      maxint <- 0
      for v = 1 to ring do
        try
          if done0.[v] then raise Continue;
          let u        = if v > 1     then v - 1 else ring
          let w        = if v < ring  then v + 1 else 1
          let doneIntU = if done0.[u] then 1     else 0
          let doneIntW = if done0.[w] then 1     else 0
          let inter    = 3 * gConf.[v+2].[1] + 4 * (doneIntU + doneIntW)
          if inter > maxint then maxint <- inter; best <- v
        with
        | Continue -> ()
      let grav = gConf.[best+2]
      let u = if best > 1 then best - 1 else ring
      if done0.[u] then
        for h = grav.[0+1] - 1 downto 2 do
          edgeNo.[best].[grav.[h+1]] <- term
          edgeNo.[grav.[h+1]].[best] <- term
          term <- term - 1
      else
        for h = 2 to grav.[0+1] - 1 do
          edgeNo.[best].[grav.[h+1]] <- term
          edgeNo.[grav.[h+1]].[best] <- term
          term <- term - 1
      done0.[best] <- true
    // --
    (gConf, (major : Const.TpGConfMajor), edgeNo)



module Angles =
  exception Continue
  exception Break
  exception Return of int
  let angle     = Array.init Const.EDGES (fun _ -> Array.zeroCreate 5)
  let diffangle = Array.init Const.EDGES (fun _ -> Array.zeroCreate 5)
  let sameangle = Array.init Const.EDGES (fun _ -> Array.zeroCreate 5)
  let contract  = Array.replicate (Const.EDGES + 1) 0

  let private anglesSub2Sub x y c =
    try
      if x <= c then raise (Return 0)
      let d = if angle.[c].[0] >= 4 then 4 else angle.[c].[0] <- angle.[c].[0] + 1; angle.[c].[0]
      angle.[c].[d] <- x
      // printfn "x,y,c: %d %d %d" x y c
      if contract.[x] = 0 && contract.[y] = 0 && contract.[c] = 0 then
        let e = if diffangle.[c].[0] >= 4 then 4 else diffangle.[c].[0] <- diffangle.[c].[0] + 1; diffangle.[c].[0]
        diffangle.[c].[e] <- x
      if contract.[y] = 0 then raise (Return 0)
      let e = if sameangle.[c].[0] >= 4 then 4 else sameangle.[c].[0] <- sameangle.[c].[0] + 1; sameangle.[c].[0]
      sameangle.[c].[e] <- x
      1
    with
    | Return x -> x;

  let private anglesSub2 (gConf : int array array) (edgeNo : Const.TpedgeNo) =
    for v in 1..gConf.[0 + 1].[0] do
      try
        for h in 1..gConf.[v + 2].[0 + 1] do
          try
            if v <= gConf.[1].[1] && h = gConf.[v + 2].[1] then raise Continue
            if h >= Array.length gConf.[v + 2] then raise Break
            let i = if h < gConf.[v + 2].[1] then h + 1 else 1
            let u = gConf.[v + 2].[h + 1]
            let w = gConf.[v + 2].[i + 1]
            let a = edgeNo.[v].[w]
            let b = edgeNo.[u].[w]
            let c = edgeNo.[u].[v]
            // どっちかが0なら通過
            Debug.Assert((contract.[a] = 0 || contract.[b] = 0), "***  ERROR: CONTRACT IS NOT SPARSE  ***")
            anglesSub2Sub a b c |> ignore
            anglesSub2Sub b a c |> ignore
          with
          | Continue -> ()
      with
      | Break -> ()
    true

  let private anglesSub3 (gConf : int array array) verts ring =
    let neighbour = Array.replicate Const.MVERTS false
    // checking that there is a triad
    try
      if contract.[0] < 4 then raise (Return 1)
      let mutable v = ring + 1
      while v <= verts do
        try
          // v is a candidate triad
          let mutable a = 0
          let mutable i = 1
          while i <= gConf.[v + 2].[1] do
            let u = gConf.[v + 2].[i + 1]
            try
              for j in 1..8 do
                if u = gConf.[2].[j] then a <- a + 1; raise Break
            with
            | Break -> ()
            i <- i + 1
          if a < 3 then raise Continue
          if gConf.[v + 2].[0] >= 6 then raise (Return 1)
          for x in 1..verts               do neighbour[x]                 <- false
          for y in 1..(gConf.[v + 2].[1]) do neighbour[gConf.[y + 2].[i]] <- true
          for j in 1..8                   do if not neighbour[gConf.[2].[j]] then raise (Return 1)
          v <- v + 1
        with
        | Continue -> v <- v + 1; ()
      Debug.Assert((1 = 2), "***  ERROR: CONTRACT HAS NO TRIAD  ***")
      0 // ここには来ない
    with
    | Return x -> x

  let run (gConf : int array array) (edgeNo : Const.TpedgeNo) (major : Const.TpGConfMajor) =
    contract.[0]           <- major.cont0 // number of edges in contract
    contract.[Const.EDGES] <- major.contE
    for i in 1..contract.[0] do
      let u = gConf.[2].[2 * i - 1]
      let v = gConf.[2].[2 * i]
      Debug.Assert((edgeNo.[u].[v] >= 1), "         ***  ERROR: CONTRACT CONTAINS NON-EDGE  ***\n\n")
      contract.[edgeNo.[u].[v]] <- 1
    for i in 0..(Const.EDGES - 1) do
      angle.[i].[0]     <- 0
      diffangle.[i].[0] <- 0
      sameangle.[i].[0] <- 0
    diffangle.[0].[0] <- major.verts
    diffangle.[0].[1] <- major.ring
    diffangle.[0].[2] <- major.edges
    angle.[0].[0]     <- diffangle.[0].[0]
    angle.[0].[1]     <- diffangle.[0].[1]
    angle.[0].[2]     <- diffangle.[0].[2]
    // findanglesSub2
    anglesSub2 gConf edgeNo |> ignore
    // findanglesSub3
    anglesSub3 gConf major.verts major.ring |> ignore
    (gConf, edgeNo, angle, diffangle, sameangle, contract) : Const.TpAnglePack


module MLive =
  exception Return of int
  // /* computes {\cal C}_0 and stores it in live. That is, computes codes of
  // * colorings of the ring that are not restrictions of tri-colorings of the
  // * free extension. Returns the number of such codes */
  let private isEndFL (j : int byref) (c : int array) (extent : int) (major : Const.TpGConfMajor) =
    let printStatus ring totalcols (extent : int) extentclaim =
      printf "\n\n   This has ring-size %d, so there are %d colourings total,\n" ring totalcols
      printf "   and %d balanced signed matchings.\n" Const.SIMATCHNUMBER.[ring]
      printf "\n   There are %d colourings that extend to the configuration." extent
      Debug.Assert((extent = extentclaim), "   *** ERROR31: DISCREPANCY IN NUMBER OF EXTENDING COLOURINGS ***")
      printf "\n\n            remaining               remaining balanced\n"
      printf "           colourings               signed matchings\n"
      printf "\n              %7d" (totalcols - extent)
      true
    try
      c.[j] <- c.[j] <<< 1
      while c.[j] &&& 8 <> 0 do
        if j >= major.edges - 1 then
          printStatus major.ring major.ncodes extent major.claim |> ignore
          raise (Return (major.ncodes - extent)) // 0 にはならないはず
        j <- j + 1
        c.[j] <- c.[j] <<< 1
      0
    with
    | Return x -> x
  let private chgLive
      (col : int array) (angle : Const.TpAngle) (live : int array) (extent : int byref) (major : Const.TpGConfMajor) =
    let weight = Array.replicate 5 0
    for i = 1 to major.ring do
      let sum = 7 - col.[angle.[i].[1]] - col.[angle.[i].[2]]
      weight.[sum] <- weight.[sum] + Const.POWER.[i]
    let mutable min = weight.[4]
    let mutable max = weight.[4]
    for i = 1 to 2 do
      let w = weight.[i]
      if w < min then min <- w
      else if w > max then max <- w
    let colno = major.bigno - 2 * min - max
    if live.[colno] <> 0 then extent <- extent + 1; live.[colno] <- 0
    true
  let run (angle : Const.TpAngle) (major : Const.TpGConfMajor) =
    let c = Array.replicate (Const.EDGES) 0
    let forbidden = Array.replicate (Const.EDGES) 0
    let live = Array.replicate (major.ncodes) 1
    c[major.edges] <- 1
    let mutable j = major.edges - 1
    // printfn "aaa: %d" j
    c[j] <- 2
    forbidden[j] <- 5
    let mutable extent = 0
    let y =
      try
        while true do
          while 0 <> (forbidden.[j] &&& c.[j]) do
            let ret = isEndFL &j c extent major
            // printfn "bbb: %d" j
            if ret <> 0 then raise (Return ret)
          if j = major.ring + 1 then
            chgLive c angle live &extent major |> ignore
            // printfn "ccc: %d" j
            let ret = isEndFL &j c extent major
            if ret <> 0 then raise (Return ret)
          else
            j <- j - 1
            // printfn "ddd: %d" j
            let am = angle.[j]
            c[j] <- 1
            let mutable u = 0
            for i = 1 to am.[0] do u <- u ||| c.[am.[i]]
            forbidden.[j] <- u
        0 // ここには来ない
      with
      | Return x -> x
    (live, y)



module DReduce =
  exception Return of int
  let interval    = Array.replicate 10 0
  let weight      = Array.init 16 (fun _ -> Array.zeroCreate 4)
  let matchweight = Array.init 16 (fun _ -> Array.init 16 (fun _ -> Array.zeroCreate 4))
  let mutable nReal2 = 0
  let testMatch (twin, real, nReal, bit, realTerm, (major : Const.TpGConfMajor), d, b1, b2) =
    // long dReduceTestMatch(long ring, ref byte[] real2, long[] power, ref byte[] live, long nbyte) pure {
    // long a, b, n, nReal, realterm;
    // byte bit;
    // /* "nReal" will be the number of balanced signed matchings such that all associated colourings belong to "live",
    // * ie the total number of nonzero bits in the entries of "real" */
    // nReal = 0; bit = 1; realterm = 0;
    let mutable n = 0
    // /* First, it generates the matchings not incident with the last ring edge */
    for a = 2 to major.ring do
      for b = 1 to a - 1 do
        matchweight.[a].[b].[0] <- 2 * (Const.POWER.[a] + Const.POWER.[b]);
        matchweight.[a].[b].[1] <- 2 * (Const.POWER.[a] - Const.POWER.[b]);
        matchweight.[a].[b].[2] <-      Const.POWER.[a] + Const.POWER.[b];
        matchweight.[a].[b].[3] <-      Const.POWER.[a] - Const.POWER.[b];
    for a = 2 to major.ring - 1 do
      for b = 1 to a - 1 do
        n <- 0; weight.[1] <- matchweight.[a].[b]
        if b >= 3 then     n <- 1;     interval.[1] <- 1;             interval.[2]     <- b - 1
        if a >= b + 3 then n <- n + 1; interval.[2 * n - 1] <- b + 1; interval.[2 * n] <- a - 1
        // augment(n, interval, 1L, weight, matchweight, live, real2, nReal, ring, 0L, 0L, bit, realterm, nbyte);
    // /* now, the matchings using an edge incident with "ring" */
    for a = 2 to major.ring do
      for b = 1 to a - 1 do
        matchweight.[a].[b].[0] <-  Const.POWER.[a] +     Const.POWER.[b];
        matchweight.[a].[b].[1] <-  Const.POWER.[a] -     Const.POWER.[b];
        matchweight.[a].[b].[2] <- -Const.POWER.[a] -     Const.POWER.[b];
        matchweight.[a].[b].[3] <- -Const.POWER.[a] - 2 * Const.POWER.[b];
    for b = 1 to major.ring - 1 do
      n <- 0; weight.[1] <- matchweight.[major.ring].[b]
      if b >= 3 then              n <- 1;     interval.[1] <- 1;             interval.[2]     <- b - 1
      if major.ring >= b + 3 then n <- n + 1; interval.[2 * n - 1] <- b + 1; interval.[2 * n] <- major.ring - 1
      // augment(n, interval, 1L, weight, matchweight, live, real2, nReal, ring,
      //   (power[ring + 1] - 1) / 2, 1L, bit, realterm, nbyte);
    (twin, real, nReal2, bit, realTerm, major, d, b1, b2)

  let updateLive (twin, real, nReal, _, _, (major : Const.TpGConfMajor), d, b1, b2) =
    let isUpdate ncols ((live : int array), nLive) nReal =
      let mutable newnlive = 0
      let ret =
        try
          if live.[0] > 1 then live.[0] <- 15
          for i = 0 to ncols - 1 do
            if live.[i] <> 15 then live.[i] <- 0
            else
              newnlive <- newnlive + 1; live.[i] <- 1;
          printf "               %d\n" nReal // right
          printf "            %9d" newnlive  // left
          if (newnlive < nLive) && (newnlive > 0) then raise (Return 0)
          if 0 = newnlive then
            printf "\n\n\n                  ***  D-reducible  ***\n\n"
          else
            printf "\n\n\n                ***  Not D-reducible  ***\n"
          1
        with
        | Return x -> x
      (1 = ret, 0 = newnlive, (live, newnlive))
    let (b1, b2, twin2) = isUpdate (major.ncodes) twin nReal
    (twin2, real, 0, 1y, 0, major, d, true, b2)

module Re =
  let rec private until p f (a: 'a) = if p a then a else until p f (f a)

  let private readFileGoodConfsR =
    File.ReadAllText "data/ReGoodConfs.txt"
    |> Const.TpConfFmt.Parse
  let private gConfs = readFileGoodConfsR

  let private makeGConfMajor (gConf: int array array) =
    let verts0 = gConf.[1].[0]
    let ring0  = gConf.[1].[1]
    ( gConf, ({ verts  = verts0;
                ring   = ring0;
                term   = 3 * (verts0 - 1) - ring0;
                edges  = 3 * verts0 - 3 - ring0;
                claim  = gConf.[1].[2];
                cont0  = gConf.[2].[0];
                contE  = gConf.[1].[3];
                bigno  = (Const.POWER.[ring0 + 1] - 1) / 2;
                ncodes = (Const.POWER.[ring0] + 1) / 2;
                nchar  = Const.SIMATCHNUMBER.[ring0] / 8 + 1; }: Const.TpGConfMajor) )

  let private makeEdgeNo (gConf, major) =
    EdgeNo.run gConf major

  let private makeAngle (gConf, (major : Const.TpGConfMajor), edgeNo) =
    (major, Angles.run gConf edgeNo major)

  let private makeLive ((major : Const.TpGConfMajor), ap) =
    let (_, _, an, _, _, _) = ap
    let real = Array.replicate (Const.SIMATCHNUMBER[major.ring] / 8 + 1) -1
    (MLive.run an major, real, 0, 1y, 0, major, ap, false, false): Const.TpLiveState

  let private chkDReduce : Const.TpLiveState -> Const.TpLiveState =
    let p (_, _, _, _, _, _, _, b1, _) = b1
    until p (DReduce.testMatch >> DReduce.updateLive)

  let private chkCReduce _ = true

  let reduce =
    // gConfs |> Array.forall (makeGConfMajor >> makeEdgeNo >> makeAngle >> makeLive >> chkDReduce >> chkCReduce)
    let (liveTwin, _, _, _, _, _, _, _, _) = gConfs.[0] |> (makeGConfMajor >> makeEdgeNo >> makeAngle >> makeLive >> chkDReduce)
    liveTwin



