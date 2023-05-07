// 9:13 7m-100 20m-200 100m-300 100m-500 90m-600 26m-33 :343m
// 2:12 5m-100 20m-200 83m-300 155m-600 27m-33          :290m
// 8:30 1m-100 1m-200 1m-300 1m-600 1m-33               :5m
namespace Reduce

// open System
open System.IO
open System.Diagnostics
open FSharp.Data
open LibraryCS


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
  type TpAnglePack   = TpAngle * TpAngle * TpAngle * int array
  type TpLiveTwin    = int array * int
  type TpLiveState   = TpLiveTwin * int8 array * int * TpGConfMajor * TpAnglePack * bool * bool
  type TpConfFmt     = JsonProvider<"[[[1]]]">


module EdgeNo =
  // 1. strip()
  let run (gConf: int array array) (major: Const.TpGConfMajor) =
    let verts, ring  = major.verts, major.ring
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
    term <- LibReduceStrip.StripSub2(Const.MVERTS, gConf, verts, ring, edgeNo, done0, term)
    // stripSub3
    // Now we must list the edges between the interior and the ring
    let mutable maxint = 0
    for _ = 1 to ring do
      maxint <- 0
      for v = 1 to ring do
        if done0.[v] then ()
        else
          let u        = if v > 1     then v - 1 else ring
          let w        = if v < ring  then v + 1 else 1
          let doneIntU = if done0.[u] then 1     else 0
          let doneIntW = if done0.[w] then 1     else 0
          let inter    = 3 * gConf.[v+2].[1] + 4 * (doneIntU + doneIntW)
          if inter > maxint then maxint <- inter; best <- v
      let grav, u = gConf.[best+2], if best > 1 then best - 1 else ring
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
    // output
    (gConf, (major : Const.TpGConfMajor), edgeNo)


module Angles =
  exception Continue
  exception Break
  exception Return of int
  let private angle     = Array.init Const.EDGES (fun _ -> Array.zeroCreate 5)
  let private diffangle = Array.init Const.EDGES (fun _ -> Array.zeroCreate 5)
  let private sameangle = Array.init Const.EDGES (fun _ -> Array.zeroCreate 5)
  let private contract  = Array.replicate (Const.EDGES + 1) 0
  let private anglesSub2Sub x y c =
    try
      if x <= c then raise (Return 0)
      let d = if angle.[c].[0] >= 4 then 4 else angle.[c].[0] <- angle.[c].[0] + 1; angle.[c].[0]
      angle.[c].[d] <- x
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
            let u, w = gConf.[v + 2].[h + 1], gConf.[v + 2].[i + 1]
            let a, b, c = edgeNo.[v].[w], edgeNo.[u].[w], edgeNo.[u].[v]
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
          let mutable a, i = 0, 1
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
      Debug.Assert(false, "***  ERROR: CONTRACT HAS NO TRIAD  ***")
      0 // ここには来ない
    with
    | Return x -> x
  let run (gConf : int array array) (edgeNo : Const.TpedgeNo) (major : Const.TpGConfMajor) =
    // init
    for i = 0 to Const.EDGES - 1 do
      for j = 0 to 4 do
        angle.[i].[j] <- 0
        diffangle.[i].[j] <- 0
        sameangle.[i].[j] <- 0
    for i = 0 to Const.EDGES do
      contract.[i] <- 0
    contract.[0]           <- major.cont0 // number of edges in contract
    contract.[Const.EDGES] <- major.contE
    for i in 1..contract.[0] do
      let u, v = gConf.[2].[2 * i - 1], gConf.[2].[2 * i]
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
    (angle, diffangle, sameangle, contract) : Const.TpAnglePack


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
    let mutable min, max = weight.[4], weight.[4]
    for i = 1 to 2 do
      let w = weight.[i]
      if w < min then min <- w
      else if w > max then max <- w
    let colno = major.bigno - 2 * min - max
    if live.[colno] <> 0 then extent <- extent + 1; live.[colno] <- 0
    true
  let run (angle : Const.TpAngle) (major : Const.TpGConfMajor) =
    let c         = Array.replicate (Const.EDGES) 0
    let forbidden = Array.replicate (Const.EDGES) 0
    let live      = Array.replicate (major.ncodes) 1
    c[major.edges] <- 1
    let mutable j = major.edges - 1
    c[j] <- 2
    forbidden[j] <- 5
    let mutable extent = 0
    let y =
      try
        while true do
          while 0 <> (forbidden.[j] &&& c.[j]) do
            let ret = isEndFL &j c extent major
            if ret <> 0 then raise (Return ret)
          if j = major.ring + 1 then
            chgLive c angle live &extent major |> ignore
            let ret = isEndFL &j c extent major
            if ret <> 0 then raise (Return ret)
          else
            j <- j - 1
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
  let private interval    = Array.replicate 10 0
  let private weight      = Array.init 16 (fun _ -> Array.zeroCreate 4)
  let private matchweight = Array.init 16 (fun _ -> Array.init 16 (fun _ -> Array.zeroCreate 4))
  let mutable private nReal2, bit2, realTerm2 = 0, 1y, 0
  let rec private augment n (interval2 : int array) depth live real baseCol on (major : Const.TpGConfMajor) =
    let on2 = if on then 1 else 0
    LibReduceUpdate.Checkreality(depth, weight, live, real, &nReal2, major.ring, baseCol, on2, &bit2, &realTerm2, major.nchar)
    let mutable newN = 0
    let newInterval = Array.replicate 10 0
    for r = 1 to n do
      let lower, upper = interval2.[2 * r - 1], interval2.[2 * r]
      for i = lower + 1 to upper do
        for j = lower to i - 1 do
          for h = 0 to 3 do weight.[depth + 1].[h] <- matchweight.[i].[j].[h]
          for h = 1 to 2 * r - 2 do newInterval.[h] <- interval2.[h]
          let mutable h = 2 * r - 1
          newN <- r - 1
          if j > lower + 1 then newN <- newN + 1; newInterval.[h] <- lower; h <- h + 1; newInterval.[h] <- j - 1; h <- h + 1;
          if i > j + 1     then newN <- newN + 1; newInterval.[h] <- j + 1; h <- h + 1; newInterval.[h] <- i - 1
          augment newN newInterval (depth + 1) live real baseCol on major |> ignore
    true
  let testMatch ((live, _) as twin, real, nReal, (major : Const.TpGConfMajor), ap, b1, b2) =
    // /* "nReal" will be the number of balanced signed matchings such that all associated colourings belong to "live",
    // * ie the total number of nonzero bits in the entries of "real" */
    let mutable n = 0
    nReal2    <- nReal
    bit2      <- 1y
    realTerm2 <- 0
    // /* First, it generates the matchings not incident with the last ring edge */
    for a = 2 to major.ring do
      for b = 1 to a - 1 do
        matchweight.[a].[b].[0] <- 2 * (Const.POWER.[a] + Const.POWER.[b]);
        matchweight.[a].[b].[1] <- 2 * (Const.POWER.[a] - Const.POWER.[b]);
        matchweight.[a].[b].[2] <-      Const.POWER.[a] + Const.POWER.[b];
        matchweight.[a].[b].[3] <-      Const.POWER.[a] - Const.POWER.[b];
    for a = 2 to major.ring - 1 do
      for b = 1 to a - 1 do
        n <- 0;
        for h = 0 to 3 do weight.[1].[h] <- matchweight.[a].[b].[h]
        if b >= 3     then n <- 1;     interval.[1] <- 1;             interval.[2]     <- b - 1
        if a >= b + 3 then n <- n + 1; interval.[2 * n - 1] <- b + 1; interval.[2 * n] <- a - 1
        augment n interval 1 live real 0 false major |> ignore
    // /* now, the matchings using an edge incident with "ring" */
    for a = 2 to major.ring do
      for b = 1 to a - 1 do
        matchweight.[a].[b].[0] <-  Const.POWER.[a] +     Const.POWER.[b];
        matchweight.[a].[b].[1] <-  Const.POWER.[a] -     Const.POWER.[b];
        matchweight.[a].[b].[2] <- -Const.POWER.[a] -     Const.POWER.[b];
        matchweight.[a].[b].[3] <- -Const.POWER.[a] - 2 * Const.POWER.[b];
    for b = 1 to major.ring - 1 do
      n <- 0;
      for h = 0 to 3 do weight.[1].[h] <- matchweight.[major.ring].[b].[h]
      if b >= 3              then n <- 1;     interval.[1] <- 1;             interval.[2]     <- b - 1
      if major.ring >= b + 3 then n <- n + 1; interval.[2 * n - 1] <- b + 1; interval.[2 * n] <- major.ring - 1
      augment n interval 1 live real ((Const.POWER.[major.ring + 1] - 1) / 2) true major |> ignore
    (twin, real, nReal2, major, ap, b1, b2)

  let updateLive (twin, real, nReal, (major : Const.TpGConfMajor), ap, _, _) =
    let isUpdate ncols ((live : int array), nLive) nReal =
      let mutable newnlive = 0
      let ret =
        if live.[0] > 1 then live.[0] <- 15
        for i = 0 to ncols - 1 do
          if live.[i] <> 15 then live.[i] <- 0
          else
            newnlive <- newnlive + 1; live.[i] <- 1;
        printf "               %d\n" nReal // right
        printf "            %9d" newnlive  // left
        if (newnlive < nLive) && (newnlive > 0) then 0
        else
          if 0 = newnlive then
            printf "\n\n\n                  ***  D-reducible  ***\n\n"
          else
            printf "\n\n\n                ***  Not D-reducible  ***\n"
          1
      (1 = ret, 0 = newnlive, (live, newnlive))
    let (b1, b2, twin2) = isUpdate (major.ncodes) twin nReal
    (twin2, real, 0, major, ap, b1, b2)


module CReduce =
  let run (major : Const.TpGConfMajor) ((live : int array), nLive) ((_, diffangle, sameangle, contract) : Const.TpAnglePack) =
    Debug.Assert((contract.[0] <> 0),              "       ***  ERROR: NO CONTRACT PROPOSED  ***\n\n")
    Debug.Assert((nLive = contract.[Const.EDGES]), "       ***  ERROR: DISCREPANCY IN EXTERIOR SIZE  ***\n\n")
    let mutable start = diffangle.[0].[2]
    let c         = Array.replicate Const.EDGES 0
    let forbidden = Array.replicate Const.EDGES 0 // called F in the notes
    while contract.[start] <> 0 do
      start <- start - 1
    c.[start] <- 1
    let mutable j = start - 1
    while contract.[j] <> 0 do
      j <- j - 1
    let dm, sm = diffangle.[j], sameangle.[j]
    c.[j] <- 1
    let mutable u = 4
    let imax1 = if dm.[0] >= 4 then 4 else dm.[0]
    for i in 1..imax1 do
      u <- u ||| c.[dm.[i]]
    let imax2 = if sm.[0] >= 4 then 4 else sm.[0]
    for i in 1..imax2 do
      u <- u ||| ~~~c.[sm.[i]]
    forbidden.[j] <- u
    LibReduceContract.CheckContractSub (forbidden, c, contract, j, start, diffangle, sameangle,
      major.bigno, major.ring, live, Const.POWER)
    ()


module Re =
  let rec private until p f (a: 'a) = if p a then a else until p f (f a)

  let private readFileGoodConfsR =
    File.ReadAllText "data/GoodConfs.txt"
    |> Const.TpConfFmt.Parse
  let private gConfs = readFileGoodConfsR

  let private makeGConfMajor (gConf: int array array) =
    let verts0, ring0 = gConf.[1].[0], gConf.[1].[1]
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

  let private makeLive ((major : Const.TpGConfMajor), ((an, _, _, _) as ap : Const.TpAnglePack)) =
    let real = Array.replicate (Const.SIMATCHNUMBER[Const.MAXRING] / 8 + 1) -1y
    (MLive.run an major, real, 0, major, ap, false, false): Const.TpLiveState

  let private chkDReduce : Const.TpLiveState -> Const.TpLiveState =
    let p (_, _, _, _, _, b1, _) = b1
    until p (DReduce.testMatch >> DReduce.updateLive)

  let private chkCReduce (twin, _, _, major, ap, _, b2) =
    if b2 then ()  // D可約 のときはスルー
    else       CReduce.run major twin ap
    b2

  let reduce =
    gConfs |> Array.take 12 |> Array.map (makeGConfMajor >> makeEdgeNo >> makeAngle >> makeLive >> chkDReduce >> chkCReduce)
    // let (liveTwin, _, _, _, _, b1, b2) = gConfs.[10] |> (makeGConfMajor >> makeEdgeNo >> makeAngle >> makeLive >> chkDReduce)
    // (b1, b2)



