namespace Reduce

open System
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
  type TpLiveTwin    = int * int array
  //type TpRingNchar     = (Int, Int)
  //type TpUpdateState   = (TpLiveTwin, [Int], Int, Int8, Int)
  type TpLiveState   = TpLiveTwin * int array * int * int8 * int * TpGConfMajor * TpAnglePack * bool

  type TpConfFmt     = JsonProvider<"[[[1]]]">


module EdgeNo =
  exception Continue
  exception Break
  exception Return of int
  let private inInterval (grav: int array) (don: bool array) =
    try
      let d = grav.[1] in
      let mutable first = 1 in
      while first < d && not don.[grav.[first + 1]] do first <- first + 1 done;
      if first = d then raise (Return (if don.[grav.[d + 1]] then 1 else 0));
      let mutable last = first in
      while last < d && don.[grav.[last + 2]] do last <- last + 1 done;
      let mutable length = last - first + 1 in
      if last  = d then raise (Return length);
      if first > 1 then
        begin
          for j = last + 2 to d do if don.[grav.[j + 1]] then raise (Return 0); done;
          raise (Return length)
        end;
      let mutable worried = false in
      for j = last + 2 to d do
        if don.[grav.[j + 1]] then begin length <- length + 1; worried <- true end
        else if worried then raise (Return 0);
      done;
      length;
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
            begin maxint <- inter; maxes <- 1; max.[1] <- v end
          else
            if inter = maxint then begin maxes <- maxes + 1; max.[maxes] <- v end
        with
        | Continue -> ()
      done;
      let mutable maxdeg = 0
      (* 2_2. *)
      for h = 1 to maxes do
        let d = gConf.[max.[h] + 2].[1] in
        if d > maxdeg then begin maxdeg <- d; best <- max.[h] end
      done;
      let grav = gConf.[best + 2] in
      let d = grav.[1]
      let mutable first = 1
      let mutable previous = done0.[grav.[d + 1]]
      (* 2_3. *)
      begin
        try
          while previous || not done0.[grav.[first + 1]] do
            previous <- done0.[grav.[first + 1]]
            first    <- first + 1;
            if first > d then begin first <- 1; raise Break; end
          done
        with
        | Break -> ()
      end;
      let mutable h = first
      (* 2_4. *)
      begin
        try
          while done0.[grav.[h + 1]] do
            edgeNo.[best].[grav.[h+1]] <- term
            edgeNo.[grav.[h+1]].[best] <- term
            term <- term - 1
            if h = d then
              begin
                if first = 1 then raise Break;
                h <- 0
              end;
            h <- h + 1
          done;
        with
        | Break -> ()
      end;
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
          if inter > maxint then begin maxint <- inter; best <- v end
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
                if u = gConf.[2].[j] then begin a <- a + 1; raise Break end
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
    // let edge                = major.edges
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



module DReduce =
  let testMatch  = id
  let updateLive = id


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

  let private makeLive (major, ap) =
    ((0, [|5|]), [|3|], 0, 8y, 0, major, ap, true): Const.TpLiveState

  let private chkDReduce: Const.TpLiveState -> Const.TpLiveState =
    let p (_, _, _, _, _, _, _, b) = b
    until p (DReduce.testMatch >> DReduce.updateLive)

  let private chkCReduce _ = true

  let reduce =
    // gConfs |> Array.forall (makeGConfMajor >> makeEdgeNo >> makeAngle >> makeLive >> chkDReduce >> chkCReduce)
    let (_, (_, _, a, b, c, d)) = gConfs.[0] |> (makeGConfMajor >> makeEdgeNo >> makeAngle)
    (a, b, c, d)



