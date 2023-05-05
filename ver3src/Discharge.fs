namespace Discharge

open System
open System.IO
open System.Diagnostics
open FSharp.Data
open LibraryCS2


module Const =
  let VERTS        = 27             // max number of vertices in a free completion + 1
  let CONFS        = 640            // max number of configurations
  let MAXVAL       = 12
  let CARTVERT     = 5 * MAXVAL + 2 // domain of l_A, u_A, where A is an axle
  let INFTY        = 12             // the "12" in the definition of limited part
  let MAXOUTLETS   = 110            // max number of outlets
  let MAXSYM       = 50             // max number of symmetries
  let MAXELIST     = 134            // length of edgelist[a][b]
  let MAXSTACK     = 5              // max height of Astack (see "Reduce")
  let MAXLEV       = 12             // max level of an input line + 1
  let DIFNOUTS     = [0; 0; 0; 0; 0; 0; 0; 103; 64; 53; 53; 53]
  type TpAxle      = {low: int array array; upp: int array array; lev: int}
  type TpPosout    = {number: int array; nolines: int array; value: int array; pos: int array array; plow: int array array; pupp: int array array; xx: int array}
  type TpDiRules   = JsonProvider<"""{"a":[0], "b":[0], "c":[8], "d":[[6]], "e":[[6]], "f":[[6]], "g":[6]}""">
  type TpDiRules2  = JsonProvider<"""[{"b":[0], "z":[0], "c":"comment"}]""">
  type TpDiConfs   = JsonProvider<"""[{"a":[0], "b":[0], "c":[8], "d":[6]}]""">
  type TpRules2Ret = {B: int array; Z: int array; Comment: string}
  type TpAdjmat      = {adj: int array array}
  type TpEdgelist    = {edg: int array array array}
  type TpVertices    = {ver: int array}
  type TpQuestion    = {qa: int array; qb: int array; qc: int array; qd: int array}
  type TpReducePack1 = {axle: TpAxle; bLow: int array; bUpp: int array; adjmat: TpAdjmat}
  type TpReducePack2 = {edgelist: TpEdgelist; used: bool array; image: TpVertices; redquestions: TpQuestion array}


module CaseSplit =
  // TpCond
  let private nn = Array.replicate Const.MAXLEV 0
  let private mm = Array.replicate Const.MAXLEV 0
  // sym
  let private symNum = Array.zeroCreate (Const.MAXSYM + 1)
  let private symNol = Array.zeroCreate (Const.MAXSYM + 1)
  let private symVal = Array.zeroCreate (Const.MAXSYM + 1)
  let private symPos = Array.init       (Const.MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
  let private symLow = Array.init       (Const.MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
  let private symUpp = Array.init       (Const.MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
  let private symXxx = Array.zeroCreate (Const.MAXSYM + 1)
  let sym : Const.TpPosout = {number = symNum; nolines = symNol; value = symVal; pos = symPos; plow = symLow; pupp = symUpp; xx = symXxx}
  let mutable nosym: int = 0
  let run deg (ax : Const.TpAxle) n m lineCnt =
    ax.low.[ax.lev+1] <- Array.copy ax.low.[ax.lev]
    ax.upp.[ax.lev+1] <- Array.copy ax.upp.[ax.lev]
    let aLowN = ax.low.[ax.lev].[n]
    let aUppN = ax.upp.[ax.lev].[n]
    if m > 0 then
      // new lower bound
      if aLowN >= m || m > aUppN then
        Debug.Assert(false, "Invalid lower bound in condition")
      else
        ax.upp.[ax.lev]    .[n] <- m - 1
        ax.low.[ax.lev + 1].[n] <- m
    else
      // new upper bound
      if aLowN > -m || -m >= aUppN then
        Debug.Assert(false, "Invalid upper bound in condition")
      else
        ax.low.[ax.lev]    .[n] <- 1 - m
        ax.upp.[ax.lev + 1].[n] <- -m
    // remember symmetry unless contains a fan vertex
    let mutable good = true
    for i in 0..ax.lev do
      if (nn.[i] > 2 * deg || nn.[i] < 1) then good <- false
    if good then // remember symmetry
      Debug.Assert((nosym < Const.MAXSYM), "Too many symmetries")
      sym.number.[nosym] <- lineCnt
      sym.value.[nosym] <- 1
      sym.nolines.[nosym] <- ax.lev + 1
      for i: int32 in 0..ax.lev do
        sym.pos.[nosym].[i] <- nn.[i]
        if (mm.[i] > 0) then
          sym.plow.[nosym].[i] <- mm.[i]
          sym.pupp.[nosym].[i] <- Const.INFTY
        else
          sym.plow.[nosym].[i] <- 5
          sym.pupp.[nosym].[i] <- -mm.[i]
    nn.[ax.lev]     <- n
    nn.[ax.lev + 1] <- 0
    mm.[ax.lev]     <- m
    mm.[ax.lev + 1] <- 0
    if good then nosym <- nosym + 1
    {ax with lev = ax.lev + 1}

  let rec downNosym lev =
    if nosym < 1 || sym.nolines.[nosym - 1] - 1 < lev then
      printfn "  nosym: %d" nosym; ()
    else
      nosym <- nosym - 1; downNosym lev


module Apply =
  exception Return of int
  let outletForced deg (ax : Const.TpAxle) (sym : Const.TpPosout) ii xx =
    try
      let x = xx - 1
      for i = 0 to sym.nolines.[ii] - 1 do
        let mutable p = sym.pos.[ii].[i];
        p <- if x + (p - 1) % deg < deg then p + x else p + x - deg
        if sym.plow.[ii].[i] > ax.low.[ax.lev].[p] || sym.pupp.[ii].[i] < ax.upp.[ax.lev].[p] then raise (Return 0)
      sym.value.[ii]
    with
    | Return x -> x
  let outletPermitted deg (ax : Const.TpAxle) (sym : Const.TpPosout) ii xx =
    try
      let x = xx - 1
      for i = 0 to sym.nolines.[ii] - 1 do
        let mutable p = sym.pos.[ii].[i];
        p <- if x + (p - 1) % deg < deg then p + x else p + x - deg
        if sym.plow.[ii].[i] > ax.upp.[ax.lev].[p] || sym.pupp.[ii].[i] < ax.low.[ax.lev].[p] then raise (Return 0)
      sym.value.[ii]
    with
    | Return x -> x
  let reflForced deg (ax : Const.TpAxle) (sym : Const.TpPosout) ii xx =
    try
      let x = xx - 1
      for i = 0 to sym.nolines.[ii] - 1 do
        let mutable q = 0
        let mutable p = sym.pos.[ii].[i];
        p <- if x + (p - 1) % deg < deg then p + x else p + x - deg
        if p < 1 || p > 2 * deg then raise (Return 0)
        elif p <= deg           then q <- deg - p + 1
        elif p < 2 * deg        then q <- 3 * deg - p
        else                         q <- 2 * deg
        if sym.plow.[ii].[i] > ax.low.[ax.lev].[q] || sym.pupp.[ii].[i] < ax.upp.[ax.lev].[q] then raise (Return 0)
      sym.value.[ii]
    with
    | Return x -> x
  let run deg (ax : Const.TpAxle) (strL : string list) (sym : Const.TpPosout) nosym =
    let k       = int (Int32.Parse strL.[0])
    let epsilon = int (Int32.Parse strL.[1])
    let level   = int (Int32.Parse strL.[2])
    let line    = int (Int32.Parse strL.[3])
    let i       = Array.findIndex (fun (x: int) -> x = line) sym.number
    Debug.Assert((k >= 0 &&
                  k <= Array.head ax.low.[ax.lev] &&
                  epsilon >= 0 &&
                  epsilon <= 1),                "Illegal symmetry")
    Debug.Assert((i < nosym),                   "No symmetry as requested")
    Debug.Assert((sym.nolines.[i] = level + 1), "Level mismatch")
    if epsilon = 0 then
      Debug.Assert((0 <> outletForced deg ax sym i (k+1)), "Invalid symmetry")
    else
      Debug.Assert((0 <> reflForced deg ax sym i (k+1)),   "Invalid reflected symmetry")
    printfn "  checkSymmetry OK."
    ()


module Adjmat =
  type Way = Forward | Backward
  let adjmat = Array.init (Const.CARTVERT) (fun _ -> Array.zeroCreate Const.CARTVERT)
  let chgAdjmat a b c way =
    adjmat.[a].[b] <- c
    if way = Forward then
      adjmat.[c].[a] <- b
      adjmat.[b].[c] <- a
    else
      adjmat.[b].[c] <- a
      adjmat.[c].[a] <- b
  let doFan deg i k =
    let a = if i = 1 then 2 * deg else deg + i - 1
    let b = deg + i
    let c = 2 * deg + i
    let d = 3 * deg + i
    let e = 4 * deg + i
    match k with
    | 5 ->  chgAdjmat i a b Backward
    | 6 ->  chgAdjmat i a c Backward
            chgAdjmat i c b Backward
    | 7 ->  chgAdjmat i a c Backward
            chgAdjmat i c d Backward
            chgAdjmat i d b Backward
    | _ ->  chgAdjmat i a c Backward
            chgAdjmat i c d Backward
            chgAdjmat i d e Backward
            chgAdjmat i e b Backward
  let resetAdjmat deg (ax : Const.TpAxle) =
    for a = 0 to Const.CARTVERT - 1 do
      for b = 0 to Const.CARTVERT - 1 do
        adjmat.[a].[b] <- -1
    for i = 1 to deg do
      let h = if i = 1 then deg else i - 1
      chgAdjmat 0 h i Forward
      let a = deg + h
      chgAdjmat i h a Forward
      if ax.upp.[ax.lev].[i] < 9 then doFan deg i ax.upp.[ax.lev].[i]


module Rules =
  exception Continue
  exception Return of int
  let private symNum = Array.zeroCreate (Const.MAXOUTLETS * 2)
  let private symNol = Array.zeroCreate (Const.MAXOUTLETS * 2)
  let private symVal = Array.zeroCreate (Const.MAXOUTLETS * 2)
  let private symPos = Array.init       (Const.MAXOUTLETS * 2) (fun _ -> Array.zeroCreate 17)
  let private symLow = Array.init       (Const.MAXOUTLETS * 2) (fun _ -> Array.zeroCreate 17)
  let private symUpp = Array.init       (Const.MAXOUTLETS * 2) (fun _ -> Array.zeroCreate 17)
  let private symXxx = Array.zeroCreate (Const.MAXOUTLETS * 2)
  let private posout : Const.TpPosout = {number = symNum; nolines = symNol; value = symVal; pos = symPos; plow = symLow; pupp = symUpp; xx = symXxx}
  let doOutlet deg axles number (zzz : int array) (bbb : int array) index (xxx : int array) (yyy : int array) =
    Adjmat.resetAdjmat deg axles
    posout.nolines.[index] <- zzz.[0] - 1
    posout.number.[index]  <- number
    let phi = Array.replicate 17 (-1)
    let mutable k = 0
    phi.[0]              <- if number > 0 then 1 else 0
    phi.[1]              <- if number > 0 then 0 else 1
    posout.value.[index] <- if number > 0 then 1 else -1
    k                    <- if number > 0 then 1 else 0
    posout.pos.[index].[0] <- 1
    try
      // # compute phi
      let mutable i = 0
      for j = 0 to zzz.[0] - 1 do
        try
          posout.plow.[index].[i] <- bbb.[j] / 10
          posout.pupp.[index].[i] <- bbb.[j] % 10
          if posout.pupp.[index].[i] = 9 then posout.pupp.[index].[i] <- Const.INFTY
          if posout.plow.[index].[i] = 0 then posout.plow.[index].[i] <- posout.pupp.[index].[i]
          if j = k then
            if not (posout.plow.[index].[i] <= deg && deg <= posout.pupp.[index].[i]) then raise (Return 0)
            // # if above true then outlet cannot apply for this degree
            raise Continue
          let mutable u = 0
          if j >= 2 then // # now computing T->pos[i]
            u <- phi.[xxx.[zzz.[j]]]
            let v = phi.[yyy.[zzz.[j]]]
            posout.pos.[index].[i] <- Adjmat.adjmat.[u].[v]
            phi.[zzz.[j]]          <- Adjmat.adjmat.[u].[v]
          u <- posout.pos.[index].[i]
          // # update adjmat
          if u <= deg && posout.plow.[index].[i] = posout.pupp.[index].[i] then Adjmat.doFan deg u posout.plow.[index].[i]
          i <- i + 1
        with
        | Continue -> ()
      // # Condition (T4) is checked in CheckIso
      1
    with
    | Return x -> x
  let readFileRulesD2 =
    let mutable out = [||]
    let ind = Const.TpDiRules2.Parse <| File.ReadAllText "data/DiRules.txt"
    for indLine in ind do
      let ret = {B = indLine.B; Z = indLine.Z; Comment = indLine.C} : Const.TpRules2Ret
      out <- Array.append out [|ret|]
    out
  let initPosout deg axles =
    let u = [|0; 0; 0; 1; 0; 3; 2; 1; 4; 3; 8; 3; 0; 0; 5; 6; 15|]
    let v = [|0; 0; 1; 0; 2; 0; 1; 3; 2; 5; 2; 9; 4; 12; 0; 1; 1|]
    let rules = readFileRulesD2
    // # p rules[10]['z']
    // # set data
    let mutable index = 0
    for line in rules do
      if line.Comment = "invert" then
        if 0 <> doOutlet deg axles  line.Z.[1] line.Z line.B index v u then index <- index + 1
        if 0 <> doOutlet deg axles -line.Z.[1] line.Z line.B index v u then index <- index + 1
      else
        if 0 <> doOutlet deg axles  line.Z.[1] line.Z line.B index u v then index <- index + 1
        if 0 <> doOutlet deg axles -line.Z.[1] line.Z line.B index u v then index <- index + 1
    // # データを2回重ねる
    for i = 0 to index - 1 do
      posout.number.[i + index]  <- posout.number.[i]
      posout.nolines.[i + index] <- posout.nolines.[i]
      posout.value.[i + index]   <- posout.value.[i]
      posout.pos.[i + index]     <- Array.copy posout.pos.[i]
      posout.plow.[i + index]    <- Array.copy posout.plow.[i]
      posout.pupp.[i + index]    <- Array.copy posout.pupp.[i]
      posout.xx.[i + index]      <- posout.xx.[i]
    posout


module Dischg =
  exception Continue
  exception Return of int
  // let private readFileRulesD =
  //   let ind = Const.TpDiRules.Parse <| File.ReadAllText "data/DiRules07.txt"
  //   {number = ind.A; nolines = ind.B; value = ind.C; pos = ind.D; plow = ind.E; pupp = ind.F; xx = ind.G} : Const.TpPosout
  let mutable private posout =
    {number = null; nolines = null; value = null; pos = null; plow = null; pupp = null; xx = null} : Const.TpPosout
  let mutable private initEnd = false
  let rec private dischgCoreSub5 deg (ax : Const.TpAxle) forcedch allowedch (s : int array) maxch pos0 depth =
    try
      let mutable pos = pos0
      let mutable allowedch2 = allowedch
      while s.[pos] < 99 do
        try
          if s.[pos] <> 0 || posout.value.[pos] < 0 then pos <- pos + 1; raise Continue
          // /* accepting positioned outlet PO, computing AA */
          let x = posout.xx.[pos]
          let axlesLow = Array.init (Const.MAXLEV + 1) (fun _ -> Array.zeroCreate Const.CARTVERT)
          let axlesUpp = Array.init (Const.MAXLEV + 1) (fun _ -> Array.zeroCreate Const.CARTVERT)
          let ax2 = {low = axlesLow; upp = axlesUpp; lev = ax.lev} : Const.TpAxle
          ax2.low.[ax2.lev] <- Array.copy ax.low.[ax.lev]
          ax2.upp.[ax2.lev] <- Array.copy ax.upp.[ax.lev]
          for i = 0 to posout.nolines.[pos] - 1 do
            let mutable p = posout.pos.[pos].[i]
            p <- if x - 1 + (p - 1) % deg < deg then p + x - 1 else p + x - 1 - deg
            if (posout.plow.[pos].[i] > ax2.low.[ax2.lev].[p]) then ax2.low.[ax2.lev].[p] <- posout.plow.[pos].[i]
            if (posout.pupp.[pos].[i] < ax2.upp.[ax2.lev].[p]) then ax2.upp.[ax2.lev].[p] <- posout.pupp.[pos].[i]
            Debug.Assert((ax2.low.[ax2.lev].[p] <= ax2.upp.[ax2.lev].[p]), "Unexpected error 321")
          // /* Check if a previously rejected positioned outlet is forced to apply */
          let mutable good = true
          for i = 0 to pos - 1 do
            if s.[i] = -1 && 0 <> Apply.outletForced deg ax2 posout i posout.xx.[i] then good <- false
          if good then
            // recursion with PO forced
            let mutable sPrime = Array.replicate (Array.length s) 0
            sPrime <- Array.copy s
            sPrime.[pos] <- 1
            dischgCore deg ax2 sPrime maxch (pos + 1) (depth + 1)
          // rejecting positioned outlet PO
          s[pos] <- -1
          allowedch2 <- allowedch2 - posout.value.[pos]
          if allowedch2 + forcedch <= maxch then
            raise (Return 1) // ★★★ ここから脱出するしかない
          pos <- pos + 1
        with
        | Continue -> ()
      0
    with
    | Return x -> x
  and private dischgCore deg (ax: Const.TpAxle) (s : int array) maxch pos depth =
    // 1. compute forced and permitted rules, allowedch, forcedch, update s
    let mutable forcedch = 0
    let mutable allowedch = 0
    let mutable i = 0
    while s.[i] < 99 do
      try
        if   s.[i] > 0           then forcedch <- forcedch + posout.value.[i]
        if   s.[i] <> 0          then i <- i + 1; raise Continue
        if   0 <> Apply.outletForced    deg ax posout i posout.xx.[i] then s.[i] <-  1; forcedch <- forcedch + posout.value.[i]
        elif 0 =  Apply.outletPermitted deg ax posout i posout.xx.[i] then s.[i] <- -1
        elif posout.value.[i] > 0 then allowedch <- allowedch + posout.value.[i]
        i <- i + 1
      with
      | Continue -> ()
    // 2. print omitted
    // liftIO $ printf "%d POs: " depth
    // liftIO $ dischargeCoreSub2 0 s rules posoutX
    // 3. check if inequality holds
    if forcedch + allowedch <= maxch then
      printfn "1 %d Inequality holds. Case done." depth
      () // true end 1
    elif forcedch > maxch then // 4. check reducibility
      let ax1_2 = LibDischargeReduce.TpAxle(low = ax.low, upp = ax.upp, lev = ax.lev)
      let ret   = LibDischargeReduce.Reduce(ax1_2)
      printfn "2 %d reduce done. %b" depth ret.retB
      () // true end 2
    elif 0 <> dischgCoreSub5 deg ax forcedch allowedch s maxch pos depth then // 5.
      printfn "3 %d dischgCoreSub5() done." depth
      () // true end 3
    else
      // 6. error
      Debug.Assert(false, "Unexpected error 101")

  let run deg (ax : Const.TpAxle) strL =
    // init
    if initEnd = false then
      posout  <- Rules.initPosout deg ax
      initEnd <- true
    // 0.
    let xyv =
      strL |> List.map ( (fun (str: string) -> str.Split [|','; '('; ')'|])
                          >> (Array.filter (not << String.IsNullOrEmpty))
                          >> (Array.map (Int32.Parse >> int)) )
    let x       = Array.replicate (Const.MAXVAL + 2) 0
    let y       = Array.replicate (Const.MAXVAL + 2) 0
    let v       = Array.replicate (Const.MAXVAL + 2) 0
    let mutable cnt = 1
    for line: int array in xyv do
      x.[cnt] <- line.[0]
      y.[cnt] <- line.[1]
      v.[cnt] <- line.[2]
      cnt     <- cnt + 1
    let covered = Array.replicate (Const.MAXVAL + 2) 0
    let aux     = Array.replicate (Const.MAXVAL + 2) 0
    let s       = Array.replicate (2 * Const.MAXOUTLETS + 1) 0
    let nouts   = Const.DIFNOUTS.[deg]
    // 1. omitted
    x.[0] <- xyv.Length
    // 2. omitted
    // 3. omitted
    // 4. omitted
    // 5.
    for i in 1..x.[0] do
      printfn "-->Checking hubcap member (%d,%d,%d)" x.[i] y.[i] v.[i]
      printf ""
      for j in 0..(nouts-1) do
        posout.xx.[j] <- x.[i]
        s.[j] <- 0
      if x.[i] <> y.[i] then
        for j in nouts..(2 * nouts - 1) do
          posout.xx.[j] <- y.[i]
          s.[j] <- 0
        s.[2 * nouts] <- 99 // to indicate end of list
      else
        s.[nouts] <- 99 // to indicate end of list
      dischgCore deg ax s v.[i] 0 0
    ()


module Di =
  let rec private until p f (a: 'a) = if p a then a else until p f (f a)
  let private makeDisData deg =
    let tacName = [""; ""; ""; ""; ""; ""; ""; "data/DiTactics07.txt";
      "data/DiTactics08.txt"; "data/DiTactics09.txt"; "data/DiTactics10.txt"; "data/DiTactics11.txt"]
    let readFileTacticsD =
      File.ReadAllLines tacName.[deg]
        |> Array.toList
        |> List.map ((fun str -> str.Split " ")
                      >> Array.toList
                      >> (List.filter (not << String.IsNullOrEmpty)))
    let readFileGoodConfsD =
      let mutable out = [||]
      let ind = Const.TpDiConfs.Parse <| File.ReadAllText "data/DiGoodConfs.txt"
      for indLine in ind do
        let ret = LibDischargeReduce.TpQuestion(qa = indLine.A, qb = indLine.B, qc = indLine.C, qd = indLine.D)
        //let ret = [|{qa = indLine.A; qb = indLine.B; qc = indLine.C; qd = indLine.D}|] : LibDischargeReduce.TpQuestion array
        out <- Array.append out [|ret|]
      out
    //let tac2: string list list = [["Degree"; "7"]; ["L0"; "C"; "1"; "-5"]; ["Q.E.D."]]
    // TpAxle
    let axles0    = Array.init Const.MAXLEV (fun _ -> Array.zeroCreate Const.CARTVERT)
    let axlesLow0 = Array.take Const.CARTVERT (Array.concat [| [|deg|]; (Array.create (5*deg) 5);           (Array.replicate 1000 0) |])
    let axlesUpp0 = Array.take Const.CARTVERT (Array.concat [| [|deg|]; (Array.create (5*deg) Const.INFTY); (Array.replicate 1000 0) |])
    let axlesLow  = Array.append [|axlesLow0|] axles0
    let axlesUpp  = Array.append [|axlesUpp0|] axles0
    let axles = {low = axlesLow; upp = axlesUpp; lev = 0} : Const.TpAxle
    // TpReducePack
    let aSLow    = Array.init (Const.MAXLEV + 1) (fun _ -> Array.zeroCreate Const.CARTVERT)
    let aSUpp    = Array.init (Const.MAXLEV + 1) (fun _ -> Array.zeroCreate Const.CARTVERT)
    let bLow     = Array.replicate Const.CARTVERT 0
    let bUpp     = Array.replicate Const.CARTVERT 0
    let adjmat   = Array.init Const.CARTVERT (fun _ -> Array.zeroCreate Const.CARTVERT)
    let edgelist = Array.init 12 (fun _ -> Array.init 9 (fun _ -> Array.zeroCreate Const.MAXELIST))
    let used     = Array.replicate Const.CARTVERT false
    let image    = Array.replicate Const.CARTVERT 0
    //let qU       = Array.replicate Const.VERTS 0
    //let qV       = Array.replicate Const.VERTS 0
    //let qZ       = Array.replicate Const.VERTS 0
    //let qXi      = Array.replicate Const.VERTS 0
    let graphs = readFileGoodConfsD
    let axlepk = LibDischargeReduce.TpAxle(low = aSLow, upp = aSUpp, lev = 0)
    let mutable redpk1 = LibDischargeReduce.TpReducePack1(axle = axlepk, bLow = bLow, bUpp = bUpp, adjmat = LibDischargeReduce.TpAdjmat(adj = adjmat))
    let mutable redpk2 = LibDischargeReduce.TpReducePack2(
      edgelist = LibDischargeReduce.TpEdgelist(edg = edgelist),
      used = used,
      image = LibDischargeReduce.TpVertices(ver = image),
      redquestions = graphs)
    LibDischargeReduce.ReduceInit(redpk1, redpk2)
    (deg, axles, List.tail readFileTacticsD, 2)

  let private caseSplit x =
    match x with
    | (deg, (ax : Const.TpAxle), (_ :: "C" :: nStr :: mStr :: _) :: tailTac, lineCnt) ->
        let n = int (Int32.Parse nStr) in let m = int (Int32.Parse mStr) in let ret = CaseSplit.run deg ax n m lineCnt
        (deg, ret, tailTac, lineCnt + 1)
    | _ -> x
  let private apply x =
    match x with
    | (deg, (ax : Const.TpAxle), (_ :: "S" :: strL) :: tailTac, lineCnt) ->
        Apply.run deg ax strL CaseSplit.sym CaseSplit.nosym; CaseSplit.downNosym ax.lev
        (deg, {ax with lev = ax.lev - 1}, tailTac, lineCnt + 1)
    | _ -> x
  let private dischg x =
    match x with
    | (deg, (ax : Const.TpAxle), (_ :: "H" :: strL) :: tailTac, lineCnt) ->
        Dischg.run deg ax strL; CaseSplit.downNosym ax.lev
        (deg, {ax with lev = ax.lev - 1}, tailTac, lineCnt + 1)
    | _ -> x
  let private disReduce x =
    match x with
    | (deg, (ax : Const.TpAxle), (_ :: "R" :: _) :: tailTac, lineCnt) ->
        let ax1_2 = LibDischargeReduce.TpAxle(low = ax.low, upp = ax.upp, lev = ax.lev)
        let ret   = LibDischargeReduce.Reduce(ax1_2)
        printfn "rRet: %b" ret.retB
        // CaseSplit.downNosym ax.lev
        //let ax2  : Const.TpAxle = {low = ax.low; upp = ax.upp; lev = ax.lev - 1}
        // let ax3  : Const.TpAxle = {low = rp1.axle.low; upp = rp1.axle.upp; lev = rp1.axle.lev}
        // let rp12 : Const.TpReducePack1 = {axle = ax3; bLow = rp1.bLow; bUpp = rp1.bUpp; adjmat = {adj = rp1.adjmat.adj}}
        // let mutable out = [||]
        // for indLine in rp2.redquestions do
        //   let ret = [|{qa = indLine.qa; qb = indLine.qb; qc = indLine.qc; qd = indLine.qd}|] : Const.TpQuestion array
        //   out <- Array.append out ret
        // let rp22 : Const.TpReducePack2 = {edgelist = {edg = rp2.edgelist.edg}; used = rp2.used; image = {ver = rp2.image.ver}; redquestions = out}
        (deg, {ax with lev = ax.lev - 1}, tailTac, lineCnt + 1)
    | _ -> x

  let discharge deg =
    let isEnd x =
      match x with
      | (_, {low=_; upp=_; lev=(-1)} : Const.TpAxle, ("Q.E.D." :: _) :: _, _) -> true
      | _                                                                     -> false
    makeDisData deg |> until isEnd (caseSplit >> apply >> dischg >> disReduce) |> printfn "%A"
    true



