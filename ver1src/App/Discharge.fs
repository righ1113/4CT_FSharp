namespace Discharge

open System
open System.Diagnostics
//open FSharpPlus.Lens
open LibraryFS
open LibraryCS2

module Di =

  let VERTS      = 27             // max number of vertices in a free completion + 1
  let CONFS      = 640            // max number of configurations
  let MAXVAL     = 12
  let CARTVERT   = 5 * MAXVAL + 2 // domain of l_A, u_A, where A is an axle
  let INFTY      = 12             // the "12" in the definition of limited part
  let MAXOUTLETS = 110            // max number of outlets
  let MAXSYM     = 50             // max number of symmetries
  let MAXELIST   = 134            // length of edgelist[a][b]
  let MAXSTACK   = 5              // max height of Astack (see "Reduce")
  let MAXLEV     = 12             // max level of an input line + 1
  let DIFNOUTS   = [0; 0; 0; 0; 0; 0; 0; 103; 103; 103; 103; 103]


  // 1.Symmetry
  // Assertに引っかからなければ良し
  let checkSymmetry (str : string array)
                    (axles : LibFS.TpAxle)
                    (sym : LibFS.TpPosout)
                    nosym =
    let k       = int (Int32.Parse str.[0])
    let epsilon = int (Int32.Parse str.[1])
    let level   = int (Int32.Parse str.[2])
    let line    = int (Int32.Parse str.[3])
    let i       = Array.findIndex (fun x -> x = line) sym.number

    //Debug.Assert((k >= 0 && k <= Array.head low.[lev] && epsilon >= 0 && epsilon <= 1),
    //  "Illegal symmetry")
    //Debug.Assert((i < nosym),
    //  "No symmetry as requested")
    //Debug.Assert((posout.nolines.[i] = level + 1),
    //  "Level mismatch")
    Debug.Assert((epsilon <> 0
      || LibDischargeSymmetry.OutletForced(axles.low.[axles.lev],
                                           axles.upp.[axles.lev],
                                           sym.number.[i],
                                           sym.nolines.[i],
                                           sym.value.[i],
                                           sym.pos.[i],
                                           sym.plow.[i],
                                           sym.pupp.[i],
                                           k+1) = 1),
      "Invalid symmetry")
    (*Debug.Assert((LibDischargeSymmetry.ReflForced(low.[lev],
                                                  upp.[lev],
                                                  posout.number.[i],
                                                  posout.nolines.[i],
                                                  posout.value.[i],
                                                  posout.pos.[i],
                                                  posout.plow.[i],
                                                  posout.pupp.[i],
                                                  k+1) = 1),
      "Invalid reflected symmetry")*)

    printfn "  checkSymmetry OK."
    ()


  // 2.Reduce
  let reduce (rP1   : byref<LibFS.TpReducePack1>)
             (rP2   : byref<LibFS.TpReducePack2>)
             (axles : LibFS.TpAxle)
               : LibFS.TpReduceRet =
    LibDischargeReduce.Reduce(&rP1, &rP2, axles)


  // 3.Hubcap
  let checkHubcap (posout : LibFS.TpPosout)
                  (tac    : string array)
                  (axles  : LibFS.TpAxle)
                  (deg    : int)
                  (rP1    : byref<LibFS.TpReducePack1>)
                  (rP2    : byref<LibFS.TpReducePack2>)
                    : LibFS.TpPosout =

    // 0.
    let xyv = (tac
      |> Array.map ((fun str -> str.Split [|','; '('; ')'|])
                    >> (Array.filter (not << String.IsNullOrEmpty))
                    >> (Array.map (Int32.Parse >> int)) ) )
    let x       = Array.replicate (MAXVAL + 2) 0
    let y       = Array.replicate (MAXVAL + 2) 0
    let v       = Array.replicate (MAXVAL + 2) 0
    let mutable cnt = 1
    for line in xyv do
      x.[cnt] <- line.[0]
      y.[cnt] <- line.[1]
      v.[cnt] <- line.[2]
      cnt     <- cnt + 1
    let covered = Array.replicate (MAXVAL + 2) 0
    let aux     = Array.replicate (MAXVAL + 2) 0
    let s = Array.replicate (2 * MAXOUTLETS + 1) 0
    let nouts = DIFNOUTS.[deg]

    // 1.
    x.[0] <- xyv.Length
    printfn "Testing hubcap for:"
    printfn "Forced positioned outlets:"
    for i in 1..deg do
      let mutable a = 0 // a=1 if edge number printed
      for j in 0..(nouts-1) do
        if LibDischargeSymmetry.OutletForced(axles.low.[axles.lev],
                                             axles.upp.[axles.lev],
                                             posout.number.[j],
                                             posout.nolines.[j],
                                             posout.value.[j],
                                             posout.pos.[j],
                                             posout.plow.[j],
                                             posout.pupp.[j],
                                             i) <> 0 then
          if a = 0 then
            printf "\nEdge %d: " i
            a <- 1
          printf "%d " posout.number.[j]
    printfn ""

    // 2.
    let mutable total = 0
    for i in 1..x.[0] do
      Debug.Assert((x.[i] >= 1 && x.[i] <= deg && y.[i] >= 1 && y.[i] <= deg),
        (sprintf "Invalid hubcap member (%d,%d,%d)" x.[i] y.[i] v.[i]))
      if x.[i] = y.[i] then
        total <- total + 2 * v.[i] // repeated hubcap members listed once
        Debug.Assert((covered.[x.[i]] = 0),
          "Invalid double cover")
        covered.[x.[i]] <- -1
      else
        aux.[x.[i]] <- v.[i]
        total <- total + v.[i]
        Debug.Assert((covered.[x.[i]] <> -1 && covered.[y.[i]] <> -1),
          "Invalid double cover")
        covered.[x.[i]] <- if covered.[x.[i]] = 0 then y.[i] else -1
        covered.[y.[i]] <- if covered.[y.[i]] = 0 then x.[i] else -1

    // 3.
    let rec loop1 i =
      if i <= deg then
        Debug.Assert((covered.[i] <> 0),
          "Invalid hubcap")
        if covered.[i] = -1 then
          loop1 (i + 1)
        else
          Debug.Assert((covered.[covered.[i]] = i),
            "Invalid hubcap")
          total <- total + aux.[i] // repeated hubcap members are only listed once
          loop1 (i + 1)
      else ()
    loop1 1

    // 4.
    printfn "Total double cover cost is %d" total
    Debug.Assert((total <= 20 * (deg - 6) + 1),
      "Hubcap does not satisfy (H2)")

    // 5.
    for i in 1..x.[0] do
      ignore <| printfn "\n-->Checking hubcap member (%d,%d,%d)" x.[i] y.[i] v.[i]
      ignore <| printf ""
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
      ignore <| LibDischargeHubcap.CheckBound(posout, s, v.[i], 0, 0, &rP1, &rP2, axles)
    printfn ""
    posout


  // 4.Condition
  let checkCondition2
        (nn : int array, mm : int array)
        deg
        (axles : LibFS.TpAxle)
        n
        m
        (sym : LibFS.TpPosout)
        nosym
        lineno =

    axles.low.[axles.lev+1] <- Array.copy axles.low.[axles.lev]
    axles.upp.[axles.lev+1] <- Array.copy axles.upp.[axles.lev]
    let aLowN = axles.low.[axles.lev].[n]
    let aUppN = axles.upp.[axles.lev].[n]

    if m > 0 then
      // new lower bound
      if aLowN >= m || m > aUppN then
        Debug.Assert(false, "Invalid lower bound in condition")
      else
        axles.upp.[axles.lev]    .[n] <- m - 1
        axles.low.[axles.lev + 1].[n] <- m
    else
      // new upper bound
      if aLowN > -m || -m >= aUppN then
        Debug.Assert(false, "Invalid upper bound in condition")
      else
        axles.low.[axles.lev]    .[n] <- 1 - m
        axles.upp.[axles.lev + 1].[n] <- -m

    // remember symmetry unless contains a fan vertex
    let mutable good = true
    for i in 0..axles.lev do
      if (nn.[i] > 2 * deg || nn.[i] < 1) then
      //if (1 <= nn.[i] && nn.[i] <= 2 * deg) then
        good <- false
    if good then // remember symmetry
      Debug.Assert((nosym < MAXSYM), "Too many symmetries")
      //T = &sym[nosym + 1];
      sym.number.[nosym] <- lineno
      sym.value.[nosym] <- 1
      sym.nolines.[nosym] <- axles.lev + 1
      for i in 0..axles.lev do
        sym.pos.[nosym].[i] <- nn.[i];
        if (mm.[i] > 0) then
          sym.plow.[nosym].[i] <- mm.[i]
          sym.pupp.[nosym].[i] <- INFTY
        else
          sym.plow.[nosym].[i] <- 5
          sym.pupp.[nosym].[i] <- -mm.[i]

    nn.[axles.lev]     <- n
    nn.[axles.lev + 1] <- 0
    mm.[axles.lev]     <- m
    mm.[axles.lev + 1] <- 0

    if good then
      ((nn, mm), (axles.low, axles.upp, axles.lev), nosym + 1)
    else
      ((nn, mm), (axles.low, axles.upp, axles.lev), nosym)


  // main routine
  let rec mainLoop (rP1 : byref<LibFS.TpReducePack1>)
                   (rP2 : byref<LibFS.TpReducePack2>)
                   posout
                   (nn, mm)
                   deg
                   (sym : LibFS.TpPosout)
                   (nosym : int)
                   (axles : LibFS.TpAxle)
                   tactics
                   lineno  =
    let nowTac = Array.head tactics
    match axles.lev with
      | lev when lev >= MAXLEV ->
          Debug.Assert(false, "More than %d levels")
          "error1"
      | lev when lev < 0       ->
          // 終了時
          Array.head nowTac
      | _                      ->
          match nowTac.[1] with
            | "S" ->
                printfn "Symmetry %A" nowTac
                checkSymmetry (Array.tail (Array.tail nowTac)) axles sym nosym
                let nosym2 =
                  if nosym = 0 then 0
                  else LibDischargeSymmetry.DelSym(nosym, sym.nolines, axles.lev)
                //止めておくmainLoop rP1 rP2 posout (nn, mm) deg sym nosym2 (low, upp, lev - 1) (Array.tail tactics) (lineno + 1)
                "Q.E.D"
            | "R" ->
                printfn "Reduce %A" nowTac
                let ret : LibFS.TpReduceRet = reduce &rP1 &rP2 axles
                if ret.retB then
                  let nosym2 =
                    if nosym = 0 then 0
                    else LibDischargeSymmetry.DelSym(nosym, sym.nolines, axles.lev)
                  mainLoop &rP1
                           &rP2
                           posout
                           (nn, mm)
                           deg
                           sym
                           nosym2
                           { axles with lev = axles.lev - 1; }
                           (Array.tail tactics)
                           (lineno + 1)
                else
                  Debug.Assert(false, "Reducibility failed")
                  "error3"
            | "H" ->
                printfn "Hubcap %A" nowTac
                let posout' = checkHubcap posout (Array.tail (Array.tail nowTac)) axles deg &rP1 &rP2
                let nosym2 =
                  if nosym = 0 then 0
                  else LibDischargeSymmetry.DelSym(nosym, sym.nolines, axles.lev)
                mainLoop &rP1
                         &rP2
                         posout'
                         (nn, mm)
                         deg
                         sym
                         nosym2
                         { axles with lev = axles.lev - 1; }
                         (Array.tail tactics)
                         (lineno + 1)
            | "C" ->
                printfn "Condition %A" nowTac
                let n = int (Int32.Parse nowTac.[2])
                let m = int (Int32.Parse nowTac.[3])
                let (cond2, (low2, upp2, _), nosym2) =
                      checkCondition2 (nn, mm) deg axles n m sym nosym lineno
                mainLoop &rP1 &rP2 posout cond2 deg sym nosym2 {low = low2; upp = upp2; lev = axles.lev + 1} (Array.tail tactics) (lineno + 1)
            | _   ->
                Debug.Assert(false, "Invalid instruction")
                "error2"


  let discharge =
    printfn "start Dischage.fs"

    let deg = 7

    // TpAxle
    let axles0    = Array.init MAXLEV (fun _ -> Array.zeroCreate CARTVERT)
    let axlesLow0 = Array.take CARTVERT (Array.concat [| [|deg|]; (Array.create (5*deg) 5);     (Array.replicate 1000 0) |])
    let axlesUpp0 = Array.take CARTVERT (Array.concat [| [|deg|]; (Array.create (5*deg) INFTY); (Array.replicate 1000 0) |])
    let axlesLow  = Array.append [|axlesLow0|] axles0
    let axlesUpp  = Array.append [|axlesUpp0|] axles0

    // TpCond
    let nn = Array.replicate MAXLEV 0
    let mm = Array.replicate MAXLEV 0

    // TpOutlet & TpPosout
    let rules = LibFS.readFileRulesD

    // sym
    let symNum = Array.zeroCreate (MAXSYM + 1)
    let symNol = Array.zeroCreate (MAXSYM + 1)
    let symVal = Array.zeroCreate (MAXSYM + 1)
    let symPos = Array.init (MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
    let symLow = Array.init (MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
    let symUpp = Array.init (MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
    let symXxx = Array.zeroCreate (MAXSYM + 1)
    let sym : LibFS.TpPosout = {number = symNum; nolines = symNol; value = symVal; pos = symPos; plow = symLow; pupp = symUpp; xx = symXxx}

    // TpReducePack
    let aSLow    = Array.init (MAXLEV + 1) (fun _ -> Array.zeroCreate CARTVERT)
    let aSUpp    = Array.init (MAXLEV + 1) (fun _ -> Array.zeroCreate CARTVERT)
    let bLow     = Array.replicate CARTVERT 0
    let bUpp     = Array.replicate CARTVERT 0
    let adjmat   = Array.init CARTVERT (fun _ -> Array.zeroCreate CARTVERT)
    let edgelist = Array.init 12 (fun _ -> Array.init 9 (fun _ -> Array.zeroCreate MAXELIST))
    let used     = Array.replicate CARTVERT false
    let image    = Array.replicate CARTVERT 0
    let qU       = Array.replicate VERTS 0
    let qV       = Array.replicate VERTS 0
    let qZ       = Array.replicate VERTS 0
    let qXi      = Array.replicate VERTS 0
    let graphs = LibFS.readFileGoodConfsD
    let axlepk : LibFS.TpAxle = {low = aSLow; upp = aSUpp; lev = 0;}
    let mutable redpk1 : LibFS.TpReducePack1 = {axle = axlepk; bLow = bLow; bUpp = bUpp; adjmat = {adj = adjmat};}
    let mutable redpk2 : LibFS.TpReducePack2 = {edgelist = {edg = edgelist}; used = used; image = {ver = image}; redquestions = graphs}

    // tactics
    let tactics = LibFS.readFileTacticsD

    let ret = mainLoop &redpk1
                       &redpk2
                       rules
                       (nn, mm)
                       deg
                       sym
                       0
                       {low = axlesLow; upp = axlesUpp; lev = 0}
                       (Array.tail tactics)
                       2

    // final check
    //if ret == "Q.E.D." then
    //  putStrLn $ "中心の次数" ++ degStr ++ "のグラフは、電荷が負になるか、近くに好配置があらわれるかです"
    //else
    //  putStr ""

    true



