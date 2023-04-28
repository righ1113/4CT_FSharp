namespace Discharge

open System
open System.IO
open System.Diagnostics
open FSharp.Data


module Const =
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
  let DIFNOUTS   = [0; 0; 0; 0; 0; 0; 0; 103; 64; 53; 53; 53]
  type TpAxle   = {low: int array array; upp: int array array; lev: int}
  type TpPosout = {number: int array; nolines: int array; value: int array; pos: int array array; plow: int array array; pupp: int array array; xx: int array}
  type TpDiRules  = JsonProvider<"""{"a":[0], "b":[0], "c":[8], "d":[[6]], "e":[[6]], "f":[[6]], "g":[6]}""">


module Apply =
  let outletForced _ _ _ _ _ _ _ _ _ = 1
  let reflForced   _ _ _ _ _ _ _ _ _ = 1
  let run (strL : string list)
          (ax : Const.TpAxle)
          (sym : Const.TpPosout)
          (nosym: int) =
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
      Debug.Assert((outletForced ax.low.[ax.lev] ax.upp.[ax.lev] sym.number.[i] sym.nolines.[i] sym.value.[i] sym.pos.[i] sym.plow.[i] sym.pupp.[i] (k+1) = 1),
        "Invalid symmetry")
    else
      Debug.Assert((reflForced ax.low.[ax.lev] ax.upp.[ax.lev] sym.number.[i] sym.nolines.[i] sym.value.[i] sym.pos.[i] sym.plow.[i] sym.pupp.[i] (k+1) = 1),
        "Invalid reflected symmetry")
    printfn "  checkSymmetry OK."
    ()


module CaseSplit =
  // TpCond
  let nn = Array.replicate Const.MAXLEV 0
  let mm = Array.replicate Const.MAXLEV 0
  // sym
  let symNum = Array.zeroCreate (Const.MAXSYM + 1)
  let symNol = Array.zeroCreate (Const.MAXSYM + 1)
  let symVal = Array.zeroCreate (Const.MAXSYM + 1)
  let symPos = Array.init (Const.MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
  let symLow = Array.init (Const.MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
  let symUpp = Array.init (Const.MAXSYM + 1) (fun _ -> Array.zeroCreate 17)
  let symXxx = Array.zeroCreate (Const.MAXSYM + 1)
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
      //T = &sym[nosym + 1];
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


module Dischg =
  let private readFileRulesD =
    let ind = Const.TpDiRules.Parse <| File.ReadAllText "data/DiRules07.txt"
    {number = ind.A; nolines = ind.B; value = ind.C; pos = ind.D; plow = ind.E; pupp = ind.F; xx = ind.G} : Const.TpPosout
  let posout = readFileRulesD
  let private dischgCoreSub1 _ _ _ (forcedch: int) (allowedch: int) s0 =
    (forcedch, allowedch, s0)
  let rec private dischgCoreSub5 _ _ _ _ _ _ _ _ = true
  and private dischgCore (deg: int) (ax: Const.TpAxle) s0 (maxch: int) (pos: int) (depth: int) =
    // 1. compute forced and permitted rules, allowedch, forcedch, update s
    let (forcedch, allowedch, s) = dischgCoreSub1 deg (ax.low.[ax.lev], ax.upp.[ax.lev]) 0 0 0 s0
    //liftIO $ printf "f, a = %d, %d\n" forcedch allowedch
    // 2. print omitted
    // liftIO $ printf "%d POs: " depth
    // liftIO $ dischargeCoreSub2 0 s rules posoutX
    // 3. check if inequality holds
    if forcedch + allowedch <= maxch then
      printfn "%d Inequality holds. Case done." depth
      () // true end
    else if forcedch > maxch then // 4. check reducibility
      // lift $ put (((aSLow & ix 0 .~ axLowL, aSUpp & ix 0 .~ axUppL, aSLev), used, image, adjmat, edgelist), posoutX)
      // ret <- (lift . runMaybeT . reduce) 1
      // if isNothing ret then
      //   error "Incorrect hubcap upper bound"
      // else do
      //   liftIO $ printf "%d, %d, %d Reducible. Case done.\n" forcedch allowedch maxch
      //   empty -- true end
      printfn "%d reduce done." depth
      () // true end
    else if dischgCoreSub5 deg (ax.low.[ax.lev], ax.upp.[ax.lev]) forcedch allowedch s maxch pos depth then // 5.
      printfn "%d dischgCoreSub5() done." depth
      () // true end
    else
      // 6. error
      Debug.Assert(false, "Unexpected error 101")

  let run (deg    : int)
          (ax     : Const.TpAxle)
          (strL   : string list)
          //(rP1    : byref<Const.TpReducePack1>)
          //(rP2    : byref<Const.TpReducePack2>)
            =
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
      printfn "\n-->Checking hubcap member (%d,%d,%d)" x.[i] y.[i] v.[i]
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
    printfn ""
    ()


module Di =
  let rec private until p f (a: 'a) = if p a then a else until p f (f a)
  let private makeDisData =
    let readFileTacticsD =
      File.ReadAllLines "data/DiTactics07.txt"
        |> Array.toList
        |> List.map ((fun str -> str.Split " ")
                      >> Array.toList
                      >> (List.filter (not << String.IsNullOrEmpty)))
    //let tac2: string list list = [["Degree"; "7"]; ["L0"; "C"; "1"; "-5"]; ["Q.E.D."]]
    // TpAxle
    let deg = 7
    let axles0    = Array.init Const.MAXLEV (fun _ -> Array.zeroCreate Const.CARTVERT)
    let axlesLow0 = Array.take Const.CARTVERT (Array.concat [| [|deg|]; (Array.create (5*deg) 5);           (Array.replicate 1000 0) |])
    let axlesUpp0 = Array.take Const.CARTVERT (Array.concat [| [|deg|]; (Array.create (5*deg) Const.INFTY); (Array.replicate 1000 0) |])
    let axlesLow  = Array.append [|axlesLow0|] axles0
    let axlesUpp  = Array.append [|axlesUpp0|] axles0
    let axles = {low = axlesLow; upp = axlesUpp; lev = 0} : Const.TpAxle
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
        Apply.run strL ax CaseSplit.sym CaseSplit.nosym; CaseSplit.downNosym ax.lev
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
        CaseSplit.downNosym ax.lev
        (deg, {ax with lev = ax.lev - 1}, tailTac, lineCnt + 1)
    | _ -> x

  let discharge: bool =
    let isEnd x =
      match x with
      | (_, {low=_; upp=_; lev=(-1)} : Const.TpAxle, ("Q.E.D." :: _) :: _, _) -> true
      | _                                                                     -> false
    makeDisData |> until isEnd (caseSplit >> apply >> dischg >> disReduce) |> printfn "%A"
    true



