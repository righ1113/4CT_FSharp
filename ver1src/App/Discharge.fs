namespace Discharge

open System.Diagnostics
open FSharpPlus.Lens
open LibraryFS
open LibraryCS2

module Di =

  let VERTS      = 27             // max number of vertices in a free completion + 1
  let CONFS      = 640            // max number of configurations
  let MAXVAL     = 12
  let CARTVERT   = 5 * MAXVAL + 2 // domain of l_A, u_A, where A is an axle
  let INFTY      = 12             // the "12" in the definition of limited part
  let MAXOUTLETS = 110            // max number of outlets
  let MAXELIST   = 134            // length of edgelist[a][b]
  let MAXSTACK   = 5              // max height of Astack (see "Reduce")
  let MAXLEV     = 12             // max level of an input line + 1
  let DIFNOUTS   = [0; 0; 0; 0; 0; 0; 0; 103; 103; 103; 103; 103]

  type TpAxle        = int array array * int array array * int
  type TpAxleI       = int array * int array
  type TpCond        = int array * int array
  type TpAdjmat      = int array array
  type TpVertices    = int array
  type TpQuestion    = int array * int array * int array * int array
  type TpEdgelist    = int array array array
  type TpPosout      = int array * int array * int array * int array array * int array array * int array array * int array
  type TpPosoutI     = int * int * int * int array * int array * int array * int
  type TpReducePack1 = TpAxle * int array * int array * TpAdjmat
  type TpReducePack2 = TpEdgelist * bool array * TpVertices * TpQuestion array
  type TpConfPack    = bool * int * bool array * TpVertices * int

  // 1.Symmetry
  let checkSymmetry tactic axles posout nosym =
    ()

  // 2.Reduce
  let reduce (aStack, bLow, bUpp, adjmat) (edgelist, used, image, redquestions) axles =
    (true, aStack, used, image)

  // main routine
  let rec mainLoop (rP1 : TpReducePack1) rP2 posout (nn, mm) deg nosym (low, upp, lev) tactics =
    match lev with
      | lev when lev >= MAXLEV ->
          Debug.Assert(false, "More than %d levels")
          "error1"
      | lev when lev < 0       ->
          // 終了時
          Array.head (Array.head tactics)
      | _                      ->
          match (Array.head tactics).[1] with
            | "S" ->
                printfn "Symmetry"
                checkSymmetry (Array.tail (Array.tail (Array.head tactics))) (low, upp, lev) posout nosym
                mainLoop rP1 rP2 posout (nn, mm) deg nosym (low, upp, lev - 1) (Array.tail tactics)
            | "R" ->
                printfn "Reduce"
                let (retB, (aStack' : TpAxle), used', image') = reduce rP1 rP2 (low, upp, lev)
                if retB then
                  mainLoop (setl _1 aStack' rP1) (setl _3 image' (setl _2 used' rP2)) posout (nn, mm) deg nosym (low, upp, lev - 1) (Array.tail tactics)
                else
                  Debug.Assert(false, "Reducibility failed")
                  "error3"
            | "H" ->
                printfn "Hubcap"
                "Q.E.D."
            | "C" ->
                printfn "Condition"
                "Q.E.D."
            | _   ->
                Debug.Assert(false, "Invalid instruction")
                "error2"
(*
        case head tactics !! 1 of
          "S" -> do
                  putStrLn "Symmetry"
                  checkSymmetry (tail (tail (head tactics))) axles posout nosym
                  mainLoop rP posout (nn, mm) deg nosym (low, upp, lev-1) (tail tactics)
          "R" -> do
                  putStrLn "Reduce"
                  (retB, aStack', used', image') <- reduce rP axles
                  if retB
                    then
                      mainLoop (((rP & _1 .~ aStack') & _6 .~ used') & _7 .~ image') posout (nn, mm) deg nosym (low, upp, lev-1) (tail tactics)
                    else
                      error "Reducibility failed"
          "H" -> do
                  putStrLn "Hubcap"
                  posout' <- checkHubcap posout (tail (tail (head tactics))) (low, upp, lev) deg
                  mainLoop rP posout' (nn, mm) deg nosym (low, upp, lev-1) (tail tactics)
          "C" -> do
                  putStrLn "Condition"
                  let n = read (head tactics !! 2) :: Int
                  let m = read (head tactics !! 3) :: Int
                  nosym2                   <- checkCondition1 (nn, mm) deg axles n m nosym
                  (cond2, (low2, upp2, _)) <- checkCondition2 (nn, mm) axles n m
                  mainLoop rP posout cond2 deg nosym2 (low2, upp2, lev+1) (tail tactics)
          _   -> error "Invalid instruction"*)
  let discharge =
    printfn "start Dischage.fs"

    LibDischarge.Hoge (1, 2, 3)

    let deg = 7

    // TpAxle
    let axles0 = Array.replicate MAXLEV (Array.replicate CARTVERT 0)
    let axlesLow = Array.take CARTVERT (Array.concat [| [|deg|]; (Array.replicate (5*deg) 5);     (Array.replicate 1000 0) |])
    let axlesUpp = Array.take CARTVERT (Array.concat [| [|deg|]; (Array.replicate (5*deg) INFTY); (Array.replicate 1000 0) |])

    // TpCond
    let nn = Array.replicate MAXLEV 0
    let mm = Array.replicate MAXLEV 0

    // TpOutlet & TpPosout
    //posoutStr    <- readFile $ "readFile/rules" ++ degStr ++ "HS.txt"
    //let posout   = read posoutStr :: TpPosout // CheckHubcap(axles, NULL, 0, print); -- read rules, compute outlets
    let rules = LibFS.readFileRulesD
    printfn "%d" rules.[1].[8].[3]

    // TpReducePack
    let aSLow    = Array.replicate (MAXLEV + 1) (Array.replicate CARTVERT 0)
    let aSUpp    = Array.replicate (MAXLEV + 1) (Array.replicate CARTVERT 0)
    let bLow     = Array.replicate CARTVERT 0
    let bUpp     = Array.replicate CARTVERT 0
    let adjmat   = Array.replicate CARTVERT (Array.replicate CARTVERT 0)
    let edgelist = Array.replicate 12 (Array.replicate 9 (Array.replicate MAXELIST 0))
    let used     = Array.replicate CARTVERT false
    let image    = Array.replicate CARTVERT 0
    let qU       = Array.replicate VERTS 0
    let qV       = Array.replicate VERTS 0
    let qZ       = Array.replicate VERTS 0
    let qXi      = Array.replicate VERTS 0
    //redQStr      <- readFile "readFile/unavoidableHS.txt"
    //let redQ     = read redQStr :: [TpQuestion] // (void) Reduce(NULL, 0, 0); -- read unavoidable set
    let graphs = LibFS.readFileGoodConfsD
    printfn "%d" graphs.[5].C.[1]


    //inStr <- readFile $ "readFile/present" ++ degStr
    let tactics = LibFS.readFileTacticsD
    printfn "%s" tactics.[13].[2]
    let ret = mainLoop ((aSLow, aSUpp, 0), bLow, bUpp, adjmat)
                       (edgelist, used, image, [|([|0|], [|0|], [|0|], [|0|])|]) // graphs) 
                       rules
                       (nn, mm)
                       deg
                       0
                       (axlesLow, axlesUpp, 0)
                       (Array.tail tactics)

    // final check
    //if ret == "Q.E.D." then
    //  putStrLn $ "中心の次数" ++ degStr ++ "のグラフは、電荷が負になるか、近くに好配置があらわれるかです"
    //else
    //  putStr ""

    true



