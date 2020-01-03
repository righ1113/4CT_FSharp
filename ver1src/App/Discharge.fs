namespace Discharge

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

  type TpAxle       = int array array * int array array * int
  type TpAxleI      = int array * int array
  type TpCond       = int array * int array
  type TpAdjmat     = int array array
  type TpVertices   = int array
  type TpQuestion   = int array * int array * int array * int array
  type TpEdgelist   = int array array array
  type TpPosout     = int array * int array * int array * int array array * int array array * int array array * int array
  type TpPosoutI    = int * int * int * int array * int array * int array * int
  type TpReducePack = TpAxle * int array * int array * TpAdjmat * TpEdgelist * bool array * TpVertices * TpQuestion array
  type TpConfPack   = bool * int * bool array * TpVertices * int

  // main routine
  let mainLoop rP posout (nn, mm) deg nosym (low, upp, lev) tactics =
    "Q.E.D."
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
    let ret = mainLoop ((aSLow, aSUpp, 0), bLow, bUpp, adjmat, edgelist, used, image, graphs)
                       rules
                       (nn, mm)
                       deg
                       0
                       (axlesLow, axlesUpp, 0)
                       tactics //(tail (map words (lines inStr)))

    // final check
    //if ret == "Q.E.D." then
    //  putStrLn $ "中心の次数" ++ degStr ++ "のグラフは、電荷が負になるか、近くに好配置があらわれるかです"
    //else
    //  putStr ""

    true



