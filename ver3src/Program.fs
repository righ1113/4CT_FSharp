// VSCode の「editor.inlayHints.enabled」を
// 「offUnlessPressed」にすると良さげ
// $ cd ver2src
// $ code .
// $ dotnet run
open Reduce
open Discharge


[<EntryPoint>]
let main argv =
  let ret1 = Re.reduce
  printfn "reduce() = %A" ret1
  //let ret2 = Di.discharge 7
  //printfn "discharge() = %b" ret2
  0



