// $ cd ver2src
// $ code .
// $ dotnet run
open Reduce
open Discharge


[<EntryPoint>]
let main (argv: string array) =
  let ret1 = Re.reduce
  printfn "reduce() = %A" ret1
  //let ret2: bool = Di.discharge
  //printfn "discharge() = %b" ret2
  0



