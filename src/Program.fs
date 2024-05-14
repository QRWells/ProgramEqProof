module ProgramEqProof.Main

open ProgramEqProof.TD1.``type``
open ProgramEqProof.TD2.sat

[<EntryPoint>]
let main _ =
    // if 1+(2+3) < 4 then false else 5
    let program = If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Int 4, Int 5)

    printfn $"%A{typable program}"
    printfn $"%A{pnormalize program}"

    let _ =
        let x = Var 0 in
        let x' = Not x in
        let y = Var 1 in
        let y' = Not y in
        let a = And(And(Or(x, y), Or(x', y)), Or(x', y')) in
        let b = And(And(Or(x, y), Or(x', y)), And(Or(x, y'), Or(x', y'))) in
        assert (sat a)
        assert (not (sat b))

    0 // return an integer exit code
