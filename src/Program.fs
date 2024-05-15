module ProgramEqProof.Main

open ProgramEqProof.TD1.``type``
open ProgramEqProof.TD2.sat

[<EntryPoint>]
let main _ =
    // TD1 tests

    assert (typable (If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Int 4, Int 5)))
    assert (not (typable (Add(Bool true, Int 1))))
    assert (not (typable (If(Bool true, Int 1, Bool false))))

    // if 1+(2+3) < 4 then false else 5
    let program = If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Bool false, Int 5)

    printfn $"%A{normalize program}"
    printfn $"%A{pnormalize program}"

    // TD2 tests

    let _ =
        let x = Var 0 in
        let x' = Not x in
        let y = Var 1 in
        let y' = Not y in
        let a = And(And(Or(x, y), Or(x', y)), Or(x', y')) in
        let b = And(And(Or(x, y), Or(x', y)), And(Or(x, y'), Or(x', y'))) in
        assert (sat a)
        assert (not (sat b))

    let () =
        assert (list_mem 2 [ 1; 2; 3 ])
        assert (not (list_mem 5 [ 1; 2; 3 ]))
        assert (not (list_mem 1 []))

    let () =
        assert (list_map (fun x -> 2 * x) [ 1; 2; 3 ] = [ 2; 4; 6 ])
        assert (list_map (fun _ -> ()) [] = [])

    let () =
        let even x = x % 2 = 0 in assert (list_filter even [ 1; 2; 3; 4; 6 ] = [ 2; 4; 6 ])

    0 // return an integer exit code
