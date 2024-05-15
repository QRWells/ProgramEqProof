module ProgramEqProof.Main

open ProgramEqProof.TD1.``type``
open ProgramEqProof.TD2.sat


assert (typable (If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Int 4, Int 5)))
assert (not (typable (Add(Bool true, Int 1))))
assert (not (typable (If(Bool true, Int 1, Bool false))))

// if 1+(2+3) < 4 then false else 5
let program = If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Bool false, Int 5)

assert (normalize program = Int 5)
assert (pnormalize program = Int 5)

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

let _ =
    assert (list_mem 2 [ 1; 2; 3 ])
    assert (not (list_mem 5 [ 1; 2; 3 ]))
    assert (not (list_mem 1 []))

let _ =
    assert (list_map (fun x -> 2 * x) [ 1; 2; 3 ] = [ 2; 4; 6 ])
    assert (list_map (fun _ -> ()) [] = [])

let _ =
    let even x = x % 2 = 0 in assert (list_filter even [ 1; 2; 3; 4; 6 ] = [ 2; 4; 6 ])

let _ =
    let x = true, 0 in
    let x' = false, 0 in
    let y = true, 1 in
    let y' = false, 1 in
    let a = [ [ x; y ]; [ x'; y ]; [ x'; y' ] ] in
    let b = [ [ x; y ]; [ x'; y ]; [ x; y' ]; [ x'; y' ] ] in
    assert (naive_dpll a)
    assert (not (naive_dpll b))

let _ =
    let x = true, 0 in
    let y = true, 1 in
    let y' = false, 1 in
    assert (unit [ [ x; y ]; [ x ]; [ y; y' ] ] = Some x)

let _ =
    let x = true, 0 in
    let x' = false, 0 in
    let y = true, 1 in
    let y' = false, 1 in
    assert (_pure [ [ x; y ]; [ x ]; [ y; y' ] ] = Some x)
    assert (_pure [ [ x; y ]; [ x' ]; [ y; y' ] ] = None)

let _ =
    let x = true, 0 in
    let x' = false, 0 in
    let y = true, 1 in
    let y' = false, 1 in
    let a = [ [ x; y ]; [ x'; y ]; [ x'; y' ] ] in
    let b = [ [ x; y ]; [ x'; y ]; [ x; y' ]; [ x'; y' ] ] in
    assert (dpll a)
    assert (not (dpll b))
    assert (dpll_mom a)
    assert (not (dpll_mom b))
    assert (dpll_jw a)
    assert (not (dpll_jw b))

let _ = assert (parse "example/cnf/sat/quinn.cnf" |> dpll)

let _ =
    let prop =
        Or(Or(And(Var 1, Var 2), And(Var 3, Var 4)), Or(And(Var 5, Var 6), And(Var 7, Var 8))) in

    cnf true prop |> printfn "%A"
