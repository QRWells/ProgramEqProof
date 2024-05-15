module ProgramEqProof.Test.test.TD2Tests

open Xunit
open ProgramEqProof.TD2.sat

[<Fact>]
let ``SAT Test`` () =
    let x = Var 0
    let x' = Not x
    let y = Var 1
    let y' = Not y
    let a = And(And(Or(x, y), Or(x', y)), Or(x', y'))
    let b = And(And(Or(x, y), Or(x', y)), And(Or(x, y'), Or(x', y')))
    Assert.True(sat a)
    Assert.False(sat b)

[<Fact>]
let ``SAT Test 2`` () =
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
