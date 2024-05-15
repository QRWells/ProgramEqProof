module ProgramEqProof.Test.test.TD1Tests

open Xunit
open ProgramEqProof.TD1.nat
open ProgramEqProof.TD1.``type``
open Xunit.Sdk

[<Fact>]
let ``Test NAT`` () =
    Assert.Equal(S(S O), plus (S O) (S O))

    Assert.Equal(None, pred O)
    Assert.Equal(Some O, pred (S O))

    Assert.Equal(S O, half (S(S(S O))))
    Assert.Equal(S(S O), half (S(S(S(S O)))))

    Assert.True(even (S(S(O))))
    Assert.False(even (S(S(S(O)))))

[<Fact>]
let ``Test Infer`` () =
    Assert.Equal(TUnit, infer Unit)
    Assert.Equal(TInt, infer (Int 1))
    Assert.Equal(TProduct(TInt, TInt), infer (Product(Int 1, Int 2)))
    Assert.Equal(TInt, infer (First(Product(Int 1, Bool false))))
    Assert.Equal(TBool, infer (Second(Product(Int 1, Bool false))))

    Assert.Throws<TypeError>(fun () -> infer (Lt(Int 1, Bool true)) :> obj)
    |> ignore

    Assert.Throws<TypeError>(fun () -> infer (Add(Int 1, Bool true)) :> obj)
    |> ignore

    Assert.Throws<TypeError>(fun () -> infer (If(Int 0, Int 1, Int 2)) :> obj)
    |> ignore

    Assert.Throws<TypeError>(fun () -> infer (First(Int 1)) :> obj) |> ignore
    Assert.Throws<TypeError>(fun () -> infer (Second(Int 1)) :> obj) |> ignore



[<Fact>]
let ``Test Type`` () =
    Assert.True(typable (If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Int 4, Int 5)))
    Assert.False(typable (Add(Bool true, Int 1)))
    Assert.False(typable (If(Bool true, Int 1, Bool false)))

    // if 1+(2+3) < 4 then 4 else 5
    let program = If(Lt(Add(Int 1, Add(Int 2, Int 3)), Int 4), Int 4, Int 5)

    Assert.Equal(Int 5, normalize program)
    Assert.Equal(Int 5, pnormalize program)

[<Fact>]
let ``Test Swap``() =
    Assert.Equal(Product(Int 1, Int 2), swap(Product(Int 2, Int 1)))
    Assert.Throws<TypeError>(fun () -> swap(Int 1) :> obj) |> ignore