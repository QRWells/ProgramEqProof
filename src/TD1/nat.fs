module ProgramEqProof.TD1.nat

type nat =
    | O
    | S of nat

let rec plus n m =
    match n with
    | O -> m
    | S n' -> S(plus n' m)

let pred n =
    match n with
    | O -> None
    | S n' -> Some n'

let rec half n =
    match n with
    | O -> O
    | S O -> O
    | S(S n') -> S(half n')

let rec even n =
    match n with
    | O -> true
    | S(O) -> false
    | S(S n') -> even n'
