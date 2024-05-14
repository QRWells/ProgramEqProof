module ProgramEqProof.TD2.sat

type var = int
type literal = bool * var (* false means negated *)
type clause = literal list
type cnf = clause list

type formula =
    | Var of var
    | And of formula * formula
    | Or of formula * formula
    | Not of formula
    | True
    | False

let rec subst v b a =
    match a with
    | Var x -> if x = v then b else a
    | And(a1, a2) -> And(subst v b a1, subst v b a2)
    | Or(a1, a2) -> Or(subst v b a1, subst v b a2)
    | Not a1 -> Not(subst v b a1)
    | _ -> a

let rec free_var f =
    match f with
    | True
    | False -> None
    | Var v -> Some v
    | And(f1, f2)
    | Or(f1, f2) ->
        match free_var f1 with
        | Some v -> Some v
        | None ->
            (match free_var f2 with
             | Some v -> Some v
             | None -> None)
    | Not f -> free_var f

exception UnclosedFormula

let rec eval f =
    match f with
    | True -> true
    | False -> false
    | Var _ -> raise UnclosedFormula
    | And(f1, f2) -> eval f1 && eval f2
    | Or(f1, f2) -> eval f1 || eval f2
    | Not f1 -> not (eval f1)

let sat f =
    let rec freeVarList acc f =
        match free_var f with
        | None -> acc
        | Some v -> freeVarList (v :: acc) (subst v True f) in // substitute v with True/False to "mark it as used"

    let rec split l f =
        match l with
        | [] -> eval f
        | v :: q -> (split q (subst v True f)) || (split q (subst v False f)) in

    split (freeVarList [] f) f

let rec list_mem x l =
    match l with
    | [] -> false
    | y :: q -> x = y || list_mem x q

let rec list_map f l =
    match l with
    | [] -> []
    | x :: q -> (f x) :: (list_map f q)

let rec list_filter f l =
    match l with
    | [] -> []
    | x :: q -> if f x then x :: (list_filter f q) else list_filter f q
