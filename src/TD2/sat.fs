module ProgramEqProof.TD2.sat

open System.IO

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

let rec list_mem x =
    function
    | [] -> false
    | y :: q -> x = y || list_mem x q

let rec list_map f =
    function
    | [] -> []
    | x :: q -> (f x) :: (list_map f q)

let rec list_filter f =
    function
    | [] -> []
    | x :: q -> if f x then x :: (list_filter f q) else list_filter f q

let rec subst_cnf (x: var) (b: bool) (cnf: cnf) : cnf =
    match cnf with
    | [] -> []
    | c :: q when list_mem (b, x) c -> (subst_cnf x b q)
    | c :: q when list_mem (not b, x) c -> (list_filter (fun (b', y) -> y <> x) c) :: (subst_cnf x b q)
    | c :: q -> c :: (subst_cnf x b q)

let rec naive_dpll (cnf: cnf) =
    match cnf with
    | [] -> true
    | list when list_mem [] list -> false
    | c :: q ->
        (naive_dpll (subst_cnf (snd (List.head c)) true cnf))
        || (naive_dpll (subst_cnf (snd (List.head c)) false cnf))

let rec unit cnf =
    match cnf with
    | [] -> None
    | ([ x ]) :: q -> Some x
    | c :: q -> unit q

let rec _pure (cnf: cnf) : literal option =
    match cnf with
    | [] -> None
    | [] :: q -> _pure q
    | c :: q ->
        let (b, v) = List.head c in

        match list_mem true (list_map (list_mem (not b, v)) cnf) with
        | true -> _pure (list_map (list_filter (fun (b', v') -> v' <> v)) cnf)
        | false -> Some(b, v)

let rec unit_all cnf =
    match unit cnf with
    | None -> cnf
    | Some(b, v) -> unit_all (subst_cnf v b cnf)

let rec pure_all cnf =
    match _pure cnf with
    | None -> cnf
    | Some(b, v) -> pure_all (subst_cnf v b cnf)

let rec dpll cnf =
    match (unit_all (pure_all cnf)) with
    | [] -> true
    | [] :: _ -> false
    | c :: q -> let (b, v) = List.head c in (dpll (subst_cnf v true cnf)) || (dpll (subst_cnf v false cnf))

let rec minimal_length min cnf =
    match cnf with
    | [] -> min
    | c :: q -> let l = List.length c in minimal_length (if l < min then l else min) q

let rec minimal_clause cnf =
    let rec aux len cnf =
        match cnf with
        | [] -> []
        | c :: q when List.length c = len -> c :: (aux len q)
        | _ :: q -> aux len q in

    let min = minimal_length (List.length (List.head cnf)) cnf in
    aux min cnf

let rec count (cnf: cnf) (vars: Map<var, int>) =
    match cnf with
    | [] -> vars
    | [] :: q -> count q vars
    | (head :: tail) :: q ->
        let (_, v) = head in

        vars.TryFind(v)
        |> Option.defaultValue 0
        |> fun x -> vars.Add(v, x + 1)
        |> count (tail :: q)

/// Get Maximum number of Occurences in the Minimum length
let mom cnf =
    let reduced = minimal_clause cnf in
    let vars = count reduced (Map []) in

    let folder = fun acc var count -> if count > snd acc then (var, count) else acc in
    fst (Map.fold folder (0, 0) vars)

let rec dpll_mom cnf =
    match pure_all (unit_all cnf) with
    | [] -> true
    | [] :: _ -> false
    | _ -> let v = mom cnf in (dpll_mom (subst_cnf v true cnf)) || (dpll_mom (subst_cnf v false cnf))

let jw (cnf: cnf) (lit: literal) =
    let (_, v) = lit in

    let rec count_occur (clause: clause) =
        match clause with
        | [] -> 0
        | (_, v') :: tail when v' = v -> 1 + count_occur tail
        | _ :: tail -> count_occur tail in

    let list = list_map count_occur cnf in
    List.fold (fun s v -> s + (if v <> 0 then 0.5 ** (float v) else 0.)) 0. list

let rec all_literals (cnf: cnf) : Set<var> =
    let rec aux acc c =
        match c with
        | [] -> acc
        | (_, v) :: q -> aux (Set.add v acc) q in

    List.fold aux (Set []) cnf

/// Get the variable with the highest Jeroslow-Wang score
let jw_var cnf =
    let vars = all_literals cnf in
    let scores = Set.map (fun v -> (v, jw cnf (true, v))) vars in

    Set.maxElement scores |> fst

let rec dpll_jw cnf =
    match pure_all (unit_all cnf) with
    | [] -> true
    | [] :: _ -> false
    | _ -> let v = jw_var cnf in (dpll_jw (subst_cnf v true cnf)) || (dpll_jw (subst_cnf v false cnf))


let parse path : cnf =
    File.ReadAllLines path
    |> Array.toList // convert to list
    |> List.map (fun (s: string) -> s.Trim()) // remove leading/trailing spaces
    |> List.filter (fun s -> s.Length > 0 && not (s.StartsWith('c')) && not (s.StartsWith('p'))) // remove empty lines and comments
    |> List.map (fun s -> s.Split(' ') |> Array.toList) // split by space
    |> List.map (fun l -> List.filter (fun (s: string) -> s.Length > 0) l) // remove empty strings
    |> List.map (fun l -> List.map int l) // convert to int
    |> List.map (fun l -> List.map (fun x -> (x > 0, abs x)) l) // split the number and the sign
    |> List.map (fun l -> List.filter (fun (_, v) -> v <> 0) l) // remove 0, which is the end of the clause

let rec cnf (b: bool) (f: formula) : cnf =
    match f with
    | Var v -> [ [ b, v ] ]
    | And(f1, f2) ->
        if b then
            (cnf true f1) @ (cnf true f2)
        else
            cnf true (Or(Not f1, Not f2))
    | Or(f1, f2) ->
        if b then
            let f1 = cnf true f1 in
            let f2 = cnf true f2 in
            let distribute clauses clause = List.map (List.append clause) clauses in
            List.concat (List.map (distribute f2) f1)
        else
            cnf true (And(Not f1, Not f2))
    | Not f1 -> cnf (not b) f1
    | True -> []
    | False -> [ [] ]
