module ProgramEqProof.TD1.``type``

type prog =
    | Unit
    | Bool of bool
    | Int of int
    | Add of prog * prog
    | Lt of prog * prog
    | If of prog * prog * prog
    | Product of prog * prog
    | First of prog
    | Second of prog

type typ =
    | TUnit
    | TBool
    | TInt
    | TProduct of typ * typ

exception TypeError

let rec infer p : typ =
    match p with
    | Unit -> TUnit
    | Bool _ -> TBool
    | Int _ -> TInt
    | Add(p1, p2) ->
        (match infer p1, infer p2 with
         | TInt, TInt -> TInt
         | _ -> raise TypeError)
    | Lt(p1, p2) ->
        (match infer p1, infer p2 with
         | TInt, TInt -> TBool
         | _ -> raise TypeError)
    | If(p1, p2, p3) ->
        (match infer p1 with
         | TBool ->
             let t2 = infer p2 in
             let t3 = infer p3 in
             if t2 = t3 then t2 else raise TypeError
         | _ -> raise TypeError)
    | Product(p1, p2) -> TProduct(infer p1, infer p2)
    | First p ->
        (match infer p with
         | TProduct(t1, _) -> t1
         | _ -> raise TypeError)
    | Second p ->
        (match infer p with
         | TProduct(_, t2) -> t2
         | _ -> raise TypeError)

let typable p =
    try
        ignore (infer p)
        true
    with TypeError ->
        false

let rec reduce p =
    match p with
    | Add(Int n1, Int n2) -> Some(Int(n1 + n2))
    | Add(p1, p2) ->
        (match reduce p1 with
         | Some p1' -> Some(Add(p1', p2))
         | None ->
             (match reduce p2 with
              | Some p2' -> Some(Add(p1, p2'))
              | None -> None))
    | Lt(Int n1, Int n2) -> Some(Bool(n1 < n2))
    | Lt(p1, p2) ->
        (match reduce p1 with
         | Some p1' -> Some(Lt(p1', p2))
         | None ->
             (match reduce p2 with
              | Some p2' -> Some(Lt(p1, p2'))
              | None -> None))
    | If(Bool true, p1, _) -> Some p1
    | If(Bool false, _, p2) -> Some p2
    | If(p1, p2, p3) ->
        (match reduce p1 with
         | Some p1' -> Some(If(p1', p2, p3))
         | None -> None)
    | Product(p1, p2) ->
        (match reduce p1 with
         | Some p1' -> Some(Product(p1', p2))
         | None ->
             (match reduce p2 with
              | Some p2' -> Some(Product(p1, p2'))
              | None -> None))
    | First p ->
        (match p with
         | Product(p1, _) -> Some p1
         | _ -> None)
    | Second p ->
        (match p with
         | Product(_, p2) -> Some p2
         | _ -> None)
    | _ -> None

let rec normalize p =
    match reduce p with
    | None -> p
    | Some q -> normalize q

/// Parallel reduction
/// ! Maybe wrong, since it is ambiguous with the definition of the "parallel"
let rec pnormalize p =
    match reduce p with
    | None -> p
    | Some(Add(p1, p2)) -> Add(pnormalize p1, pnormalize p2)
    | Some(Lt(p1, p2)) -> Lt(pnormalize p1, pnormalize p2)
    | Some(If(p1, p2, p3)) ->
        match normalize p1 with
        | Bool true -> pnormalize p2
        | Bool false -> pnormalize p3
        | _ -> If(pnormalize p1, pnormalize p2, pnormalize p3)
    | Some(Product(p1, p2)) -> Product(pnormalize p1, pnormalize p2)
    | Some q -> pnormalize q

let swap p =
    match p with
    | Product(p1, p2) -> Product(p2, p1)
    | _ -> raise TypeError

let func p =
    match p with
    | Product(p1, p2) -> Add(p1, p2)
    | _ -> raise TypeError
