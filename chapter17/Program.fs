// STLC with subtype
// λ<:

type Type =
    | Top
    | Bottom
    | Bool
    | Fn of Type * Type
    | TRecord of Map<string, Type>

    // <: but : cannot be used in an operator
    static member (<+)(a, b) =
        match a, b with
        | a, b when a = b -> true
        | _, Top -> true
        | Bottom, _ -> true
        | Fn(arg1, ret1), Fn(arg2, ret2) -> arg2 <+ arg1 && ret1 <+ ret2
        | TRecord rcd1, TRecord rcd2 ->
            if Map.count rcd1 > Map.count rcd2 then
                false
            else
                Map.forall
                    (fun name ty1 ->
                        match Map.tryFind name rcd2 with
                        | Some ty2 -> ty1 <+ ty2
                        | None -> false)
                    rcd1
        | _, _ -> false

    // join
    static member (<|>)(a, b) =
        match a, b with
        | a, b when a <+ b -> b
        | a, b when b <+ a -> a
        | Fn(arg1, ret1), Fn(arg2, ret2) -> Fn(arg1 <&> arg2, ret1 <|> ret2)
        | TRecord rcd1, TRecord rcd2 ->
            let fields =
                Map.fold
                    (fun state name ty1 ->
                        match Map.tryFind name rcd2 with
                        | Some ty2 -> Map.add name (ty1 <|> ty2) state
                        | None -> state)
                    Map.empty
                    rcd1

            TRecord fields
        | _, _ -> Top

    // meet
    static member (<&>)(a, b) =
        match a, b with
        | a, b when a <+ b -> a
        | a, b when b <+ a -> b
        | Fn(arg1, ret1), Fn(arg2, ret2) -> Fn(arg1 <|> arg2, ret1 <&> ret2)
        | TRecord rcd1, TRecord rcd2 ->
            let fields =
                Map.fold
                    (fun state name ty1 ->
                        Map.add
                            name
                            (match Map.tryFind name state with
                             | Some ty2 -> (ty1 <&> ty2)
                             | None -> ty1)
                            state)
                    rcd1
                    rcd2

            TRecord fields
        | _, _ -> Bottom

exception TypeError of string

type Apply = { arg: Term; callee: Term }

and Abs = { body: Term; type_: Type }

and If = { test: Term; cons: Term; alt: Term }

and Term =
    | True
    | False
    | Unit
    | If of If
    | Var of int
    | Abs of Abs
    | Apply of Apply
    | Record of Map<string, Term>
    | Proj of Term * string

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

let add_type ctx v = Array.append ctx [| v |]

let rec typeof ctx term =
    match term with
    | True
    | False -> Bool
    | Unit -> Top
    | Var v -> get ctx v
    | Abs { type_ = type_; body = body } ->
        let new_ctx = add_type ctx type_
        Fn(type_, typeof new_ctx body)
    | Apply { callee = callee; arg = arg } ->
        let t_callee = typeof ctx callee
        let t_arg = typeof ctx arg

        match t_callee with
        | Bottom -> Bottom
        | Fn(t_param, body) when t_param <+ t_arg -> if t_arg = Bottom then Bottom else body
        | Fn(_, _) -> raise (TypeError "parameter type mismatch")
        | _ -> raise (TypeError "callee not a function")
    | If { test = test; cons = cons; alt = alt } ->
        if typeof ctx test = Bool then
            typeof ctx cons <|> typeof ctx alt
        else
            raise (TypeError "guard of conditional not a boolean")
    | Record r -> TRecord(Map.map (fun _ ty -> typeof ctx ty) r)
    | Proj(obj, key) ->
        match typeof ctx obj with
        | TRecord t ->
            match Map.tryFind key t with
            | Some ty -> ty
            | None -> raise (TypeError $"ket {key} not found in proj")
        | _ -> raise (TypeError "proj object not a record")

exception RuntimeError of string

type Res =
    | RBool of bool
    | RUnit
    | RRecord of Map<string, Res>
    | RFn of Abs

let rec to_term r =
    match r with
    | RBool true -> True
    | RBool false -> False
    | RUnit -> Unit
    | RFn a -> Abs a
    | RRecord r -> Record(Map.map (fun _ r -> to_term r) r)

let walk onvar term =
    let rec walk_real c term =
        match term with
        | True
        | False
        | Unit -> term
        | If { test = test; cons = cons; alt = alt } ->
            If
                { test = walk_real c test
                  cons = walk_real c cons
                  alt = walk_real c alt }
        | Apply a ->
            Apply
                { callee = walk_real c a.callee
                  arg = walk_real c a.arg }
        | Abs a ->
            Abs
                { type_ = a.type_
                  body = walk_real (c + 1) a.body }
        | Var v -> onvar v c
        | Record r -> Record(Map.map (fun name term -> walk_real c term) r)
        | Proj(obj, key) -> Proj(walk_real c obj, key)

    walk_real 0 term

let shift d =
    walk (fun v c -> Var(if v >= c then v + d else v))

let substitute s =
    walk (fun v c -> if v = c then shift c s else Var v)

let eval_call body arg =
    let arg = shift 1 arg
    let term = substitute arg body

    shift -1 term

let rec eval ctx term =
    match term with
    | Unit -> RUnit
    | True -> RBool true
    | False -> RBool false
    | Var v -> get ctx v
    | Abs a -> RFn a
    | Apply { callee = callee; arg = arg } ->
        let callee = eval ctx callee

        match callee with
        | RFn a ->
            let arg = eval ctx arg |> to_term

            eval_call a.body arg |> eval ctx
        | _ -> raise (RuntimeError "callee not a function")

    | If { test = test; cons = cons; alt = alt } ->
        match eval ctx test with
        | RBool b -> eval ctx (if b then cons else alt)
        | _ -> raise (RuntimeError "guard of conditional not a boolean")

    | Record r -> RRecord(Map.map (fun name term -> eval ctx term) r)
    | Proj(obj, key) ->
        match eval ctx obj with
        | RRecord t ->
            match Map.tryFind key t with
            | Some r -> r
            | None -> raise (RuntimeError $"ket {key} not found in proj")
        | _ -> raise (RuntimeError "proj object not a record")

let rec to_string res =
    match res with
    | RUnit -> "()"
    | RBool true -> "true"
    | RBool false -> "false"
    | RRecord r -> Map.fold (fun state name r -> state + $" {name}: {to_string r}\n") "{\n" r + "}"
    | RFn _ -> "FUNCTION"

let print_res term =
    try
        let _ = typeof [||] term
        let res = eval [||] term

        printfn "Result: %s" (to_string res)
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

print_res (
    Apply
        { callee =
            Abs
                { type_ = Bool
                  body =
                    If
                        { test = Var(0)
                          cons =
                            Record
                                Map[("a", Unit)
                                    ("b", False)]
                          alt = Record Map[("a", True)] } }
          arg = True }
)
