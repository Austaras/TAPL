// STLC with exception

let add ctx v = Array.append ctx [| v |]

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

type Type =
    | Bool
    | TUnit
    | Nat
    | Fn of Type * Type
    | TError

exception TypeError of string

type Let = { value: Term; body: Term }

and If = { test: Term; cons: Term; alt: Term }

and Apply = { arg: Term; callee: Term }
and Abs = { body: Term; type_: Type }

and Term =
    | Zero
    | Unit
    | True
    | False
    | Error
    | Pred of Term
    | Succ of Term
    | IsZero of Term
    | If of If
    | Var of int
    | Apply of Apply
    | Abs of Abs
    | TryWith of Term * Term

let rec equal a b =
    match a, b with
    | Bool, Bool
    | TUnit, TUnit
    | Nat, Nat -> true
    | Fn(a1, a2), Fn(b1, b2) -> equal a1 b1 && equal a2 b2
    | TError, _
    | _, TError -> true
    | _ -> false

let rec typeof ctx term =
    match term with
    | Unit -> TUnit
    | True
    | False -> Bool
    | Zero -> Nat
    | Error -> TError
    | Pred n
    | Succ n ->
        if equal (typeof ctx n) Nat then
            Nat
        else
            raise (TypeError "cannot succ/pred non number")
    | IsZero n ->
        if equal (typeof ctx n) Nat then
            Bool
        else
            raise (TypeError "cannot iszero non number")
    | If { test = test; cons = cons; alt = alt } ->
        if equal (typeof ctx test) Bool then
            let t_cons = typeof ctx cons
            let t_alt = typeof ctx alt

            if equal t_cons t_alt then
                t_cons
            else
                raise (TypeError "arms of conditional have different types")
        else
            raise (TypeError "guard of conditional not a boolean")

    | Var v -> get ctx v
    | Abs { type_ = type_; body = body } ->
        let new_ctx = add ctx type_
        Fn(type_, typeof new_ctx body)
    | Apply { callee = callee; arg = arg } ->
        let t_callee = typeof ctx callee
        let t_arg = typeof ctx arg

        match t_callee with
        | Fn(t_param, body) when equal t_param t_arg -> body
        | Fn(_, _) -> raise (TypeError "parameter type mismatch")
        | _ -> raise (TypeError "callee not a function")
    | TryWith(t1, t2) ->
        let t1 = typeof ctx t1
        let t2 = typeof ctx t2

        if equal t1 t2 then
            t1
        else
            raise (TypeError "arms of try have different types")

exception RuntimeError of string

let walk onvar term =
    let rec walk_real c term =
        match term with
        | True
        | False
        | Unit
        | Zero
        | Error -> term
        | IsZero t -> IsZero(walk_real c t)
        | Succ t -> Succ(walk_real c t)
        | Pred t -> Pred(walk_real c t)
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
        | TryWith(body, exp) -> TryWith(walk_real c body, walk_real c exp)

    walk_real 0 term

let shift d =
    walk (fun v c -> Var(if v >= c then v + d else v))

let substitute s =
    walk (fun v c -> if v = c then shift c s else Var v)

let eval_call body arg =
    let arg = shift 1 arg
    let term = substitute arg body

    shift -1 term

type Res =
    | RUnit
    | RBool of bool
    | RNat of int
    | RFn of Abs
    | RError

let rec to_term r =
    match r with
    | RBool true -> True
    | RBool false -> False
    | RNat 0 -> Zero
    | RNat r -> Succ(to_term (RNat(r - 1)))
    | RUnit -> Unit
    | RFn a -> Abs a
    | RError -> Error

let rec eval ctx term =
    match term with
    | Unit -> RUnit
    | True -> RBool true
    | False -> RBool false
    | Zero -> RNat 0
    | Error -> RError
    | Succ s ->
        match eval ctx s with
        | RNat n -> RNat(n + 1)
        | _ -> raise (RuntimeError "cannot succ non number")
    | Pred p ->
        match eval ctx p with
        | RNat 0 -> RNat 0
        | RNat n -> RNat(n - 1)
        | RError -> RError
        | _ -> raise (RuntimeError "cannot pred non number")
    | IsZero n ->
        match eval ctx n with
        | RNat 0 -> RBool true
        | RNat _ -> RBool false
        | RError -> RError
        | _ -> raise (TypeError "cannot iszero non number")
    | If { test = test; cons = cons; alt = alt } ->
        match eval ctx test with
        | RBool b -> eval ctx (if b then cons else alt)
        | RError -> RError
        | _ -> raise (RuntimeError "guard of conditional not a boolean")

    | Var v -> get ctx v
    | Abs a -> RFn a
    | Apply { callee = callee; arg = arg } ->
        let callee = eval ctx callee

        match callee with
        | RFn a ->
            let arg = eval ctx arg

            eval_call a.body (to_term arg) |> eval ctx
        | RError -> RError
        | _ -> raise (RuntimeError "callee not a function")
    | TryWith(body, alt) ->
        match eval ctx body with
        | RError -> eval ctx alt
        | r -> r

let print_res t =
    try
        let _ = typeof [||] t

        let res =
            match eval [||] t with
            | RUnit -> "unit"
            | RNat i -> string i
            | RBool true -> "true"
            | RBool false -> "false"
            | RFn _ -> "FUNCTION"
            | RError -> "ERROR"

        printfn "Result: %s" res
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

let throw_when_zero =
    Abs
        { type_ = Nat
          body =
            If
                { test = IsZero(Var 0)
                  cons = Error
                  alt = Var 0 } }

print_res (
    Apply
        { callee = throw_when_zero
          arg = Succ Zero }
)

print_res (TryWith(Apply { callee = throw_when_zero; arg = Zero }, Zero))
