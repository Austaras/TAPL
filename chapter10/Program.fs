// STLC with Boolean

type Type =
    | Bool
    | Fn of Type * Type

let rec equal t1 t2 =
    match t1, t2 with
    | Bool, Bool -> true
    | Fn(param1, body1), Fn(param2, body2) -> (equal param1 param2) && (equal body1 body2)
    | _ -> false

let rec to_string t =
    match t with
    | Bool -> "Bool"
    | Fn(param, body) -> $"{to_string param} -> {to_string body}"

type Apply = { arg: Term; callee: Term }

and Abs = { body: Term; type_: Type }

and If = { test: Term; cons: Term; alt: Term }

and Term =
    | True
    | False
    | If of If
    | Var of int
    | Abs of Abs
    | Apply of Apply

exception TypeError of string

let get_type ctx v =
    Array.get ctx (Array.length ctx - v - 1)

let add_type ctx v = Array.append ctx [| v |]

let rec typeof ctx t =
    match t with
    | True
    | False -> Bool
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
    | Var v -> get_type ctx v
    | Abs { type_ = type_; body = body } ->
        let new_ctx = add_type ctx type_
        Fn(type_, typeof new_ctx body)
    | Apply { callee = callee; arg = arg } ->
        let t_callee = typeof ctx callee
        let t_arg = typeof ctx arg

        match t_callee with
        | Fn(t_param, body) when equal t_param t_arg -> body
        | Fn(_, _) -> raise (TypeError "parameter type mismatch")
        | Bool -> raise (TypeError "callee not a function")

let print_type ctx term =
    try
        (typeof ctx term) |> to_string |> printfn "Type: %s"
    with TypeError str ->
        printfn "Error: %s" str

let ctx = [||]
print_type ctx True
print_type ctx (Abs { body = Var(0); type_ = Bool })

print_type
    ctx
    (Abs
        { type_ = Bool
          body = Apply { callee = Var(0); arg = True } })

print_type
    ctx
    (Apply
        { callee =
            Abs
                { type_ = Fn(Bool, Bool)
                  body = Apply { callee = Var(0); arg = True } }
          arg = Abs { body = Var(0); type_ = Bool } })
