// type reconstruction or type inference

type Type =
    | TUnit
    | TBool
    | TNat
    | THole of int
    | TFn of Type * Type

    member this.to_string =
        match this with
        | TUnit -> "Unit"
        | TBool -> "Boolean"
        | TNat -> "Integer"
        | THole i -> $"Hole {i}"
        | TFn(arg, ret) -> $"{arg.to_string} -> {ret.to_string}"

exception TypeError of string

let rec replace_ty hole new_t ty =
    match ty with
    | TUnit
    | TBool
    | TNat -> ty
    | THole i -> if i = hole then new_t else THole i
    | TFn(arg, ret) -> TFn(replace_ty hole new_t arg, replace_ty hole new_t ret)

let add ctx v = Array.append ctx [| v |]

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

type If =
    { cond: Term; then_: Term; else_: Term }

and Term =
    | Unit
    | True
    | False
    | Zero
    | Succ of Term
    | Pred of Term
    | IsZero of Term
    | Var of int
    | Abs of Option<Type> * Term
    | Apply of Term * Term
    | Let of Term * Term
    | If of If

let walk onvar term =
    let rec walk_real c term =
        match term with
        | True
        | False
        | Unit
        | Zero -> term
        | Succ n -> Succ(walk_real c n)
        | Pred n -> Pred(walk_real c n)
        | IsZero n -> IsZero(walk_real c n)
        | If { cond = cond
               then_ = then_
               else_ = else_ } ->
            If
                { cond = walk_real c cond
                  then_ = walk_real c then_
                  else_ = walk_real c else_ }

        | Let(value, body) -> Let(walk_real (c + 1) body, walk_real c value)
        | Apply(callee, arg) -> Apply(walk_real c callee, walk_real c arg)
        | Abs(ty, body) -> Abs(ty, walk_real (c + 1) body)
        | Var v -> onvar v c

    walk_real 0 term

let shift d =
    walk (fun v c -> Var(if v >= c then v + d else v))

let substitute s =
    walk (fun v c -> if v = c then shift c s else Var v)

let eval_call body arg =
    let arg = shift 1 arg
    let term = substitute arg body

    shift -1 term

let rec get_constraint fresh ctx term =
    match term with
    | True
    | False -> TBool, [], fresh
    | Unit -> TUnit, [], fresh
    | Zero -> TNat, [], fresh
    | Succ n
    | Pred n ->
        let n, cons, fresh = get_constraint fresh ctx n
        let cons = (n, TNat) :: cons

        TNat, cons, fresh
    | IsZero n ->
        let n, cons, fresh = get_constraint fresh ctx n
        let cons = (n, TNat) :: cons

        TBool, cons, fresh
    | Var i -> get ctx i, [], fresh
    | Abs(ty, body) ->
        let new_ty, fresh =
            match ty with
            | Some ty -> ty, fresh
            | None -> THole fresh, fresh + 1

        let new_ctx = add ctx new_ty
        let ret, cons, fresh = get_constraint fresh new_ctx body

        TFn(new_ty, ret), cons, fresh
    | Apply(callee, arg) ->
        let callee, cons1, fresh = get_constraint fresh ctx callee
        let arg, cons2, fresh = get_constraint fresh ctx arg
        let cons = (callee, TFn(arg, THole fresh)) :: cons1 @ cons2

        THole fresh, cons, fresh + 1
    | If { cond = cond
           then_ = then_
           else_ = else_ } ->
        let ty1, cons1, fresh = get_constraint fresh ctx cond
        let ty2, cons2, fresh = get_constraint fresh ctx then_
        let ty3, cons3, fresh = get_constraint fresh ctx else_

        let cons = (ty1, TBool) :: (ty2, ty3) :: cons1 @ cons2 @ cons3

        ty2, cons, fresh

    // let polymorphism
    | Let(value, body) ->
        match value with
        | Abs(_, _) as abs -> get_constraint fresh ctx (eval_call body abs)
        | _ ->
            let value, cons1, fresh = get_constraint fresh ctx value
            let new_ctx = add ctx value
            let body, cons2, fresh = get_constraint fresh new_ctx body

            body, cons1 @ cons2, fresh + 1

let rec unify cons =
    match cons with
    | [] -> []
    | (s, t) :: rest ->
        match s, t with
        | s, t when s = t -> unify rest
        | THole i, t
        | t, THole i ->
            let rep (t1, t2) = (replace_ty i t t1, replace_ty i t t2)
            let rest = List.map rep rest
            (i, t) :: unify rest
        | TFn(s1, s2), TFn(t1, t2) -> unify (rest @ [ (s1, t1) ] @ [ (s2, t2) ])
        | s, t -> raise (TypeError $"fail to unify {s.to_string} and {t.to_string}")

let rec apply cons ty =
    match cons with
    | [] -> ty
    | (s, t) :: rest -> apply rest (replace_ty s t ty)

let typeof fresh term =
    let ty, cons, _ = get_constraint fresh [||] term
    let cons = unify cons
    let ty = apply cons ty

    ty

type Res =
    | RUnit
    | RBool of bool
    | RNat of int
    | RFn of Term

    member this.to_term =
        match this with
        | RUnit -> Unit
        | RBool true -> True
        | RBool false -> False
        | RNat 0 -> Zero
        | RNat n -> Succ (RNat(n - 1)).to_term
        | RFn f -> Abs(None, f)

    member this.to_string =
        match this with
        | RUnit -> "()"
        | RBool true -> "true"
        | RBool false -> "false"
        | RNat n -> string n
        | RFn _ -> "FUNCTION"

exception RuntimeError of string

let rec eval_real ctx term =
    match term with
    | Unit -> RUnit
    | True -> RBool true
    | False -> RBool false
    | Zero -> RNat 0
    | Succ s ->
        match eval_real ctx s with
        | RNat n -> RNat(n + 1)
        | _ -> raise (RuntimeError "cannot succ non number")
    | Pred p ->
        match eval_real ctx p with
        | RNat 0 -> RNat 0
        | RNat n -> RNat(n - 1)
        | _ -> raise (RuntimeError "cannot pred non number")
    | IsZero n ->
        match eval_real ctx n with
        | RNat 0 -> RBool true
        | RNat _ -> RBool false
        | _ -> raise (TypeError "cannot iszero non number")
    | If { cond = cond
           then_ = then_
           else_ = else_ } ->
        match eval_real ctx cond with
        | RBool b -> eval_real ctx (if b then then_ else else_)
        | _ -> raise (RuntimeError "guard of conditional not a boolean")

    | Var v -> get ctx v
    | Abs(_, fn) -> RFn fn
    | Apply(callee, arg) ->
        match eval_real ctx callee with
        | RFn f -> eval_call f (eval_real ctx arg).to_term |> eval_real ctx
        | _ -> raise (RuntimeError "callee not a function")

    | Let(value, body) -> eval_call body (eval_real ctx value).to_term |> eval_real ctx

let eval = eval_real [||]

let print_res fresh term =
    try
        let ty = typeof fresh term
        printfn "Type: %s" ty.to_string
        let res = eval term

        printfn "Result: %s" res.to_string
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

print_res
    0
    (Apply(
        If
            { cond = True
              then_ = Abs(None, Succ(Var 0))
              else_ = Abs(None, Var 0) },
        Succ Zero
    ))

print_res 0 (Let(True, Var 0))

print_res 0 (Let(Abs(None, Var 0), Apply(Apply(Var 0, Var 0), Apply(Var 0, Succ Zero))))

print_res 0 (Let(Abs(None, Succ Zero), Apply(Var 0, Apply(Var 0, Var 0))))
