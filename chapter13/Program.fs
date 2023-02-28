// STLC with reference

let add ctx v = Array.append ctx [| v |]

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

type Type =
    | Bool
    | TUnit
    | Fn of Type * Type
    | TRef of Type
    | Nat

type Let = { value: Term; body: Term }

and If = { test: Term; cons: Term; alt: Term }

and Apply = { arg: Term; callee: Term }
and Abs = { body: Term; type_: Type }

and Term =
    | Zero
    | Unit
    | True
    | False
    | Pred of Term
    | Succ of Term
    | IsZero of Term
    | If of If
    | Let of Let
    | Ref of Term
    | Deref of Term
    | Assign of Term * Term
    | RefLabel of int
    | Var of int
    | Apply of Apply
    | Abs of Abs
    | Seq of Term * Term
    | Times of Term * Term

exception TypeError of string

let rec typeof ctx t =
    match t with
    | Zero -> Nat
    | True
    | False -> Bool
    | Unit -> TUnit
    | Succ n
    | Pred n ->
        match typeof ctx n with
        | Nat -> Nat
        | _ -> raise (TypeError "cannot succ/pred non number")
    | IsZero n ->
        match typeof ctx n with
        | Nat -> Bool
        | _ -> raise (TypeError "cannot iszero non number")
    | If { test = test; cons = cons; alt = alt } ->
        if typeof ctx test = Bool then
            let t_cons = typeof ctx cons
            let t_alt = typeof ctx alt

            if t_cons = t_alt then
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
        | Fn(t_param, body) when t_param = t_arg -> body
        | Fn(_, _) -> raise (TypeError "parameter type mismatch")
        | _ -> raise (TypeError "callee not a function")
    | Let { value = value; body = body } ->
        let new_ctx = add ctx (typeof ctx value)
        typeof new_ctx body

    | Ref t -> TRef(typeof ctx t)
    | Assign(left, right) ->
        match typeof ctx left with
        | TRef tl ->
            let tr = typeof ctx right

            if tl = tr then
                TUnit
            else
                raise (TypeError "assign to wrong type of cell")
        | _ -> raise (TypeError "assign to a non ref type")
    | Deref t ->
        match typeof ctx t with
        | TRef t -> t
        | _ -> raise (TypeError "derefer to a non ref type")

    | Seq(first, second) ->
        let _ = typeof ctx first

        typeof ctx second
    | Times(left, right) ->
        match typeof ctx left, typeof ctx right with
        | Nat, Nat -> Nat
        | _ -> raise (TypeError "times of non nat")
    | RefLabel _ -> raise (TypeError "ref label should not be in user input")

exception RuntimeError of string

let walk onvar term =
    let rec walk_real c term =
        match term with
        | True
        | False
        | Unit
        | Zero -> term
        | IsZero t -> IsZero(walk_real c t)
        | RefLabel l -> RefLabel l
        | Succ t -> Succ(walk_real c t)
        | Pred t -> Pred(walk_real c t)
        | If { test = test; cons = cons; alt = alt } ->
            If
                { test = walk_real c test
                  cons = walk_real c cons
                  alt = walk_real c alt }
        | Let { body = body; value = value } ->
            Let
                { body = walk_real (c + 1) body
                  value = walk_real c value }
        | Apply a ->
            Apply
                { callee = walk_real c a.callee
                  arg = walk_real c a.arg }
        | Abs a ->
            Abs
                { type_ = a.type_
                  body = walk_real (c + 1) a.body }
        | Var v -> onvar v c
        | Ref t -> Ref(walk_real c t)
        | Assign(left, right) -> Assign(walk_real c left, walk_real c right)
        | Deref t -> Deref(walk_real c t)
        | Seq(first, second) -> Seq(walk_real c first, walk_real c second)
        | Times(left, right) -> Times(walk_real c left, walk_real c right)

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
    | RNat of int
    | RBool of bool
    | RFn of Abs
    | RRef of int

let rec to_term r =
    match r with
    | RBool true -> True
    | RBool false -> False
    | RNat 0 -> Zero
    | RNat r -> Succ(to_term (RNat(r - 1)))
    | RUnit -> Unit
    | RFn a -> Abs a
    | RRef r -> RefLabel r

let rec eval ctx store t =
    match t with
    | Zero -> RNat 0, store
    | True -> RBool true, store
    | False -> RBool false, store
    | Unit -> RUnit, store
    | RefLabel l -> RRef l, store
    | Succ s ->
        match eval ctx store s with
        | RNat n, store -> RNat(n + 1), store
        | _ -> raise (RuntimeError "cannot succ non number")
    | Pred p ->
        match eval ctx store p with
        | RNat 0, store -> RNat 0, store
        | RNat n, store -> RNat(n - 1), store
        | _ -> raise (RuntimeError "cannot pred non number")
    | IsZero n ->
        match eval ctx store n with
        | RNat 0, store -> RBool true, store
        | RNat _, store -> RBool false, store
        | _ -> raise (TypeError "cannot iszero non number")
    | If { test = test; cons = cons; alt = alt } ->
        match eval ctx store test with
        | RBool b, store -> eval ctx store (if b then cons else alt)
        | _ -> raise (RuntimeError "guard of conditional not a boolean")

    | Var v -> get ctx v, store
    | Abs a -> RFn a, store
    | Apply { callee = callee; arg = arg } ->
        let callee, store = eval ctx store callee

        match callee with
        | RFn a ->
            let arg, store = eval ctx store arg

            eval_call a.body (to_term arg) |> eval ctx store
        | _ -> raise (RuntimeError "callee not a function")

    | Let { body = body; value = value } ->
        let value, store = eval ctx store value

        let a = eval_call body (to_term value)
        eval ctx store a

    | Ref t ->
        let value, store = (eval ctx store t)
        RRef(Array.length store), add store value

    | Assign(left, right) ->
        match eval ctx store left with
        | RRef l, store ->
            let value, store = eval ctx store right
            Array.set store l value
            RUnit, store
        | a ->
            printfn "%s %s" (string a) (string right)
            raise (RuntimeError "assign to a non ref value")
    | Deref t ->
        match eval ctx store t with
        | RRef l, store -> Array.get store l, store
        | _ -> raise (RuntimeError "derefer to a non ref value")
    | Seq(first, second) ->
        let _, store = eval ctx store first
        eval ctx store second

    | Times(left, right) ->
        let left, store = eval ctx store left
        let right, store = eval ctx store right

        match left, right with
        | (RNat l, RNat r) -> RNat(l * r), store
        | _ -> raise (RuntimeError "times of non nat")

let rec to_string store r =
    match r with
    | RUnit -> "unit"
    | RNat i -> string i
    | RBool true -> "true"
    | RBool false -> "false"
    | RFn _ -> "FUNCTION"
    | RRef l -> Array.get store l |> to_string store

let print_res ctx t =
    try
        let _ = typeof [||] t

        let res, store = eval ctx [||] t

        printfn "Result: %s" (to_string store res)
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

print_res
    [||]
    (Let
        { value = Ref(Succ Zero)
          body = Seq(Assign(Var 0, Succ(Deref(Var 0))), Deref(Var 0)) })

// factorial
print_res
    [||]
    (Let
        { value = Ref(Abs { type_ = Nat; body = Zero })
          body =
            Let
                { value =
                    Abs
                        { type_ = Nat
                          body =
                            If
                                { test = IsZero(Var 0)
                                  cons = Succ Zero
                                  alt =
                                    Times(
                                        Var(0),
                                        Apply
                                            { callee = Deref(Var 1)
                                              arg = Pred(Var 0) }
                                    ) } }
                  body =
                    Seq(
                        Assign(Var(1), Var(0)),
                        Apply
                            { callee = Var(0)
                              arg = Succ(Succ(Succ(Succ(Succ(Succ Zero))))) }
                    ) } })
