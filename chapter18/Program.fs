// Imperative Objects, aka STLC with subtype, reference and recursion

type Type =
    | Top
    | Bottom
    | Bool
    | Nat
    | Fn of Type * Type
    | TRecord of Map<string, Type>
    | TRef of Type

    // <: but : cannot be used in an operator
    static member (<+)(a, b) =
        match a, b with
        | a, b when a = b -> true
        | _, Top -> true
        | Bottom, _ -> true
        | Fn(arg1, ret1), Fn(arg2, ret2) -> arg2 <+ arg1 && ret1 <+ ret2
        | TRecord rcd1, TRecord rcd2 ->
            if Map.count rcd1 < Map.count rcd2 then
                false
            else
                Map.forall
                    (fun name ty2 ->
                        match Map.tryFind name rcd2 with
                        | Some ty1 -> ty1 <+ ty2
                        | None -> false)
                    rcd2
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
    | Zero
    | Succ of Term
    | Pred of Term
    | IsZero of Term
    | If of If
    | Var of int
    | Abs of Abs
    | Apply of Apply
    | Let of Term * Term
    | Record of Map<string, Term>
    | Proj of Term * string
    | Ref of Term
    | Label of int
    | Deref of Term
    | Assign of Term * Term
    | Fix of Term
    | Block of Term[]

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

let add ctx v = Array.append ctx [| v |]

let rec typeof ctx term =
    match term with
    | True
    | False -> Bool
    | Unit -> Top
    | Zero -> Nat
    | Succ n
    | Pred n ->
        if typeof ctx n = Nat then
            Nat
        else
            raise (TypeError "succ/pred on a non number")
    | IsZero n ->
        if typeof ctx n = Nat then
            Bool
        else
            raise (TypeError "IsZero on a non number")
    | Var v -> get ctx v
    | Abs { type_ = type_; body = body } ->
        let new_ctx = add ctx type_
        Fn(type_, typeof new_ctx body)
    | Apply { callee = callee; arg = arg } ->
        let t_callee = typeof ctx callee
        let t_arg = typeof ctx arg

        match t_callee with
        | Bottom -> Bottom
        | Fn(t_param, body) when t_arg <+ t_param -> if t_arg = Bottom then Bottom else body
        | Fn(_, _) -> raise (TypeError "parameter type mismatch")
        | _ -> raise (TypeError "callee not a function")
    | If { test = test; cons = cons; alt = alt } ->
        if typeof ctx test = Bool then
            typeof ctx cons <|> typeof ctx alt
        else
            raise (TypeError "guard of conditional not a boolean")
    | Let(value, body) ->
        let ty = typeof ctx value
        let ctx = add ctx ty

        typeof ctx body
    | Record r -> TRecord(Map.map (fun _ ty -> typeof ctx ty) r)
    | Proj(obj, key) ->
        match typeof ctx obj with
        | TRecord t ->
            match Map.tryFind key t with
            | Some ty -> ty
            | None -> raise (TypeError $"ket {key} not found in proj")
        | _ -> raise (TypeError "proj object not a record")
    | Label _ -> raise (TypeError "label should not be in input")
    | Ref r -> TRef(typeof ctx r)
    | Deref r ->
        let r = typeof ctx r

        match r with
        | TRef r -> r
        | _ -> raise (TypeError "deref on a non ref type")
    | Assign(l, r) ->
        let l = typeof ctx l
        let r = typeof ctx r

        match l with
        | TRef l when l = r -> Top
        | TRef _ -> raise (TypeError "assign on a different type")
        | _ -> raise (TypeError "assign on a non ref type")
    | Fix t ->
        let t = typeof ctx t

        match t with
        | Fn(arg, res) when arg = res -> arg
        | Fn _ -> raise (TypeError "should pass a recusive function to fix")
        | _ -> raise (TypeError "should pass a function to fix")
    | Block t -> Array.fold (fun _ term -> typeof ctx term) Top t


exception RuntimeError of string

type Res =
    | RBool of bool
    | RUnit
    | RNat of int
    | RRecord of Map<string, Res>
    | RFn of Abs
    | RRef of int

let rec to_term r =
    match r with
    | RBool true -> True
    | RBool false -> False
    | RNat n -> if n = 0 then Zero else n - 1 |> RNat |> to_term |> Succ
    | RUnit -> Unit
    | RFn a -> Abs a
    | RRecord r -> Record(Map.map (fun _ r -> to_term r) r)
    | RRef l -> Label l

let walk onvar term =
    let rec walk_real c term =
        match term with
        | True
        | False
        | Unit
        | Zero -> term
        | Succ t -> Succ(walk_real c t)
        | Pred t -> Pred(walk_real c t)
        | IsZero t -> IsZero(walk_real c t)
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
        | Let(value, body) -> Let(walk_real c value, walk_real (c + 1) body)
        | Var v -> onvar v c
        | Record r -> Record(Map.map (fun _ term -> walk_real c term) r)
        | Proj(obj, key) -> Proj(walk_real c obj, key)
        | Label l -> Label l
        | Ref r -> Ref(walk_real c r)
        | Deref r -> Deref(walk_real c r)
        | Assign(l, r) -> Assign(walk_real c l, walk_real c r)
        | Fix r -> Fix(walk_real c r)
        | Block t -> Block(Array.map (fun t -> walk_real c t) t)

    walk_real 0 term

let shift d =
    walk (fun v c -> Var(if v >= c then v + d else v))

let substitute s =
    walk (fun v c -> if v = c then shift c s else Var v)

let eval_call body arg =
    let arg = shift 1 arg
    let term = substitute arg body

    shift -1 term

let rec eval ctx store term =
    match term with
    | Unit -> RUnit, store
    | True -> RBool true, store
    | False -> RBool false, store
    | Zero -> RNat 0, store
    | Succ n ->
        let n, store = eval ctx store n

        match n with
        | RNat n -> RNat(n + 1), store
        | _ -> raise (RuntimeError "succ on a non number")
    | Pred n ->
        let n, store = eval ctx store n

        match n with
        | RNat 0 -> RNat 0, store
        | RNat n -> RNat(n - 1), store
        | _ -> raise (RuntimeError "pred on a non number")
    | IsZero n ->
        let n, store = eval ctx store n

        match n with
        | RNat 0 -> RBool true, store
        | RNat _ -> RBool false, store
        | _ -> raise (RuntimeError "iszero on a non number")
    | Var v -> get ctx v, store
    | Abs a -> RFn a, store
    | Apply { callee = callee; arg = arg } ->
        let callee, store = eval ctx store callee

        match callee with
        | RFn a ->
            let arg, store = eval ctx store arg

            eval_call a.body (to_term arg) |> eval ctx store
        | _ -> raise (RuntimeError "callee not a function")

    | If { test = test; cons = cons; alt = alt } ->
        let test, store = eval ctx store test

        match test with
        | RBool b -> eval ctx store (if b then cons else alt)
        | _ -> raise (RuntimeError "guard of conditional not a boolean")
    | Let(value, body) ->
        let value, store = eval ctx store value

        eval_call body (to_term value) |> eval ctx store
    | Record r ->
        let map, store =
            Map.fold
                (fun (map, store) name term ->
                    let term, store = eval ctx store term
                    Map.add name term map, store)
                (Map.empty, store)
                r

        RRecord map, store
    | Proj(obj, key) ->
        let obj, store = eval ctx store obj

        match obj with
        | RRecord t ->
            match Map.tryFind key t with
            | Some r -> r, store
            | None -> raise (RuntimeError $"ket {key} not found in proj")
        | _ -> raise (RuntimeError "proj object not a record")
    | Ref r ->
        let r, store = eval ctx store r

        RRef(Array.length store), add store r
    | Deref r ->
        let r, store = eval ctx store r

        match r with
        | RRef l -> Array.get store l, store
        | _ -> raise (RuntimeError "deref on a non ref")
    | Assign(l, r) ->
        let l, store = eval ctx store l

        match l with
        | RRef l ->
            let r, store = eval ctx store r
            Array.set store l r
            RUnit, store
        | _ -> raise (RuntimeError "deref on a non ref")
    | Label l -> RRef l, store
    | Fix t ->
        let t, store = eval ctx store t
        let t = to_term t

        match t with
        | Abs a -> eval_call a.body (Fix t) |> eval ctx store
        | _ -> raise (RuntimeError "should pass a function to fix")
    | Block t ->
        let block (_, store) term = eval ctx store term
        Array.fold block (RUnit, store) t

let rec to_string res =
    match res with
    | RUnit -> "()"
    | RBool true -> "true"
    | RBool false -> "false"
    | RNat n -> string n
    | RRecord r -> Map.fold (fun state name r -> state + $" {name}: {to_string r}\n") "{\n" r + "}"
    | RFn _ -> "FUNCTION"
    | RRef r -> $"REFERENCE {string r}"

let print_res term =
    try
        let _ = typeof [||] term
        let res, _ = eval [||] [||] term

        printfn "Result: %s" (to_string res)
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

let add_fn =
    Fix(
        Abs
            { type_ = Fn(Nat, Fn(Nat, Nat))
              body =
                Abs
                    { type_ = Nat
                      body =
                        Abs
                            { type_ = Nat
                              body =
                                If
                                    { test = IsZero(Var 0)
                                      cons = Var 1
                                      alt =
                                        Succ(
                                            Apply
                                                { callee = Apply { callee = Var 2; arg = Var 1 }
                                                  arg = Pred(Var 0) }
                                        ) } } } }
    )

let call_with_unit term = Apply { callee = term; arg = Unit }

let counter_type =
    TRecord
        Map[("get", Fn(Top, Nat))
            ("set", Fn(Nat, Top))
            ("inc", Fn(Top, Top))]

let reset_counter_type =
    TRecord
        Map[("get", Fn(Top, Nat))
            ("set", Fn(Nat, Top))
            ("inc", Fn(Top, Top))
            ("reset", Fn(Top, Top))]

let counter_rep = TRecord Map[("x", TRef Nat)]

let reset_counter_rep =
    TRecord
        Map[("x", TRef Nat)
            ("r", TRef Nat)]

// counterClass =
//     λr:CounterRep.
//     λself: Unit→CounterClass.
//     λ_:Unit.
//         {get = λ_:Unit. !(r.x),
//          set = λn:Unit. r.x:=n
//          inc = λ_:Unit. (self unit).set Succ (self.get unit)}
let counter_class =
    Abs
        { type_ = counter_rep
          body =
            Abs
                { type_ = Fn(Top, counter_type)
                  body =
                    Abs
                        { type_ = Top
                          body =
                            Record
                                Map[("get",
                                     Abs
                                         { type_ = Top
                                           body = Deref(Proj(Var 3, "x")) })

                                    ("set",
                                     Abs
                                         { type_ = Nat
                                           body = Assign(Proj(Var 3, "x"), Var 0) })

                                    ("inc",
                                     Abs
                                         { type_ = Top
                                           body =
                                             Apply
                                                 { callee = Proj(call_with_unit (Var 2), "set")
                                                   arg = Succ(call_with_unit (Proj(call_with_unit (Var 2), "get"))) } })] } } }

// resetCounterClass =
//     λr:ResetCounterRep.
//     λself: Unit→ResetCounterClass.
//     λ_:Unit.
//         let super = counterClass r self in
//         {get = super.get,
//          set = λn:n. r.r:=(self unit).get unit;super.set n
//          inc = super.inc
//          reset = λ_:Unit. (self unit).set r.r}
let reset_counter_class =
    Abs
        { type_ = reset_counter_rep
          body =
            Abs
                { type_ = Fn(Top, reset_counter_type)
                  body =
                    Abs
                        { type_ = Top
                          body =
                            Let(
                                call_with_unit (
                                    Apply
                                        { callee = Apply { callee = counter_class; arg = Var 2 }
                                          arg = Var 1 }
                                ),
                                Record
                                    Map[("get", Proj(Var 0, "get"))

                                        ("set",
                                         Abs
                                             { type_ = Nat
                                               body =
                                                 Block
                                                     [| Assign(
                                                            Proj(Var 4, "r"),
                                                            call_with_unit (Proj(call_with_unit (Var 3), "get"))
                                                        )

                                                        Apply
                                                            { callee = Proj(Var 1, "set")
                                                              arg = Var 0 } |] })

                                        ("inc", Proj(Var 0, "inc"))

                                        ("reset",
                                         Abs
                                             { type_ = Top
                                               body =
                                                 Apply
                                                     { callee = Proj(call_with_unit (Var 3), "set")
                                                       arg = Deref(Proj(Var 4, "r")) } })]
                            ) } } }
// newResetCounter =
//     λ_:Unit. let r = {x=ref 1, r=ref 0} in
//     fix (resetCounterClass r) unit;
let new_reset_count =
    Abs
        { type_ = Top
          body =
            call_with_unit (
                Fix(
                    Apply
                        { callee = reset_counter_class
                          arg =
                            Record
                                Map[("x", Ref(Succ Zero))
                                    ("r", Ref Zero)] }
                )
            ) }

// let inc3 (r: Counter) -> unit =
//     r.inc unit
//     r.inc unit
//     r.inc unit
let inc3 =
    Abs
        { type_ = counter_type
          body = Block(Array.replicate 3 (call_with_unit (Proj(Var 0, "inc")))) }

// let r = newResetCounter
// inc3 r
// add (r.get unit) (r.reset unit; r.get unit)
print_res (
    Let(
        call_with_unit new_reset_count,
        Block
            [| (Apply { callee = inc3; arg = Var 0 })
               Apply
                   { callee =
                       Apply
                           { callee = add_fn
                             arg = call_with_unit (Proj(Var 0, "get")) }
                     arg = Block [| call_with_unit (Proj(Var 0, "reset")); call_with_unit (Proj(Var 0, "get")) |] } |]
    )
)
