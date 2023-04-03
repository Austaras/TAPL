// universal types and existential types
// System F omega

let get ctx idx =
    Array.get ctx ((Array.length ctx) - idx - 1)

let add ctx ele = Array.append ctx [| ele |]

let rec gen_name idx =
    let name =
        match idx % 3 with
        | 0 -> "X"
        | 1 -> "Y"
        | _ -> "Z"

    if idx > 3 then name + gen_name (idx / 3) else name

type Type =
    | TUnit
    | TBool
    | TNat
    | TFn of Type * Type
    | TAll of Type
    | TSome of Type
    | TApp of Type * Type
    | TVar of int
    | TRecord of (string * Type)[]
    | TRef of Type

    member this.to_string =
        let rec to_string ctx ty =
            match ty with
            | TUnit -> "Unit"
            | TBool -> "Boolean"
            | TNat -> "Integer"
            | TFn(arg, ret) -> $"{to_string ctx arg} -> {to_string ctx ret}"
            | TVar i -> get ctx i
            | TAll ty ->
                let name = gen_name (Array.length ctx)

                "∀" + name + ". " + to_string (add ctx name) ty
            | TSome ty ->
                let name = gen_name (Array.length ctx)

                "∃" + name + ". " + to_string (add ctx name) ty
            | TRecord r ->
                "{\n"
                + Array.fold (fun state (name, ty) -> state + $"    {name}: {to_string ctx ty},\n") "" r
                + "}"
            | TRef ty -> $"&{to_string ctx ty}"
            | TApp _ -> failwith "unreachable"

        to_string [||] this

let walk_ty onvar c ty =
    let rec walk_real c ty =
        match ty with
        | TUnit
        | TBool
        | TNat -> ty
        | TFn(arg, ret) -> TFn(walk_real c arg, walk_real c ret)
        | TAll t -> TAll(walk_real (c + 1) t)
        | TSome t -> TSome(walk_real (c + 1) t)
        | TVar t -> onvar t c
        | TRecord t -> TRecord(Array.map (fun (name, ty) -> name, walk_real c ty) t)
        | TRef t -> TRef(walk_real c t)
        | TApp(t1, t2) -> TApp(walk_real c t1, walk_real c t2)

    walk_real c ty

let shift_ty d =
    walk_ty (fun v c -> TVar(if v >= c then v + d else v))

let shift_ty_above d = shift_ty d 0

let substitute_ty j s =
    walk_ty (fun v c -> if v = c then shift_ty c j s else TVar v) j

let eval_ty body arg =
    let arg = shift_ty_above 1 arg
    let term = substitute_ty 0 arg body

    shift_ty_above -1 term

let rec simplify_ty ty =
    match ty with
    | TApp(t1, t2) ->
        match simplify_ty t1 with
        | TAll t1 -> eval_ty t1 t2
        | t1 -> t1
    | _ -> ty

type If =
    { cond: Term; then_: Term; else_: Term }

and Pack = { ty: Type; value: Term; as_: Type }

and Term =
    | Unit
    | True
    | False
    | Zero
    | Succ of Term
    | Pred of Term
    | IsZero of Term
    | If of If
    | Var of int
    | Abs of Type * Term
    | Apply of Term * Term
    | Let of Term * Term
    | Fix of Term
    | TyAbs of Term
    | TyApp of Term * Type
    | Pack of Pack
    | Unpack of Term * Term
    | Record of (string * Term)[]
    | Proj of Term * string
    | Ref of Term
    | Deref of Term
    | Assign of Term * Term
    | Label of int

exception TypeError of string

let wrong_scope =
    walk_ty (fun v c -> if v >= c then raise (TypeError "wrong scope") else (TVar v)) 0

let rec typeof ctx term =
    match term with
    | Unit -> TUnit
    | True
    | False -> TBool
    | Zero -> TNat
    | Succ n
    | Pred n ->
        match typeof ctx n with
        | TNat -> TNat
        | _ -> raise (TypeError "cannot pred/succ a non number")
    | IsZero n ->
        match typeof ctx n with
        | TNat -> TBool
        | _ -> raise (TypeError "cannot test zero a non number")
    | If i ->
        match typeof ctx i.then_ with
        | TBool -> TBool
        | _ -> raise (TypeError "guard of conditional not a boolean")
    | Var i -> get ctx i
    | Abs(ty, term) ->
        let ty = simplify_ty ty
        TFn(ty, typeof (add ctx ty) term)
    | Apply(callee, param) ->
        match typeof ctx callee with
        | TFn(arg, ret) when arg = typeof ctx param -> ret
        | TFn _ -> raise (TypeError "arg type mismatch")
        | _ -> raise (TypeError "cannot apply on a non function")
    | Let(value, body) ->
        let new_ctx = add ctx (simplify_ty (typeof ctx value))
        typeof new_ctx body

    | TyAbs t ->
        let ctx = Array.map (shift_ty_above 1) ctx
        TAll(typeof ctx t)
    | TyApp(term, ty) ->
        match typeof ctx term with
        | TAll t -> eval_ty t ty
        | _ -> raise (TypeError "cannot type apply on a non universal type")
    | Pack p ->
        let real_ty = typeof ctx p.value

        match p.as_ with
        | TSome exp ->
            if real_ty = eval_ty exp p.ty then
                p.as_
            else
                raise (TypeError "existiential param mismatch")
        | _ -> raise (TypeError "can only pack to existiential type")

    | Unpack(value, body) ->
        match typeof ctx value with
        | TSome t ->
            let ctx = Array.map (shift_ty_above 1) ctx
            let ctx = add ctx t
            typeof ctx body |> wrong_scope
        | _ -> raise (TypeError "must unpack an existential type")

    | Record r -> TRecord(Array.map (fun (name, t) -> (name, typeof ctx t)) r)
    | Proj(obj, key) ->
        match typeof ctx obj with
        | TRecord r ->
            match Array.tryFind (fun (name, _) -> name = key) r with
            | Some(_, ty) -> ty
            | None -> raise (TypeError $"key {key} not found")
        | _ -> raise (TypeError "can only project record")
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
    | Label _ -> raise (TypeError "ref label should not be in user input")

    | Fix t ->
        match typeof ctx t with
        | TFn(arg, res) when arg = res -> arg
        | TFn _ -> raise (TypeError "should pass a recusive function")
        | _ -> raise (TypeError "should pass a function to fix")

let walk onvar term =
    let rec walk_real c term =
        match term with
        | Unit
        | True
        | False
        | Zero
        | Label _ -> term
        | Succ t -> Succ(walk_real c t)
        | Pred t -> Pred(walk_real c t)
        | IsZero t -> IsZero(walk_real c t)
        | If t ->
            If
                { cond = walk_real c t.cond
                  then_ = walk_real c t.then_
                  else_ = walk_real c t.else_ }
        | Var i -> onvar i c
        | Apply(arg, ret) -> Apply(walk_real c arg, walk_real c ret)
        | Abs(ty, body) -> Abs(ty, walk_real (c + 1) body)
        | Let(value, body) -> Let(walk_real c value, walk_real (c + 1) body)
        | TyAbs t -> TyAbs(walk_real c t)
        | TyApp(term, ty) -> TyApp(walk_real c term, ty)
        | Pack p ->
            Pack
                { ty = p.ty
                  value = walk_real c p.value
                  as_ = p.as_ }
        | Unpack(value, body) -> Unpack(walk_real c value, walk_real (c + 1) body)
        | Record r -> Record(Array.map (fun (name, term) -> name, walk_real c term) r)
        | Proj(obj, key) -> Proj(walk_real c obj, key)
        | Ref t -> Ref(walk_real c t)
        | Assign(left, right) -> Assign(walk_real c left, walk_real c right)
        | Deref t -> Deref(walk_real c t)
        | Fix t -> Fix(walk_real c t)

    walk_real 0 term

let shift d =
    walk (fun v c -> Var(if v >= c then v + d else v))

let substitute s =
    walk (fun v c -> if v = c then shift c s else Var v)

let eval_call body arg =
    let arg = shift 1 arg
    let term = substitute arg body

    shift -1 term

let walk_tmty ontype term =
    let rec walk_real c term =
        match term with
        | Unit
        | True
        | False
        | Zero
        | Var _
        | Label _ -> term
        | Succ t -> Succ(walk_real c t)
        | Pred t -> Pred(walk_real c t)
        | IsZero t -> IsZero(walk_real c t)
        | If t ->
            If
                { cond = walk_real c t.cond
                  then_ = walk_real c t.then_
                  else_ = walk_real c t.else_ }
        | Apply(arg, ret) -> Apply(walk_real c arg, walk_real c ret)
        | Abs(ty, body) -> Abs(ontype ty c, walk_real c body)
        | Let(value, body) -> Let(walk_real c value, walk_real c body)
        | TyAbs t -> TyAbs(walk_real (c + 1) t)
        | TyApp(term, ty) -> TyApp(walk_real c term, ty)
        | Pack p ->
            Pack
                { ty = p.ty
                  value = walk_real c p.value
                  as_ = p.as_ }
        | Unpack(value, body) -> Unpack(walk_real c value, walk_real (c + 1) body)
        | Record r -> Record(Array.map (fun (name, term) -> name, walk_real c term) r)
        | Proj(obj, key) -> Proj(walk_real c obj, key)
        | Ref t -> Ref(walk_real c t)
        | Assign(left, right) -> Assign(walk_real c left, walk_real c right)
        | Deref t -> Deref(walk_real c t)
        | Fix t -> Fix(walk_real c t)

    walk_real 0 term

let shift_tmty d = walk_tmty (fun ty c -> shift_ty d c ty)

let substitute_tmty s =
    walk_tmty (fun v c -> substitute_ty c s v)

let eval_ty_call arg body =
    let arg = shift_ty_above 1 arg
    let term = substitute_tmty arg body

    shift_tmty -1 term

type RPack = { ty: Type; value: Result; as_: Type }

and Result =
    | RUnit
    | RBool of bool
    | RInt of int
    | RFn of Type * Term
    | RAll of Term
    | RSome of RPack
    | RRecord of (string * Result)[]
    | RRef of int

    member this.to_term =
        match this with
        | RUnit -> Unit
        | RBool true -> True
        | RBool false -> False
        | RInt 0 -> Zero
        | RInt n -> Succ (RInt(n - 1)).to_term
        | RAll r -> TyAbs r
        | RSome p ->
            Pack
                { ty = p.ty
                  value = p.value.to_term
                  as_ = p.as_ }
        | RRecord r -> Record(Array.map (fun (name, res: Result) -> name, res.to_term) r)
        | RFn(ty, term) -> Abs(ty, term)
        | RRef i -> Label i

    member this.to_string(store: Result[]) =
        match this with
        | RUnit -> "()"
        | RBool true -> "true"
        | RBool false -> "false"
        | RInt i -> string i
        | RRecord r ->
            "{\n"
            + Array.fold (fun state (name, res: Result) -> state + $"    {name}: {res.to_string store},\n") "" r
            + "\n}"
        | RAll _ -> "ALL"
        | RSome _ -> "SOME"
        | RFn _ -> "FUNCTION"
        | RRef i -> $"&{(Array.get store i).to_string store}"

exception RuntimeError of string

let eval ctx term =
    let rec eval_real store term =
        match term with
        | Unit -> RUnit, store
        | True -> RBool true, store
        | False -> RBool false, store
        | Zero -> RInt 0, store
        | Succ n ->
            let n, store = eval_real store n

            match n with
            | RInt n -> RInt(n + 1), store
            | _ -> raise (RuntimeError "cannot succ a non number")
        | Pred n ->
            let n, store = eval_real store n

            match n with
            | RInt n -> RInt(n - 1), store
            | _ -> raise (RuntimeError "cannot pred a non number")
        | IsZero n ->
            let n, store = eval_real store n

            let res =
                match n with
                | RInt 0 -> true
                | RInt _ -> false
                | _ -> raise (RuntimeError "cannot pred a non number")

            RBool res, store
        | If i ->
            let cond, store = eval_real store i.cond

            eval_real
                store
                (match cond with
                 | RBool true -> i.then_
                 | RBool false -> i.else_
                 | _ -> raise (RuntimeError "cannot pred a non number"))
        | Var i -> get ctx i
        | Abs(ty, t) -> RFn(ty, t), store
        | Apply(callee, arg) ->
            let callee, store = eval_real store callee

            let arg, store = eval_real store arg

            match callee with
            | RFn(_, f) -> eval_call f arg.to_term |> eval_real store
            | _ -> raise (RuntimeError "call a non function")
        | Let(value, body) ->
            let value, store = eval_real store value
            eval_call body value.to_term |> eval_real store

        | TyAbs t -> RAll t, store
        | TyApp(t, ty) ->
            let t, store = eval_real store t

            match t with
            | RAll a -> eval_ty_call ty a |> eval_real store
            | _ -> raise (RuntimeError "cannot apply on a non universal type")
        | Pack p ->
            let value, store = eval_real store p.value

            RSome
                { ty = p.ty
                  value = value
                  as_ = p.as_ },
            store
        | Unpack(value, body) ->
            let value, store = eval_real store value

            match value with
            | RSome p -> eval_call body p.value.to_term |> eval_ty_call p.ty |> eval_real store
            | _ -> raise (RuntimeError "cannot unpack a non existential type")
        | Record r ->
            let folder (rcd, store) (name, term) =
                let r, store = eval_real store term
                add rcd (name, r), store

            let record, store = Array.fold folder ([||], store) r

            RRecord record, store
        | Proj(obj, key) ->
            let obj, store = eval_real store obj

            match obj with
            | RRecord r ->
                match Array.tryFind (fun (name, _) -> name = key) r with
                | Some(_, r) -> r, store
                | None -> raise (TypeError $"key {key} not found")
            | _ -> raise (TypeError "can only project record")
        | Label l -> RRef l, store
        | Ref t ->
            let value, store = (eval_real store t)
            RRef(Array.length store), add store value
        | Assign(left, right) ->
            match eval_real store left with
            | RRef l, store ->
                let value, store = eval_real store right
                Array.set store l value
                RUnit, store
            | _ -> raise (RuntimeError "assign to a non ref value")
        | Deref t ->
            match eval_real store t with
            | RRef l, store -> Array.get store l, store
            | _ -> raise (RuntimeError "derefer to a non ref value")
        | Fix t ->
            let t, store = eval_real store t

            match t with
            | RFn(_, body) -> eval_call body (Fix t.to_term) |> eval_real store
            | _ -> raise (RuntimeError "should pass a function to fix")

    eval_real [||] term

let print_res term =
    try
        let ty = typeof [||] term
        printfn "Type: %s" ty.to_string
        let res, store = eval [||] term
        printfn "Result: %s" (res.to_string store)
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

// λX. λx: X. x
let generic_id = TyAbs(Abs(TVar 0, Var 0))
print_res (Apply(TyApp(generic_id, TNat), Succ Zero))

// λX. λf: X -> X. λx: X. -> f (f x)
let double =
    TyAbs(Abs(TFn(TVar 0, TVar 0), Abs(TVar 0, Apply(Var 1, Apply(Var 1, Var 0)))))

print_res (Apply(Apply(TyApp(double, TNat), Abs(TNat, Succ(Var 0))), Zero))

// λf: ∀X X -> X. if iszero f[Nat] 0 then f[Bool] true else f[Bool] false
let rank2 =
    Abs(
        TAll(TFn(TVar 0, TVar 0)),
        If
            { cond = IsZero(Apply(TyApp(Var 0, TNat), Zero))
              then_ = Apply(TyApp(Var 0, TBool), True)
              else_ = Apply(TyApp(Var 0, TBool), False) }
    )

print_res (Apply(rank2, generic_id))

// ∀X ∀Y ∀R (X -> Y -> R) -> R
let Pair = TAll(TAll(TAll(TFn(TFn(TVar 2, TFn(TVar 1, TVar 0)), TVar 0))))
// ∀X ∀Y λx: X. λy: Y. ∀R λp: X -> Y -> R. p x y
let pair =
    TyAbs(
        TyAbs(Abs(TVar 1, Abs(TVar 0, TyAbs(Abs(TFn(TVar 2, TFn(TVar 1, TVar 0)), Apply(Apply(Var 0, Var 2), Var 1))))))
    )

// ∀X ∀Y λp: Pair X Y. p[X] λx: X. λy: Y. x
let fst =
    TyAbs(TyAbs(Abs(TApp(TApp(Pair, TVar 1), TVar 0), Apply(TyApp(Var 0, TVar 1), Abs(TVar 1, Abs(TVar 0, Var 1))))))

// ∀X ∀Y λp: Pair X Y. p[Y] λx: X. λy: Y. y
let snd =
    TyAbs(TyAbs(Abs(TApp(TApp(Pair, TVar 1), TVar 0), Apply(TyApp(Var 0, TVar 0), Abs(TVar 1, Abs(TVar 0, Var 0))))))

let pr = Apply(Apply(TyApp(TyApp(pair, TNat), TBool), Zero), False)
print_res (Apply(TyApp(TyApp(fst, TNat), TBool), pr))
print_res (Apply(TyApp(TyApp(snd, TNat), TBool), pr))

let counter_adt =
    Pack
        { ty = TNat
          value = Record [| "new", Zero; "get", Abs(TNat, Var 0); "inc", Abs(TNat, Succ(Var 0)) |]
          as_ = TSome(TRecord [| "new", TVar 0; "get", TFn(TVar 0, TNat); "inc", TFn(TVar 0, TVar 0) |]) }

let add3 =
    Abs(TVar 0, Apply(Proj(Var 1, "inc"), Apply(Proj(Var 1, "inc"), Apply(Proj(Var 1, "inc"), Var 0))))

print_res (Unpack(counter_adt, Let(add3, Apply(Proj(Var 1, "get"), Apply(Var 0, Proj(Var 1, "new"))))))

let counter_obj =
    Pack
        { ty = TRef(TNat)
          value =
            Record
                [| "state", Ref(Succ Zero)
                   "get", Abs(TRef(TNat), Deref(Var 0))
                   "inc", Abs(TRef(TNat), Assign(Var 0, Succ(Deref(Var 0)))) |]
          as_ = TSome(TRecord [| "state", TVar 0; "get", TFn(TVar 0, TNat); "inc", TFn(TVar 0, TUnit) |]) }

let sendadd3 =
    Abs(
        TVar 0,
        Let(
            Apply(Proj(Var 1, "inc"), Var 0),
            Let(Apply(Proj(Var 2, "inc"), Var 1), Let(Apply(Proj(Var 3, "inc"), Var 2), Unit))
        )
    )

print_res (
    Unpack(
        counter_obj,
        Let(sendadd3, Let(Apply(Var 0, Proj(Var 1, "state")), Apply(Proj(Var 2, "get"), Proj(Var 2, "state"))))
    )
)
