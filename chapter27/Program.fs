// Bounded Quantification with references

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

let add ctx v = Array.append ctx [| v |]

let rec gen_name idx =
    let name =
        match idx % 3 with
        | 0 -> "X"
        | 1 -> "Y"
        | _ -> "Z"

    if idx > 3 then name + gen_name (idx / 3) else name

type Type =
    | TTop
    | TBottom
    | TBool
    | TNat
    | TVar of int
    | TAll of Type * Type
    | TSome of Type * Type
    | TApp of Type * Type
    | TFn of Type * Type
    | TRecord of Map<string, Type>
    | TRef of Type
    | TSource of Type
    | TSink of Type

    member this.to_string =
        let rec to_string ctx ty =
            match ty with
            | TTop -> "Top"
            | TBottom -> "Bottom"
            | TBool -> "Boolean"
            | TNat -> "Integer"
            | TFn(param, ret) -> $"{to_string ctx param} -> {to_string ctx ret}"
            | TVar i -> get ctx i
            | TAll(bound, ty) ->
                let name = gen_name (Array.length ctx)

                "∀" + name + ": (" + to_string ctx bound + "). " + to_string (add ctx name) ty
            | TSome(bound, ty) ->
                let name = gen_name (Array.length ctx)

                "∃" + name + ": " + to_string ctx bound + ". " + to_string (add ctx name) ty
            | TRecord r ->
                let formatter state name ty =
                    let ty = to_string ctx ty
                    let lines = ty.Split [| '\n' |]

                    let ty =
                        if lines.Length = 1 then
                            ty
                        else
                            let ty = Array.mapi (fun i line -> if i = 0 then line else "    " + line) lines

                            String.concat "\n" ty

                    state + $"    {name}: {ty},\n"

                "{\n" + Map.fold formatter "" r + "}"
            | TApp _ -> failwith "unreachable"
            | TRef t -> $"&{to_string ctx t}"
            | TSource t -> $"->{to_string ctx t}"
            | TSink t -> $"<-{to_string ctx t}"

        to_string [||] this

let walk_ty onvar c ty =
    let rec walk_real c ty =
        match ty with
        | TTop
        | TBool
        | TNat
        | TBottom -> ty
        | TFn(param, ret) -> TFn(walk_real c param, walk_real c ret)
        | TAll(bound, t) -> TAll(walk_real c bound, walk_real (c + 1) t)
        | TSome(bound, t) -> TSome(walk_real c bound, walk_real (c + 1) t)
        | TVar t -> onvar t c
        | TRecord t -> TRecord(Map.map (fun _ ty -> walk_real c ty) t)
        | TRef t -> TRef(walk_real c t)
        | TSource t -> TSource(walk_real c t)
        | TSink t -> TSink(walk_real c t)
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

exception TypeError of string

// <: but : cannot be used in an operator
let rec (<+) tyctx a b =
    let rec subtype tyctx a b count =
        if count > 3000 then
            raise (TypeError "detect dead loop in subtype checking")

        match a, b with
        | a, b when a = b -> true
        | _, TTop -> true
        | TBottom, _ -> true
        | TVar i, b -> subtype tyctx (get tyctx i) b (count + 1)
        | a, TVar i -> subtype tyctx a (get tyctx i) (count + 1)
        | TFn(arg1, ret1), TFn(arg2, ret2) -> subtype tyctx arg2 arg1 (count + 1) && subtype tyctx ret1 ret2 (count + 1)
        | TRecord rcd1, TRecord rcd2 ->
            if Map.count rcd1 < Map.count rcd2 then
                false
            else
                Map.forall
                    (fun name ty2 ->
                        match Map.tryFind name rcd1 with
                        | Some ty1 -> subtype tyctx ty1 ty2 (count + 1)
                        | None -> false)
                    rcd2
        // full f-sub
        | TAll(b1, t1), TAll(b2, t2) ->
            subtype tyctx b2 b1 (count + 1)
            && subtype tyctx (eval_ty t1 b2) (eval_ty t2 b2) (count + 1)

        // same as above
        | TSome(b1, t1), TSome(b2, t2) ->
            subtype tyctx b1 b2 (count + 1)
            && subtype tyctx (eval_ty t1 b1) (eval_ty t2 b2) (count + 1)
        | TSource a, TSource b -> subtype tyctx a b (count + 1)
        | TSink a, TSink b -> subtype tyctx b a (count + 1)
        | TRef a, TSource b -> subtype tyctx a b (count + 1)
        | TRef a, TSink b -> subtype tyctx a b (count + 1)
        | _, _ -> false

    subtype tyctx a b 0

// join
let rec (<|>) tyctx a b =
    match a, b with
    | a, b when (<+) tyctx a b -> b
    | a, b when (<+) tyctx b a -> a
    | TVar i, b -> (<|>) tyctx (get tyctx i) b
    | a, TVar i -> (<|>) tyctx a (get tyctx i)
    | TFn(arg1, ret1), TFn(arg2, ret2) -> TFn((<&>) tyctx arg1 arg2, (<|>) tyctx ret1 ret2)
    | TRecord rcd1, TRecord rcd2 ->
        let fields =
            Map.fold
                (fun state name ty1 ->
                    match Map.tryFind name rcd2 with
                    | Some ty2 -> Map.add name ((<|>) tyctx ty1 ty2) state
                    | None -> state)
                Map.empty
                rcd1

        TRecord fields
    | _, _ -> TTop

// meet
and (<&>) tyctx a b =
    match a, b with
    | a, b when (<+) tyctx a b -> a
    | a, b when (<+) tyctx a b -> b
    | TVar i, b -> (<|>) tyctx (get tyctx i) b
    | a, TVar i -> (<|>) tyctx a (get tyctx i)
    | TFn(arg1, ret1), TFn(arg2, ret2) -> TFn((<|>) tyctx arg1 arg2, (<&>) tyctx ret1 ret2)
    | TRecord rcd1, TRecord rcd2 ->
        let fields =
            Map.fold
                (fun state name ty1 ->
                    Map.add
                        name
                        (match Map.tryFind name state with
                         | Some ty2 -> (<&>) tyctx ty1 ty2
                         | None -> ty1)
                        state)
                rcd1
                rcd2

        TRecord fields
    | _, _ -> TBottom

let rec simplify_ty tyctx ty =
    match ty with
    | TApp(t1, t2) ->
        match simplify_ty tyctx t1 with
        | TAll(bound, t1) ->
            if (<+) tyctx t2 bound then
                eval_ty t1 t2
            else
                raise (TypeError "cannot satisfy bound")
        | t1 -> t1
    | TVar i -> simplify_ty tyctx (get tyctx i)
    | _ -> ty

let wrong_scope =
    walk_ty (fun v c -> if v >= c then raise (TypeError "wrong scope") else (TVar v)) 0

type If =
    { cond: Term; then_: Term; else_: Term }

and Pack = { ty: Type; value: Term; as_: Type }

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
    | Abs of Type * Term
    | App of Term * Term
    | TyAbs of Type * Term
    | TyApp of Term * Type
    | Pack of Pack
    | Unpack of Term * Term
    | Record of Map<string, Term>
    | Proj of Term * string
    | As of Term * Type
    | Let of Term * Term
    | Block of Term[]
    | Error
    | Ref of Term
    | Deref of Term
    | Assign of Term * Term
    | Label of int

let rec typeof_real ctx tyctx term =
    match term with
    | True
    | False -> TBool
    | Unit -> TTop
    | Zero -> TNat
    | Error -> TBottom
    | Succ n
    | Pred n ->
        match typeof_real ctx tyctx n with
        | TNat -> TNat
        | _ -> raise (TypeError "cannot pred/succ a non number")
    | IsZero n ->
        match typeof_real ctx tyctx n with
        | TNat -> TBool
        | _ -> raise (TypeError "cannot test zero a non number")
    | Var v -> get ctx v
    | Abs(ty, body) ->
        let new_ctx = add ctx (simplify_ty tyctx ty)
        TFn(ty, typeof_real new_ctx tyctx body)
    | App(callee, arg) ->
        let t_callee = typeof_real ctx tyctx callee
        let t_arg = typeof_real ctx tyctx arg

        match t_callee with
        | TBottom -> TBottom
        | TFn(t_param, body) when (<+) tyctx t_arg t_param -> if t_arg = TBottom then TBottom else body
        | TFn _ -> raise (TypeError "parameter type mismatch")
        | _ -> raise (TypeError "callee not a function")
    | As(value, ty) ->
        let real_ty = typeof_real ctx tyctx value

        if (<+) tyctx real_ty ty || (<+) tyctx ty real_ty then
            ty
        else
            raise (TypeError "cast to irrelevant type")
    | Let(value, body) ->
        let new_ctx = add ctx (simplify_ty tyctx (typeof_real ctx tyctx value))
        typeof_real new_ctx tyctx body
    | Block b ->
        let checker _ stmt = typeof_real ctx tyctx stmt

        Array.fold checker TTop b
    | If { cond = test
           then_ = cons
           else_ = alt } ->
        if typeof_real ctx tyctx test = TBool then
            (<|>) tyctx (typeof_real ctx tyctx cons) (typeof_real tyctx ctx alt)
        else
            raise (TypeError "guard of conditional not a boolean")

    | TyAbs(bound, t) ->
        let ctx = Array.map (shift_ty_above 1) ctx
        let tyctx = add tyctx bound
        let tyctx = Array.map (shift_ty_above 1) tyctx
        TAll(bound, typeof_real ctx tyctx t)
    | TyApp(term, ty) ->
        match typeof_real ctx tyctx term with
        | TAll(bound, tbody) ->
            if (<+) tyctx ty bound then
                eval_ty tbody ty
            else
                raise (TypeError "cannot satisfy bound")
        | _ -> raise (TypeError "cannot type apply on a non universal type")
    | Pack p ->
        let real_ty = typeof_real ctx tyctx p.value

        match p.as_ with
        | TSome(bound, exp) ->
            if not ((<+) tyctx p.ty bound) then
                raise (TypeError "cannot satisfy bound")
            else if real_ty = eval_ty exp p.ty then
                p.as_
            else
                raise (TypeError "existiential param mismatch")
        | _ -> raise (TypeError "can only pack to existiential type")

    | Unpack(value, body) ->
        match typeof_real ctx tyctx value with
        | TSome(bound, t) ->
            let ctx = Array.map (shift_ty_above 1) ctx
            let ctx = add ctx t
            let tyctx = add tyctx bound
            let tyctx = Array.map (shift_ty_above 1) tyctx

            typeof_real ctx tyctx body |> wrong_scope
        | _ -> raise (TypeError "must unpack an existential type")
    | Record r -> TRecord(Map.map (fun _ ty -> typeof_real ctx tyctx ty) r)
    | Proj(obj, key) ->
        match typeof_real ctx tyctx obj with
        | TRecord t ->
            match Map.tryFind key t with
            | Some ty -> ty
            | None -> raise (TypeError $"key {key} not found in proj")
        | _ -> raise (TypeError "proj object not a record")

    | Ref t -> TRef(typeof_real ctx tyctx t)
    | Assign(left, right) ->
        match typeof_real ctx tyctx left with
        | TRef tl
        | TSink tl ->
            let tr = typeof_real ctx tyctx right

            if tl = tr then
                TTop
            else
                raise (TypeError "assign to wrong type of cell")
        | _ -> raise (TypeError "assign to a non ref type")
    | Deref t ->
        match typeof_real ctx tyctx t with
        | TRef t
        | TSource t -> t
        | _ -> raise (TypeError "dereference to a non ref type")
    | Label _ -> raise (TypeError "ref label should not be in user input")

let typeof = typeof_real [||] [||]

exception RuntimeError of string

type RPack = { ty: Type; value: Res; as_: Type }

and Res =
    | RBool of bool
    | RUnit
    | RError
    | RInt of int
    | RAll of Type * Term
    | RSome of RPack
    | RRecord of Map<string, Res>
    | RFn of Type * Term
    | RRef of int

    member this.to_string(store: Res[]) =
        match this with
        | RUnit -> "()"
        | RError -> "error"
        | RBool true -> "true"
        | RBool false -> "false"
        | RInt n -> string n
        | RAll _ -> "ALL"
        | RSome _ -> "SOME"
        | RRecord r ->
            Map.fold (fun state name (r: Res) -> state + $" {name}: {r.to_string}\n") "{\n" r
            + "}"
        | RFn _ -> "FUNCTION"
        | RRef i -> $"&{(Array.get store i).to_string store}"

    member this.to_term =
        match this with
        | RBool true -> True
        | RBool false -> False
        | RUnit -> Unit
        | RError -> Error
        | RInt 0 -> Zero
        | RInt n -> Succ (RInt(n - 1)).to_term
        | RAll(bound, r) -> TyAbs(bound, r)
        | RSome p ->
            Pack
                { ty = p.ty
                  value = p.value.to_term
                  as_ = p.as_ }
        | RFn(ty, body) -> Abs(ty, body)
        | RRecord r -> Record(Map.map (fun _ (r: Res) -> r.to_term) r)
        | RRef i -> Label i

let walk onvar term =
    let rec walk_real c term =
        match term with
        | True
        | False
        | Unit
        | Zero
        | Error
        | Label _ -> term
        | Succ t -> Succ(walk_real c t)
        | Pred t -> Pred(walk_real c t)
        | IsZero t -> IsZero(walk_real c t)
        | If { cond = test
               then_ = cons
               else_ = alt } ->
            If
                { cond = walk_real c test
                  then_ = walk_real c cons
                  else_ = walk_real c alt }
        | App(callee, arg) -> App(walk_real c callee, walk_real c arg)
        | Abs(ty, body) -> Abs(ty, walk_real (c + 1) body)
        | As(value, ty) -> As(walk_real c value, ty)
        | Let(value, body) -> Let(walk_real c value, walk_real (c + 1) body)
        | Block(b) -> Block(Array.map (walk_real c) b)
        | Var v -> onvar v c
        | TyAbs(bound, t) -> TyAbs(bound, walk_real c t)
        | TyApp(term, ty) -> TyApp(walk_real c term, ty)
        | Pack p ->
            Pack
                { ty = p.ty
                  value = walk_real c p.value
                  as_ = p.as_ }
        | Unpack(value, body) -> Unpack(walk_real c value, walk_real (c + 1) body)
        | Record r -> Record(Map.map (fun _ term -> walk_real c term) r)
        | Proj(obj, key) -> Proj(walk_real c obj, key)

        | Ref t -> Ref(walk_real c t)
        | Assign(left, right) -> Assign(walk_real c left, walk_real c right)
        | Deref t -> Deref(walk_real c t)

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
        | Error
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
        | App(callee, arg) -> App(walk_real c callee, walk_real c arg)
        | Abs(ty, body) -> Abs(ontype ty c, walk_real c body)
        | As(value, ty) -> As(walk_real c value, ontype ty c)
        | Let(value, body) -> Let(walk_real c value, walk_real c body)
        | Block b -> Block(Array.map (walk_real c) b)

        | TyAbs(bound, t) -> TyAbs(ontype bound c, walk_real (c + 1) t)
        | TyApp(term, ty) -> TyApp(walk_real c term, ty)
        | Pack p ->
            Pack
                { ty = p.ty
                  value = walk_real c p.value
                  as_ = p.as_ }
        | Unpack(value, body) -> Unpack(walk_real c value, walk_real (c + 1) body)
        | Record r -> Record(Map.map (fun _ term -> walk_real c term) r)
        | Proj(obj, key) -> Proj(walk_real c obj, key)

        | Ref t -> Ref(walk_real c t)
        | Assign(left, right) -> Assign(walk_real c left, walk_real c right)
        | Deref t -> Deref(walk_real c t)

    walk_real 0 term

let shift_tmty d = walk_tmty (fun ty c -> shift_ty d c ty)

let substitute_tmty s =
    walk_tmty (fun v c -> substitute_ty c s v)

let eval_ty_call arg body =
    let arg = shift_ty_above 1 arg
    let term = substitute_tmty arg body

    shift_tmty -1 term

let eval ctx term =
    let rec eval_real store term =
        match term with
        | Unit -> RUnit, store
        | True -> RBool true, store
        | False -> RBool false, store
        | Zero -> RInt 0, store
        | Error -> RError, store
        | Succ n ->
            let n, store = eval_real store n

            match n with
            | RInt n -> RInt(n + 1), store
            | RError -> RError, store
            | _ -> raise (RuntimeError "cannot succ a non number")
        | Pred n ->
            let n, store = eval_real store n

            match n with
            | RInt 0 -> RInt 0, store
            | RInt n -> RInt(n - 1), store
            | RError -> RError, store
            | _ -> raise (RuntimeError "cannot pred a non number")
        | IsZero n ->
            let n, store = eval_real store n

            match n with
            | RInt 0 -> RBool true, store
            | RInt _ -> RBool false, store
            | RError -> RError, store
            | _ -> raise (RuntimeError "cannot pred a non number")

        | Var v -> get ctx v
        | Abs(ty, body) -> RFn(ty, body), store
        | App(callee, arg) ->
            let callee, store = eval_real store callee

            match callee with
            | RFn(_, body) ->
                let arg, store = eval_real store arg

                match arg with
                | RError -> RError, store
                | _ -> eval_call body arg.to_term |> eval_real store
            | RError -> RError, store
            | _ -> raise (RuntimeError "callee not a function")

        | As(value, ty) ->
            let value, store = eval_real store value

            let real_ty = typeof value.to_term

            if (<+) [||] real_ty ty then
                value, store
            else
                raise (RuntimeError "cast to wrong type")
        | Let(value, body) ->
            let value, store = eval_real store value

            match value with
            | RError -> RError, store
            | _ -> eval_call body value.to_term |> eval_real store

        | Block b ->
            let runner (_, store) stmt = eval_real store stmt

            Array.fold runner (RUnit, store) b

        | If { cond = cond
               then_ = then_
               else_ = else_ } ->
            let cond, store = eval_real store cond

            match cond with
            | RBool b -> eval_real store (if b then then_ else else_)
            | RError -> RError, store
            | _ -> raise (RuntimeError "guard of conditional not a boolean")

        | TyAbs(bound, t) -> RAll(bound, t), store
        | TyApp(t, ty) ->
            let t, store = eval_real store t

            match t with
            | RAll(_, t) -> eval_ty_call ty t |> eval_real store
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
            | RError -> RError, store
            | _ -> raise (RuntimeError "cannot unpack a non existential type")

        | Record r ->
            let folder (rcd, store) name term =
                let r, store = eval_real store term
                Map.add name r rcd, store

            let record, store = Map.fold folder (Map.empty, store) r

            RRecord record, store
        | Proj(obj, key) ->
            let obj, store = eval_real store obj

            match obj with
            | RRecord t ->
                match Map.tryFind key t with
                | Some r -> r, store
                | None -> raise (RuntimeError $"key {key} not found in proj")
            | RError -> RError, store
            | _ -> raise (RuntimeError "proj object not a record")

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

    eval_real [||] term

let print_res term =
    try
        let ty = typeof term
        printfn "Type: %s" ty.to_string
        let res, store = eval [||] term
        printfn "Result: %s" (res.to_string store)
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

let counter_rep = TRecord Map["x", TRef TNat]

let set_counter =
    TRecord(
        Map["get", TFn(TTop, TNat)
            "set", TFn(TNat, TTop)
            "inc", TFn(TTop, TTop)]
    )

let set_counter_class =
    TyAbs(
        counter_rep,
        Abs(
            TSource(TFn(TVar 0, set_counter)),
            Abs(
                TVar 0,
                Record(
                    Map
                        [ "get", Abs(TTop, Deref(Proj(Var 1, "x")))
                          "set", Abs(TNat, Assign(Proj(Var 1, "x"), Var 0))
                          "inc",
                          Abs(
                              TTop,
                              App(
                                  Proj(App(Deref(Var 2), Var 1), "set"),
                                  Succ(App(Proj(App(Deref(Var 2), Var 1), "get"), Unit))
                              )
                          ) ]
                )
            )
        )
    )

let instr_counter_rep =
    TRecord
        Map["x", TRef TNat
            "a", TRef TNat]


let instr_counter =
    TRecord
        Map["get", TFn(TTop, TNat)
            "set", TFn(TNat, TTop)
            "inc", TFn(TTop, TTop)
            "accesses", TFn(TTop, TNat)]


let instr_counter_class =
    TyAbs(
        instr_counter_rep,
        Abs(
            TSource(TFn(TVar 0, instr_counter)),
            Abs(
                TVar 0,
                Let(
                    App(TyApp(set_counter_class, TVar 0), Var 1),
                    Record(
                        Map
                            [ "get", Proj(App(Var 0, Var 1), "get")
                              "set",
                              Abs(
                                  TNat,
                                  Block
                                      [| Assign(Proj(Var 2, "a"), Succ(Deref(Proj(Var 2, "a"))))
                                         App(Proj(App(Var 1, Var 2), "set"), Var 0) |]
                              )
                              "inc", Proj(App(Var 0, Var 1), "inc")
                              "accesses", Abs(TTop, Deref(Proj(Var 2, "a"))) ]
                    )
                )
            )
        )
    )

let new_instr_counter =
    Let(
        Ref(Abs(instr_counter_rep, As(Error, instr_counter))),
        Let(
            App(TyApp(instr_counter_class, instr_counter_rep), Var 0),
            Block
                [| Assign(Var 1, Var 0)
                   Abs(
                       TTop,
                       Let(
                           Record
                               Map["x", Ref(Succ Zero)
                                   "a", Ref(Zero)],
                           App(Var 2, Var 0)
                       )
                   ) |]
        )
    )

printfn "%s" (typeof (new_instr_counter)).to_string

print_res (Let(App(new_instr_counter, Unit), Block [| App(Proj(Var 0, "inc"), Unit); App(Proj(Var 0, "get"), Unit) |]))

let not tvar = TAll(tvar, TVar 0)
let t = TAll(TTop, not (TAll(TVar 0, not (TVar 0))))
let other = TAll(t, not (TVar 0))

try
    printfn "%b" ((<+) [||] t other)
with TypeError s ->
    printfn "Error: %s" s
