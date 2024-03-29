﻿// Bounded Quantification with references
// system F<:

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

                "∀" + name + ": " + to_string ctx bound + ". " + to_string (add ctx name) ty
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

// <: but : cannot be used in an operator
let rec (<+) tyctx a b =
    match a, b with
    | a, b when a = b -> true
    | _, TTop -> true
    | TBottom, _ -> true
    | TVar i, b -> (<+) tyctx (get tyctx i) b
    | a, TVar i -> (<+) tyctx a (get tyctx i)
    | TFn(arg1, ret1), TFn(arg2, ret2) -> (<+) tyctx arg2 arg1 && (<+) tyctx ret1 ret2
    | TRecord rcd1, TRecord rcd2 ->
        if Map.count rcd1 < Map.count rcd2 then
            false
        else
            Map.forall
                (fun name ty2 ->
                    match Map.tryFind name rcd1 with
                    | Some ty1 -> (<+) tyctx ty1 ty2
                    | None -> false)
                rcd2
    // full f-sub
    | TAll(b1, t1), TAll(b2, t2) ->
        let bound = (<+) tyctx b2 b1

        if bound then
            let tyctx = add tyctx b2
            let tyctx = Array.map (shift_ty_above 1) tyctx
            (<+) tyctx t1 t2
        else
            false
    // same as above
    | TSome(b1, t1), TSome(b2, t2) ->
        let bound = (<+) tyctx b1 b2

        if bound then
            let tyctx = add tyctx b1
            let tyctx = Array.map (shift_ty_above 1) tyctx
            (<+) tyctx t1 t2
        else
            false
    | _, _ -> false

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

exception TypeError of string

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
    | _ -> ty

let rec resolve tyctx ty =
    match ty with
    | TVar i -> resolve tyctx (get tyctx i)
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

let rec typeof_real ctx tyctx term =
    match term with
    | True
    | False -> TBool
    | Unit -> TTop
    | Zero -> TNat
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

        match resolve tyctx (t_callee) with
        | TBottom -> TBottom
        | TFn(t_param, body) when (<+) tyctx t_arg t_param -> if t_arg = TBottom then TBottom else body
        | TFn _ -> raise (TypeError "parameter type mismatch")
        | _ -> raise (TypeError "callee not a function")
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
        match resolve tyctx (typeof_real ctx tyctx term) with
        | TAll(bound, tbody) ->
            if (<+) tyctx ty bound then
                eval_ty tbody ty
            else
                raise (TypeError "cannot satisfy bound")
        | _ -> raise (TypeError "cannot type apply on a non universal type")
    | Pack p ->
        let real_ty = typeof_real ctx tyctx p.value

        match resolve tyctx (p.as_) with
        | TSome(bound, exp) ->
            if not ((<+) tyctx p.ty bound) then
                raise (TypeError "cannot satisfy bound")
            else if real_ty = eval_ty exp p.ty then
                p.as_
            else
                raise (TypeError "existiential param mismatch")
        | _ -> raise (TypeError "can only pack to existiential type")

    | Unpack(value, body) ->
        match resolve tyctx (typeof_real ctx tyctx value) with
        | TSome(bound, t) ->
            let ctx = Array.map (shift_ty_above 1) ctx
            let ctx = add ctx t
            let tyctx = add tyctx bound
            let tyctx = Array.map (shift_ty_above 1) tyctx

            typeof_real ctx tyctx body |> wrong_scope
        | _ -> raise (TypeError "must unpack an existential type")
    | Record r -> TRecord(Map.map (fun _ ty -> typeof_real ctx tyctx ty) r)
    | Proj(obj, key) ->
        match resolve tyctx (typeof_real ctx tyctx obj) with
        | TRecord t ->
            match Map.tryFind key t with
            | Some ty -> ty
            | None -> raise (TypeError $"key {key} not found in proj")
        | _ -> raise (TypeError "proj object not a record")

let typeof = typeof_real [||] [||]

exception RuntimeError of string

type RPack = { ty: Type; value: Res; as_: Type }

and Res =
    | RBool of bool
    | RUnit
    | RInt of int
    | RAll of Type * Term
    | RSome of RPack
    | RRecord of Map<string, Res>
    | RFn of Type * Term

    member this.to_string =
        match this with
        | RUnit -> "()"
        | RBool true -> "true"
        | RBool false -> "false"
        | RInt n -> string n
        | RAll _ -> "ALL"
        | RSome _ -> "SOME"
        | RRecord r ->
            Map.fold (fun state name (r: Res) -> state + $" {name}: {r.to_string}\n") "{\n" r
            + "}"
        | RFn _ -> "FUNCTION"

    member this.to_term =
        match this with
        | RBool true -> True
        | RBool false -> False
        | RUnit -> Unit
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
        | If { cond = test
               then_ = cons
               else_ = alt } ->
            If
                { cond = walk_real c test
                  then_ = walk_real c cons
                  else_ = walk_real c alt }
        | App(callee, arg) -> App(walk_real c callee, walk_real c arg)
        | Abs(ty, body) -> Abs(ty, walk_real (c + 1) body)
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
        | Var _ -> term
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

    walk_real 0 term

let shift_tmty d = walk_tmty (fun ty c -> shift_ty d c ty)

let substitute_tmty s =
    walk_tmty (fun v c -> substitute_ty c s v)

let eval_ty_call arg body =
    let arg = shift_ty_above 1 arg
    let term = substitute_tmty arg body

    shift_tmty -1 term

let eval ctx term =
    let rec eval_real term =
        match term with
        | Unit -> RUnit
        | True -> RBool true
        | False -> RBool false
        | Zero -> RInt 0
        | Succ n ->
            match eval_real n with
            | RInt n -> RInt(n + 1)
            | _ -> raise (RuntimeError "cannot succ a non number")
        | Pred n ->
            match eval_real n with
            | RInt 0 -> RInt 0
            | RInt n -> RInt(n - 1)
            | _ -> raise (RuntimeError "cannot pred a non number")
        | IsZero n ->
            match eval_real n with
            | RInt 0 -> RBool true
            | RInt _ -> RBool false
            | _ -> raise (RuntimeError "cannot pred a non number")

        | Var v -> get ctx v
        | Abs(ty, body) -> RFn(ty, body)
        | App(callee, arg) ->
            match eval_real callee with
            | RFn(_, body) ->
                let arg = eval_real arg
                eval_call body arg.to_term |> eval_real
            | _ -> raise (RuntimeError "callee not a function")

        | If { cond = cond
               then_ = then_
               else_ = else_ } ->
            match eval_real cond with
            | RBool b -> eval_real (if b then then_ else else_)
            | _ -> raise (RuntimeError "guard of conditional not a boolean")

        | TyAbs(bound, t) -> RAll(bound, t)
        | TyApp(t, ty) ->
            match eval_real t with
            | RAll(_, t) -> eval_ty_call ty t |> eval_real
            | _ -> raise (RuntimeError "cannot apply on a non universal type")
        | Pack p ->
            RSome
                { ty = p.ty
                  value = eval_real p.value
                  as_ = p.as_ }
        | Unpack(value, body) ->
            match eval_real value with
            | RSome p -> eval_call body p.value.to_term |> eval_ty_call p.ty |> eval_real
            | _ -> raise (RuntimeError "cannot unpack a non existential type")

        | Record r -> RRecord(Map.map (fun _ term -> eval_real term) r)
        | Proj(obj, key) ->
            match eval_real obj with
            | RRecord t ->
                match Map.tryFind key t with
                | Some r -> r
                | None -> raise (RuntimeError $"key {key} not found in proj")
            | _ -> raise (RuntimeError "proj object not a record")

    eval_real term

let print_res term =
    try
        let ty = typeof term
        printfn "Type: %s" ty.to_string
        let res = eval [||] term
        printfn "Result: %s" res.to_string
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

// ∀X ∀T<:X. ∀F<:X. T -> F -> X
let SBool = TAll(TTop, TAll(TVar 0, TAll(TVar 1, TFn(TVar 1, TFn(TVar 0, TVar 2)))))
// ∀X ∀T<:X. ∀F<:X. T -> F -> T
let STrue = TAll(TTop, TAll(TVar 0, TAll(TVar 1, TFn(TVar 1, TFn(TVar 0, TVar 1)))))
// ∀X ∀T<:X. ∀F<:X. T -> F -> F
let SFalse =
    TAll(TTop, TAll(TVar 0, TAll(TVar 1, TFn(TVar 1, TFn(TVar 0, TVar 0)))))

// ∀X ∀T<:X. ∀F<:X. λt: X. λf: Y. t
let tru = TyAbs(TTop, TyAbs(TVar 0, TyAbs(TVar 1, Abs(TVar 1, Abs(TVar 0, Var 1)))))
// ∀X ∀T<:X. ∀F<:X. λt: X. λf: Y. f
let fls = TyAbs(TTop, TyAbs(TVar 0, TyAbs(TVar 1, Abs(TVar 1, Abs(TVar 0, Var 0)))))
// λb: SFalse ∀X ∀T<:X. ∀F<:X. λt: X. λf: Y. b[X][F][T] f t
let notft =
    Abs(
        SFalse,
        TyAbs(
            TTop,
            TyAbs(
                TVar 0,
                TyAbs(
                    TVar 1,
                    Abs(TVar 1, Abs(TVar 0, App(App(TyApp(TyApp(TyApp(Var 2, TVar 2), TVar 0), TVar 1), Var 0), Var 1)))
                )
            )
        )
    )

printfn "%s" (typeof (App(notft, fls))).to_string

let ta = TRecord Map["a", TNat]

let ab =
    Record(
        Map["a", Succ Zero
            "b", Succ Zero]
    )

let tab = typeof ab

let ac =
    Record(
        Map["a", Zero
            "c", True]
    )

let tac = typeof ac

print_res (Proj(App(App(TyApp(TyApp(TyApp(tru, ta), tab), tac), ab), ac), "b"))

let counter_adt =
    Pack
        { ty = TNat
          value =
            Record(
                Map
                    [ "new", Succ Zero
                      "get", Abs(TNat, Var 0)
                      "inc", Abs(TNat, Succ(Var 0))
                      "rcADT",
                      Pack
                          { ty = TNat
                            value =
                              Record(
                                  Map
                                      [ "new", Succ Zero
                                        "get", Abs(TNat, Var 0)
                                        "inc", Abs(TNat, Succ(Var 0))
                                        "reset", Abs(TNat, Succ Zero) ]
                              )
                            as_ =
                              TSome(
                                  TNat,
                                  TRecord(
                                      Map
                                          [ "new", TVar 0
                                            "get", TFn(TVar 0, TNat)
                                            "inc", TFn(TVar 0, TVar 0)
                                            "reset", TFn(TVar 0, TVar 0) ]
                                  )
                              ) } ]
            )
          as_ =
            TSome(
                TTop,
                TRecord(
                    Map
                        [ "new", TNat
                          "get", TFn(TVar 0, TNat)
                          "inc", TFn(TVar 0, TVar 0)
                          "rcADT",
                          TSome(
                              TVar 0,
                              TRecord(
                                  Map
                                      [ "new", TVar 0
                                        "get", TFn(TVar 0, TNat)
                                        "inc", TFn(TVar 0, TVar 0)
                                        "reset", TFn(TVar 0, TVar 0) ]
                              )
                          ) ]
                )
            ) }

printfn "%s" (typeof (counter_adt)).to_string

print_res (
    Unpack(
        counter_adt,
        Unpack(
            Proj(Var 0, "rcADT"),
            App(
                Proj(Var 1, "get"),
                App(Proj(Var 1, "inc"), App(Proj(Var 0, "reset"), App(Proj(Var 0, "inc"), Proj(Var 0, "new"))))
            )
        )
    )
)
