// STLC with various extensions and isomorphic recursive types

type Type =
    | Bool
    | TString
    | TFloat
    | TUnit
    | TRecord of (string * Type)[]
    | TVariant of (string * Type)[]
    | TRecursive of Type
    | TId of int
    | Fn of Type * Type

let walk_ty onid ty =
    let rec walk_ty_real c ty =
        let mapper (name, ty) = (name, walk_ty_real c ty)

        match ty with
        | Bool
        | TString
        | TFloat
        | TUnit -> ty
        | TRecord r -> TRecord(Array.map mapper r)
        | TVariant v -> TVariant(Array.map mapper v)
        | TRecursive ty -> walk_ty_real (c + 1) ty
        | TId i -> onid i c
        | Fn(arg, ret) -> Fn(walk_ty_real c arg, walk_ty_real c ret)

    walk_ty_real 0 ty

let shift_ty d =
    walk_ty (fun v c -> TId(if v >= c then v + d else v))

let substitute_ty s =
    walk_ty (fun v c -> if v = c then shift_ty c s else TId v)

let remove_rec body arg =
    let arg = shift_ty 1 arg
    let term = substitute_ty arg body

    shift_ty -1 term

let add ctx v = Array.append ctx [| v |]

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

let rec resolve ctx ty =
    match ty with
    | TId i -> resolve ctx (get ctx i)
    | _ -> ty

type BinOp =
    | Add
    | Minus
    | Multiply
    | Divide
    | Equal

type Apply = { arg: Term; callee: Term }
and Abs = { body: Term; type_: Type }

and Let = { value: Term; body: Term }

and If = { test: Term; cons: Term; alt: Term }

and Tag =
    { tag: string
      value: Term
      type_: Type }

and Bin = { left: Term; op: BinOp; right: Term }

and CaseBranch = { tag: string; body: Term }

and Case = { test: Term; branch: CaseBranch[] }

and Term =
    | True
    | False
    | Unit
    | Float of float
    | String of string
    | As of Term * Type
    | If of If
    | Bin of Bin
    | Let of Let
    | Var of int
    | Abs of Abs
    | Apply of Apply
    | Record of (string * Term)[]
    | Tag of Tag
    | Proj of Term * string // x.y or x.0
    | Case of Case
    | Fix of Term
    | Fold of Type * Term
    | Unfold of Type * Term

exception TypeError of string

let rec typeof ctx term =
    match term with
    | True
    | False -> Bool
    | String _ -> TString
    | Float _ -> TFloat
    | Unit -> TUnit
    | As(term, ty) ->
        if typeof ctx term = ty then
            ty
        else
            raise (TypeError "Cast to incompatible type")
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

    | Bin { left = left; op = op; right = right } ->
        let tleft = typeof ctx left
        let tright = typeof ctx right

        match tleft, op, tright with
        | TFloat, Equal, TFloat -> Bool
        | TFloat, _, TFloat -> TFloat
        | TString, Add, TString -> TString
        | TString, Equal, TString -> Bool
        | _ -> raise (TypeError "invalid type for binary experssion")

    | Var v -> get ctx v
    | Abs { type_ = type_; body = body } ->
        let new_ctx = add ctx (shift_ty 1 type_)
        Fn(type_, typeof new_ctx body)
    | Apply { callee = callee; arg = arg } ->
        let t_callee = typeof ctx callee
        let t_arg = typeof ctx arg

        match t_callee with
        | Fn(t_param, body) when t_param = t_arg -> body
        | Fn(_, _) -> raise (TypeError "parameter type mismatch")
        | _ -> raise (TypeError "callee not a function")

    | Let { value = value; body = body } ->
        let new_ctx = add ctx (shift_ty 1 (typeof ctx value))
        typeof new_ctx body

    | Record r -> TRecord(Array.map (fun (name, term) -> (name, typeof ctx term)) r)

    | Proj(obj, key) ->
        match typeof ctx obj with
        | TRecord t ->
            match Array.tryFind (fun (t, _) -> t = key) t with
            | Some(_, ty) -> ty
            | None -> raise (TypeError $"ket {key} not found in proj")
        | _ -> raise (TypeError "proj object not a record")

    | Tag { tag = tag
            value = value
            type_ = type_ } ->
        match type_ with
        | TVariant t ->
            match Array.tryFind (fun (name, _) -> name = tag) t with
            | Some(_, t) ->
                if t = typeof ctx value then
                    type_
                else
                    raise (TypeError "wrong type of value provided for tag")
            | None -> raise (TypeError "no matching tag found")
        | _ -> raise (TypeError "variant type expeced in tag")

    | Case { test = test; branch = branch } ->
        let type_ = typeof ctx test

        match type_ with
        | TVariant variant ->
            if Array.length variant <> Array.length branch then
                raise (TypeError "incomplete cover of variant")
            else
                let check (state, has) branch =
                    let { tag = tag; body = body } = branch

                    if Set.contains tag has then
                        raise (TypeError "found duplicate tag")

                    let has = Set.add tag has

                    match Array.tryFind (fun (name, _) -> name = tag) variant with
                    | Some(_, type_) ->
                        let new_ctx = add ctx (shift_ty 1 type_)
                        let body_type = typeof new_ctx body

                        match state, body_type with
                        | Some s, t when s = t -> Some t, has
                        | Some _, _ -> raise (TypeError "case branch type mismatch")
                        | None, t -> Some t, has
                    | None -> raise (TypeError "unknown tag found in case")

                match Array.fold check (None, Set.empty) branch with
                | Some t, _ -> t
                | _ -> raise (TypeError "case branch cannot be empty")

        | _ -> raise (TypeError "guard of case not a variant")

    | Fix t ->
        let t = typeof ctx t

        match t with
        | Fn(arg, res) when arg = shift_ty -1 res -> arg
        | Fn _ -> raise (TypeError "should pass a recusive function")
        | _ -> raise (TypeError "should pass a function to fix")

    | Fold(ty, term) ->
        match resolve ctx ty with
        | TRecursive t ->
            let real_ty = typeof ctx term
            let unfold = remove_rec t (TId 0)

            if real_ty = unfold then
                ty
            else
                raise (TypeError "fold to an irrelevant type")
        | _ -> raise (TypeError "can only fold a recursive type")
    | Unfold(ty, term) ->
        let real_ty = typeof ctx term

        if real_ty = ty then
            match resolve ctx ty with
            | TRecursive t -> remove_rec t (TId 0)
            | _ -> raise (TypeError "can only unfold a recursive type")
        else
            raise (TypeError "unfold to an irrelevant type")

exception RuntimeError of string

type Rtag =
    { tag: string; value: Res; type_: Type }

and Res =
    | RBool of bool
    | RString of string
    | RFloat of float
    | RUnit
    | RRecord of (string * Res)[]
    | RAbs of Abs
    | RTag of Rtag

let rec to_term r =
    match r with
    | RBool true -> True
    | RBool false -> False
    | RString s -> String s
    | RFloat f -> Float f
    | RUnit -> Unit
    | RRecord r -> Record(Array.map (fun (name, r) -> name, to_term r) r)
    | RAbs a -> Abs a
    | RTag { tag = tag
             value = value
             type_ = type_ } ->
        Tag
            { tag = tag
              value = to_term value
              type_ = type_ }

let walk onvar term =
    let rec walk_real c term =
        match term with
        | True
        | False
        | Unit
        | Float _
        | String _ -> term
        | As(a, t) -> As(walk_real c a, t)
        | If { test = test; cons = cons; alt = alt } ->
            If
                { test = walk_real c test
                  cons = walk_real c cons
                  alt = walk_real c alt }
        | Bin { left = left; op = op; right = right } ->
            Bin
                { left = walk_real c left
                  op = op
                  right = walk_real c right }
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
        | Record r -> Record(Array.map (fun (key, value) -> (key, walk_real c value)) r)
        | Proj(obj, key) -> Proj(walk_real c obj, key)
        | Tag t ->
            Tag
                { tag = t.tag
                  value = walk_real c t.value
                  type_ = t.type_ }
        | Case { test = test; branch = branch } ->
            Case
                { test = walk_real c test
                  branch =
                    Array.map
                        (fun (b: CaseBranch) ->
                            { tag = b.tag
                              body = walk_real (c + 1) b.body })
                        branch }

        | Fix t -> Fix(walk_real c t)
        | Fold(ty, term) -> Fold(ty, walk_real c term)
        | Unfold(ty, term) -> Unfold(ty, walk_real c term)

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
    | String s -> RString s
    | Float f -> RFloat f
    | As(term, _) -> eval ctx term
    | Var v -> get ctx v
    | Abs a -> RAbs a
    | Apply { callee = callee; arg = arg } ->
        let callee = eval ctx callee

        match callee with
        | RAbs a ->
            let arg = eval ctx arg |> to_term

            eval_call a.body arg |> eval ctx
        | _ -> raise (RuntimeError "callee not a function")

    | Let { body = body; value = value } ->
        let value = eval ctx value |> to_term

        eval_call body value |> eval ctx

    | If { test = test; cons = cons; alt = alt } ->
        match eval ctx test with
        | RBool b -> eval ctx (if b then cons else alt)
        | _ -> raise (RuntimeError "guard of conditional not a boolean")

    | Bin { left = left; op = op; right = right } ->
        let left = eval ctx left
        let right = eval ctx right

        match left, op, right with
        | RString ls, Add, RString rs -> RString(ls + rs)
        | RString ls, Equal, RString rs -> RBool(ls = rs)
        | RFloat lf, op, RFloat rf ->
            match op with
            | Add -> RFloat(lf + rf)
            | Minus -> RFloat(lf - rf)
            | Multiply -> RFloat(lf * rf)
            | Divide -> RFloat(lf / rf)
            | Equal -> RBool(lf = rf)
        | _ -> raise (RuntimeError "invalid type for binary experssion")

    | Record r -> RRecord(Array.map (fun (name, term) -> (name, eval ctx term)) r)
    | Tag t ->
        RTag
            { tag = t.tag
              value = eval ctx t.value
              type_ = t.type_ }
    | Proj(obj, key) ->
        match eval ctx obj with
        | RRecord t ->
            match Array.tryFind (fun (t, _) -> t = key) t with
            | Some(_, r) -> r
            | None -> raise (RuntimeError $"ket {key} not found in proj")
        | _ -> raise (RuntimeError "proj object not a record")
    | Case { test = test; branch = branch } ->
        let test = eval ctx test

        match test with
        | RTag t ->
            match Array.tryFind (fun (b: CaseBranch) -> b.tag = t.tag) branch with
            | Some b -> eval_call b.body (to_term t.value) |> eval ctx
            | _ -> raise (RuntimeError "unknown tag found in case")

        | _ -> raise (RuntimeError "guard of case not a variant")

    | Fix t ->
        let t = eval ctx t |> to_term

        match t with
        | Abs a -> eval_call a.body (Fix t) |> eval ctx
        | _ -> raise (RuntimeError "should pass a function to fix")
    // it should be `unfold [S] (fold [T] v1) -> v1` but this is easier
    | Fold(_, term) -> eval ctx term
    | Unfold(_, term) -> eval ctx term

let rec to_string res =
    match res with
    | RUnit -> "()"
    | RString s -> $"\"{s}\""
    | RBool true -> "true"
    | RBool false -> "false"
    | RFloat f -> string f
    | RRecord r ->
        Array.fold (fun state (name, res) -> state + $" {name}: {to_string res}\n") "{\n" r
        + "}"
    | RAbs _ -> "FUNCTION"
    | RTag t ->
        match t.value with
        | RUnit -> t.tag
        | v -> $"{t.tag}({to_string v})"

let print_res type_ctx ctx term =
    try
        let _ = typeof type_ctx term
        let res = eval ctx term

        printfn "Result: %s" (to_string res)
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

// type Tree = Nil | Node { left: Tree; right: Tree; value: Float }
let tree_body =
    TVariant(
        [| ("Nil", TUnit)
           ("Node", TRecord [| ("left", TId 0); ("right", TId 0); ("value", TFloat) |]) |]
    )

let tree = TRecursive tree_body

let nil =
    Fold(
        TId 0,
        Tag
            { tag = "Nil"
              value = Unit
              type_ = tree_body }
    )

let node l r v =
    Fold(
        TId 0,
        Tag
            { tag = "Node"
              value = Record [| ("left", l); ("right", r); ("value", v) |]
              type_ = tree_body }
    )

let leaf = node nil nil

let test_tree =
    node (node (leaf (Float 4)) (leaf (Float 5)) (Float 2)) (leaf (Float 3)) (Float 1)

let sum =
    Abs
        { type_ = Fn(TId 0, TFloat)
          body =
            Abs
                { type_ = TId 1
                  body =
                    Case
                        { test = Unfold(TId 2, Var 0)
                          branch =
                            [| { tag = "Nil"; body = Float 0 }
                               { tag = "Node"
                                 body =
                                   Bin
                                       { left =
                                           Apply
                                               { callee = Var 2
                                                 arg = Proj(Var 0, "left") }
                                         op = Add
                                         right =
                                           Bin
                                               { left =
                                                   Apply
                                                       { callee = Var 2
                                                         arg = Proj(Var 0, "right") }
                                                 op = Add
                                                 right = Proj(Var 0, "value") } } } |] } } }

print_res [| tree |] [||] (Apply { callee = Fix sum; arg = test_tree })
