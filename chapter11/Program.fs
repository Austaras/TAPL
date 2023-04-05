// STLC with various useful extensions

type Type =
    | Bool
    | TString
    | TFloat
    | Custom of int
    | TUnit
    | TRecord of (string * Type)[]
    | TVariant of (string * Type)[]
    | Fn of Type * Type

let add ctx v = Array.append ctx [| v |]

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

let rec resolve ctx ty =
    let map (name, t) = (name, resolve ctx t)

    match ty with
    | Custom c -> resolve ctx (get ctx c)
    | Fn(t1, t2) -> Fn(resolve ctx t1, resolve ctx t2)
    | TRecord t -> TRecord(Array.map map t)
    | TVariant t -> TVariant(Array.map map t)
    | _ -> ty

let rec equal ctx t1 t2 =
    let t1 = resolve ctx t1
    let t2 = resolve ctx t2
    t1 = t2

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

exception TypeError of string

let rec typeof ctx term =
    match term with
    | True
    | False -> Bool
    | String _ -> TString
    | Float _ -> TFloat
    | Unit -> TUnit
    | As(term, ty) ->
        if equal ctx (typeof ctx term) ty then
            ty
        else
            raise (TypeError "Cast to incompatible type")
    | If { test = test; cons = cons; alt = alt } ->
        if equal ctx (typeof ctx test) Bool then
            let t_cons = typeof ctx cons
            let t_alt = typeof ctx alt

            if equal ctx t_cons t_alt then
                t_cons
            else
                raise (TypeError "arms of conditional have different types")
        else
            raise (TypeError "guard of conditional not a boolean")

    | Bin { left = left; op = op; right = right } ->
        let tleft = resolve ctx (typeof ctx left)
        let tright = resolve ctx (typeof ctx right)

        match tleft, op, tright with
        | TFloat, Equal, TFloat -> Bool
        | TFloat, _, TFloat -> TFloat
        | TString, Add, TString -> TString
        | TString, Equal, TString -> Bool
        | _ -> raise (TypeError "invalid type for binary experssion")

    | Var v -> get ctx v
    | Abs { type_ = type_; body = body } ->
        let new_ctx = add ctx (resolve ctx type_)
        Fn(type_, typeof new_ctx body)
    | Apply { callee = callee; arg = arg } ->
        let t_callee = resolve ctx (typeof ctx callee)
        let t_arg = typeof ctx arg

        match t_callee with
        | Fn(t_param, body) when equal ctx t_param t_arg -> body
        | Fn(_, _) -> raise (TypeError "parameter type mismatch")
        | _ -> raise (TypeError "callee not a function")

    | Let { value = value; body = body } ->
        let new_ctx = add ctx (typeof ctx value)
        typeof new_ctx body

    | Record r -> TRecord(Array.map (fun (name, term) -> (name, typeof ctx term)) r)

    | Proj(obj, key) ->
        match typeof ctx obj with
        | TRecord t ->
            match Array.tryFind (fun (t, _) -> t = key) t with
            | Some(_, ty) -> ty
            | None -> raise (TypeError $"key {key} not found in proj")
        | _ -> raise (TypeError "proj object not a record")

    | Tag { tag = tag
            value = value
            type_ = type_ } ->
        let type_ = resolve ctx type_

        match type_ with
        | TVariant t ->
            match Array.tryFind (fun (name, _) -> name = tag) t with
            | Some(_, t) ->
                if equal ctx t (typeof ctx value) then
                    type_
                else
                    raise (TypeError "wrong type of value provided for tag")
            | None -> raise (TypeError "no matching tag found")
        | _ -> raise (TypeError "variant type expeced in tag")

    | Case { test = test; branch = branch } ->
        let type_ = resolve ctx (typeof ctx test)

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
                        let new_ctx = add ctx type_
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
        let t = resolve ctx (typeof ctx t)

        match t with
        | Fn(arg, res) when equal ctx arg res -> arg
        | Fn _ -> raise (TypeError "should pass a recusive function")
        | _ -> raise (TypeError "should pass a function to fix")

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
            | None -> raise (RuntimeError $"key {key} not found in proj")
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

print_res [||] [||] (String "sadas")
print_res [||] [||] (Proj((Record [| "x", Record [| "y", Float 1 |] |]), "x"))

print_res
    [| Fn(TUnit, TUnit) |]
    [||]
    (Apply
        { callee =
            Abs
                { type_ = Custom 0
                  body = Apply { callee = Var(0); arg = Unit } }
          arg = Abs { type_ = TUnit; body = Var(0) } })

print_res
    [||]
    [||]
    (Let
        { value = Float 0.4
          body =
            Apply
                { callee =
                    Abs
                        { type_ = TFloat
                          body =
                            Bin
                                { left = Var 0
                                  op = Multiply
                                  right = Var 1 } }
                  arg = Var 0 } })

print_res
    [||]
    [||]
    (Apply
        { callee =
            Abs
                { type_ = TFloat
                  body =
                    Let
                        { value = Float 0.3
                          body =
                            Bin
                                { left = Var 0
                                  op = Add
                                  right = Var 1 } } }
          arg = Float 0.2 })

print_res
    [||]
    [||]
    (Let
        { value =
            Tag
                { tag = "Bool"
                  value = True
                  type_ = TVariant [| ("Number", TFloat); ("Bool", Bool) |] }
          body =
            Case
                { test = Var 0
                  branch =
                    [| { tag = "Number"; body = Var 0 }
                       { tag = "Bool"
                         body =
                           If
                               { test = Var 0
                                 cons = Float 15
                                 alt = Float 10 } } |] } })

// power
print_res
    [||]
    [||]
    (Apply
        { callee =
            Apply
                { callee =
                    Fix(
                        Abs
                            { type_ = Fn(TFloat, Fn(TFloat, TFloat))
                              body =
                                Abs
                                    { type_ = TFloat
                                      body =
                                        Abs
                                            { type_ = TFloat
                                              body =
                                                If
                                                    { test =
                                                        Bin
                                                            { left = Var 0
                                                              op = Equal
                                                              right = Float 0 }
                                                      cons = Float 1
                                                      alt =
                                                        Bin
                                                            { left = Var 1
                                                              op = Multiply
                                                              right =
                                                                Apply
                                                                    { callee = Apply { callee = Var(2); arg = Var(1) }
                                                                      arg =
                                                                        Bin
                                                                            { left = Var(0)
                                                                              op = Minus
                                                                              right = Float 1 } } } } } } }
                    )
                  arg = Float 5 }
          arg = Float(5) })
