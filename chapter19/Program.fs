// chapter 18 but with native class
// all classes are pre defined and nested classes are prohibited

type Type =
    | Bottom
    | Bool
    | Nat
    | TClass of string

exception TypeError of string

let get ctx v =
    Array.get ctx (Array.length ctx - v - 1)

let add ctx v = Array.append ctx [| v |]

type Class =
    { name: string
      super: string
      field: Map<string, Type>
      method: Map<string, Method> }

and Method =
    { param: Type
      body: Term
      return_t: Type }

and Invoke =
    { obj: Term; method: string; arg: Term }

and Obj =
    { class_name: string
      field: Map<string, Term> }

and If = { test: Term; cons: Term; alt: Term }

and Term =
    | True
    | False
    | Zero
    | Succ of Term
    | Pred of Term
    | IsZero of Term
    | If of If
    | Let of Term * Term
    | Var of int
    | Invoke of Invoke
    | Obj of Obj
    | As of Term * Type
    | Field of Term * string
    | This
    | Super

// <: but : cannot be used in an operator
let (<+) (classes: Map<string, Class>) a b =
    let rec sub_class_of a b =
        if a = b then
            true
        else
            let a_class = classes[a]

            match Map.tryFind a_class.super classes with
            | Some s -> sub_class_of s.name b
            | None -> false

    match a, b with
    | a, b when a = b -> true
    | _, TClass b when b = "Object" -> true
    | Bottom, _ -> true
    | TClass a, TClass b -> sub_class_of a b
    | _, _ -> false

// join
let (<|>) classes a b =
    match a, b with
    | a, b when (<+) classes a b -> b
    | a, b when (<+) classes b a -> a
    | TClass a, TClass b ->
        let a = classes[a]
        let b = classes[b]

        let rec all_super set name =
            let set = Set.add name set
            let cl = classes[name]
            if cl.super = "" then set else all_super set cl.super

        let a_super = all_super Set.empty a.name

        let rec find_super set name =
            if Set.contains name set then
                name
            else
                let cl = classes[name]
                find_super set cl.super

        TClass(find_super a_super b.name)
    | _, _ -> TClass "Object"

let rec typeof ctx this classes term =
    match term with
    | True
    | False -> Bool
    | Zero -> Nat
    | Succ n
    | Pred n ->
        if typeof ctx this classes n = Nat then
            Nat
        else
            raise (TypeError "succ/pred on a non number")
    | IsZero n ->
        if typeof ctx this classes n = Nat then
            Bool
        else
            raise (TypeError "IsZero on a non number")
    | Var v -> get ctx v
    | If { test = test; cons = cons; alt = alt } ->
        if typeof ctx this classes test = Bool then
            (<|>) classes (typeof ctx this classes cons) (typeof ctx this classes alt)
        else
            raise (TypeError "guard of conditional not a boolean")
    | Let(value, body) ->
        let ty = typeof ctx this classes value
        let ctx = add ctx ty

        typeof ctx this classes body
    | Obj o ->
        let class_ty = classes[o.class_name]

        if Map.count class_ty.field <> Map.count o.field then
            raise (TypeError "provide more/less field than required")
        else
            let checker name value =
                let field_type = typeof ctx this classes value

                if not ((<+) classes field_type class_ty.field[name]) then
                    raise (TypeError "provide wrong value for class field")

            Map.iter checker o.field

        TClass o.class_name
    | Invoke i ->
        let obj_type = typeof ctx this classes i.obj

        match obj_type with
        | TClass t ->
            let class_type = classes[t]

            match Map.tryFind i.method class_type.method with
            | Some m ->
                let arg_type = typeof ctx this classes i.arg

                if (<+) classes arg_type m.param then
                    m.return_t
                else
                    raise (TypeError "method arg type mismatch")
            | None -> raise (TypeError $"non such method on class {class_type.name}")
        | _ -> raise (TypeError "invoke method on a primitive type")
    | Field(obj, key) ->
        let obj_type = typeof ctx this classes obj

        match obj_type with
        | TClass t ->
            let class_type = classes[t]

            match Map.tryFind key class_type.field with
            | Some ty -> ty
            | None -> raise (TypeError $"non such field on class {class_type.name}")
        | _ -> raise (TypeError "access field on a primitive type")
    | This -> TClass this
    | Super -> TClass classes[this].super
    | As(term, ty) ->
        let real_type = typeof ctx this classes term

        if (<+) classes real_type ty || (<+) classes ty real_type then
            ty
        else
            raise (TypeError "cast to irrelevant type")

let typeof_class ctx classes =
    let extend child parent =
        let folder state name value = Map.add name value state

        Map.fold folder parent child

    let folder (state: Map<string, Class>) klass =
        let super =
            match Map.tryFind klass.super state with
            | Some t -> t
            | None -> raise (TypeError "super class not found")

        let klass =
            { name = klass.name
              super = klass.super
              field = extend klass.field super.field
              method = extend klass.method super.method }

        let state = Map.add klass.name klass state

        let check_field name f =
            match Map.tryFind name super.field with
            | Some parent ->
                if not ((<+) state f parent) then
                    raise (TypeError "invalid override field type mismatch")
            | None -> ()

        Map.iter check_field klass.field

        let check_method name m =
            let ctx = add ctx m.param
            let real_type = typeof ctx klass.name state m.body

            if not ((<+) state real_type m.return_t) then
                printfn "%s %s %s" klass.name (string state) (string m.body)
                printfn "%s %s" (string real_type) (string m.return_t)
                raise (TypeError "return type of method mismatch")

            match Map.tryFind name super.method with
            | Some parent ->
                if not ((<+) state m.return_t parent.return_t && (<+) state parent.param m.param) then
                    raise (TypeError "invalid override method type mismatch")
            | None -> ()

        Map.iter check_method klass.method

        state

    Array.fold
        folder
        Map[("Object",
             { name = "Object"
               super = ""
               field = Map.empty
               method = Map.empty })]
        classes

exception RuntimeError of string

type RObj =
    { class_name: string
      field: Map<string, Res> }

and Res =
    | RBool of bool
    | RNat of int
    | RObj of RObj

let rec to_term r =
    match r with
    | RBool true -> True
    | RBool false -> False
    | RNat n -> if n = 0 then Zero else n - 1 |> RNat |> to_term |> Succ
    | RObj o ->
        Obj
            { class_name = o.class_name
              field = Map.map (fun _ value -> to_term value) o.field }

let walk onvar term =
    let rec walk_real c term =
        match term with
        | True
        | False
        | Zero -> term
        | Succ t -> Succ(walk_real c t)
        | Pred t -> Pred(walk_real c t)
        | IsZero t -> IsZero(walk_real c t)
        | If { test = test; cons = cons; alt = alt } ->
            If
                { test = walk_real c test
                  cons = walk_real c cons
                  alt = walk_real c alt }
        | Let(value, body) -> Let(walk_real c value, walk_real (c + 1) body)
        | Var v -> onvar v c
        | Invoke i ->
            Invoke
                { obj = walk_real c i.obj
                  method = i.method
                  arg = walk_real c i.arg }
        | Obj o ->
            Obj
                { class_name = o.class_name
                  field = Map.map (fun _ term -> walk_real c term) o.field }
        | Field(obj, key) -> Field(walk_real c obj, key)
        | This -> raise (RuntimeError "unsubstitued this")
        | Super -> raise (RuntimeError "unsubstitued this")
        | As(term, ty) -> As(walk_real c term, ty)

    walk_real 0 term

let shift d =
    walk (fun v c -> Var(if v >= c then v + d else v))

let substitute s =
    walk (fun v c -> if v = c then shift c s else Var v)

let eval_call body arg =
    let arg = shift 1 arg
    let term = substitute arg body

    shift -1 term

let eval ctx (classes: Map<string, Class>) term =
    let rec eval_real ctx this term =
        match term with
        | True -> RBool true
        | False -> RBool false
        | Zero -> RNat 0
        | Succ n ->
            match eval_real ctx this n with
            | RNat n -> RNat(n + 1)
            | _ -> raise (RuntimeError "succ on a non number")
        | Pred n ->
            match eval_real ctx this n with
            | RNat 0 -> RNat 0
            | RNat n -> RNat(n - 1)
            | _ -> raise (RuntimeError "pred on a non number")
        | IsZero n ->
            match eval_real ctx this n with
            | RNat 0 -> RBool true
            | RNat _ -> RBool false
            | _ -> raise (RuntimeError "iszero on a non number")
        | Var v -> get ctx v

        | If { test = test; cons = cons; alt = alt } ->
            let test = eval_real ctx this test

            match test with
            | RBool b -> eval_real ctx this (if b then cons else alt)
            | _ -> raise (RuntimeError "guard of conditional not a boolean")
        | Let(value, body) ->
            let value = eval_real ctx this value
            eval_call body (to_term value) |> eval_real ctx this
        | Obj o ->
            let mapper _ value = eval_real ctx this value

            RObj
                { class_name = o.class_name
                  field = Map.map mapper o.field }
        | Invoke i ->
            match eval_real ctx this i.obj |> to_term with
            | Obj o ->
                let arg = eval_real ctx this i.arg
                let klass = classes[o.class_name]
                let body = klass.method[i.method].body

                let rec eval_method term =
                    match term with
                    | True
                    | False
                    | Zero
                    | Var _ -> term
                    | Succ t -> Succ(eval_method t)
                    | Pred t -> Pred(eval_method t)
                    | IsZero t -> IsZero(eval_method t)
                    | If { test = test; cons = cons; alt = alt } ->
                        If
                            { test = eval_method test
                              cons = eval_method cons
                              alt = eval_method alt }
                    | Let(value, body) -> Let(eval_method value, eval_method body)
                    | Invoke i ->
                        Invoke
                            { obj = eval_method i.obj
                              method = i.method
                              arg = eval_method i.arg }
                    | Obj o ->
                        Obj
                            { class_name = o.class_name
                              field = Map.map (fun _ term -> eval_method term) o.field }
                    | Field(obj, key) -> Field(eval_method obj, key)
                    | This -> Obj o
                    | Super ->
                        Obj
                            { class_name = klass.super
                              field = o.field }
                    | As(term, ty) -> As(eval_method term, ty)

                eval_call (eval_method body) (to_term arg) |> eval_real ctx this
            | _ -> raise (RuntimeError "invoke method on a primitive type")
        | Field(obj, key) ->
            match eval_real ctx this obj with
            | RObj o -> o.field[key]
            | _ -> raise (RuntimeError "access field on a primitive type")
        | This -> raise (RuntimeError "this keyword cannot be in top level")
        | Super -> raise (RuntimeError "super keyword cannot be in top level")
        | As(term, ty) ->
            let res = eval_real ctx this term

            let real_type =
                match res with
                | RBool _ -> Bool
                | RNat _ -> Nat
                | RObj o -> TClass o.class_name

            if (<+) classes real_type ty then
                res
            else
                raise (RuntimeError "Cast to wrong type")

    eval_real ctx "Object" term

let rec to_string res =
    match res with
    | RBool true -> "true"
    | RBool false -> "false"
    | RNat n -> string n
    | RObj r ->
        let folder state name r = state + $" {name}: {to_string r}\n"
        Map.fold folder $"{r.class_name} {{\n" r.field + "}"

let print_res classes term =
    try
        let classes = typeof_class [||] classes
        let _ = typeof [||] "Object" classes term
        let res = eval [||] classes term

        printfn "Result: %s" (to_string res)
    with
    | TypeError t -> printfn "Type error: %s" t
    | RuntimeError t -> printfn "Runtime error: %s" t

let top =
    Obj
        { class_name = "Object"
          field = Map.empty }

// class Counter extends Object {
//     Nat x;
//     Nat get(_: Object) { return this.x; }
//     Counter set(y: Nat) { return Counter { x: y };}
//     Counter inc(_: Object) { return this.set(this.get(_) + 1)}
// }
let counter =
    { name = "Counter"
      super = "Object"
      field = Map[("x", Nat)]
      method =
        Map[("get",
             { param = TClass "Object"
               body = Field(This, "x")
               return_t = Nat })

            ("set",
             { param = Nat
               body =
                 Obj
                     { class_name = "Counter"
                       field = Map[("x", Var 0)] }
               return_t = TClass "Counter" })

            ("inc",
             { param = TClass "Object"
               body =
                 Invoke
                     { obj = This
                       method = "set"
                       arg =
                         Succ(
                             Invoke
                                 { obj = This
                                   method = "get"
                                   arg = top }
                         ) }
               return_t = TClass "Counter" })] }

// class BackupCounter extends Counter {
//     Nat r;
//     BackupCounter set(y: Nat) { return BackupCounter { r: super.get(_); x: y };}
//     BackupCounter reset(_: Object) { return this.set(this.r) }
// }
let backup_counter =
    { name = "BackupCounter"
      super = "Counter"
      field = Map[("r", Nat)]
      method =
        Map[("set",
             { param = Nat
               body =
                 Obj
                     { class_name = "BackupCounter"
                       field =
                         Map[("x", Var 0)

                             ("r",
                              Invoke
                                  { obj = Super
                                    method = "get"
                                    arg = top })] }
               return_t = TClass "BackupCounter" })

            ("reset",
             { param = TClass "Object"
               body =
                 Invoke
                     { obj = This
                       method = "set"
                       arg = Field(This, "r") }
               return_t = TClass "BackupCounter" })] }

// BackupCounter { x: 3; r: 0 }.inc().reset().get()
print_res
    [| counter; backup_counter |]
    (Invoke
        { obj =
            Invoke
                { obj =
                    As(
                        Invoke
                            { obj =
                                Obj
                                    { class_name = "BackupCounter"
                                      field =
                                        Map[("x", Succ(Succ(Succ Zero)))
                                            ("r", Zero)] }
                              method = "inc"
                              arg = top },
                        TClass "BackupCounter"
                    )
                  method = "reset"
                  arg = top }
          method = "get"
          arg = top })

// class AddCounter extends Counter {
//     AddCounter add(y: Nat) { if y = 0 then this else this.inc().add(y - 1) }
// }
let add_counter =
    { name = "AddCounter"
      super = "Counter"
      field = Map.empty
      method =
        Map[("set",
             { param = Nat
               body =
                 Obj
                     { class_name = "AddCounter"
                       field = Map[("x", Var 0)] }
               return_t = TClass "AddCounter" })

            ("add",
             { param = Nat
               body =
                 If
                     { test = IsZero(Var 0)
                       cons = This
                       alt =
                         Invoke
                             { obj =
                                 As(
                                     Invoke
                                         { obj = This
                                           method = "inc"
                                           arg = top },
                                     TClass "AddCounter"
                                 )
                               method = "add"
                               arg = Pred(Var 0) } }
               return_t = TClass "AddCounter" })] }

// (if true then BackupCounter { x: 2, r: 0 } else AddCounter { x: 0 }).inc().inc().get()
print_res
    [| counter; backup_counter; add_counter |]
    (Invoke
        { obj =
            Invoke
                { obj =
                    Invoke
                        { obj =
                            If
                                { test = True
                                  cons =
                                    Obj
                                        { class_name = "BackupCounter"
                                          field =
                                            Map[("x", Succ(Succ Zero))
                                                ("r", Zero)] }
                                  alt =
                                    Obj
                                        { class_name = "AddCounter"
                                          field = Map[("x", Succ Zero)] } }
                          method = "inc"
                          arg = top }
                  method = "inc"
                  arg = top }
          method = "get"
          arg = top })

// AddCounter { x: 4 }).add(3).get()
print_res
    [| counter; backup_counter; add_counter |]
    (Invoke
        { obj =
            Invoke
                { obj =
                    Obj
                        { class_name = "AddCounter"
                          field = Map[("x", Succ(Succ(Succ(Succ Zero))))] }
                  method = "add"
                  arg = Succ(Succ(Succ Zero)) }
          method = "get"
          arg = top })
