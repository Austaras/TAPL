// Untyped Lambda-Calculus

type Apply = { arg: Term; callee: Term }
and Abs = { name: string; body: Term }

and Term =
    | Var of int // de Bruijn index
    | Abs of Abs
    | Apply of Apply

let pickfreshname name ctx =
    let rec pick_inner name ctx suffix =
        let new_name = name + if suffix < 0 then "" else string suffix

        if Array.contains new_name ctx then
            pick_inner name ctx (suffix + 1)
        else
            new_name

    let name = pick_inner name ctx -1

    Array.append ctx [| name |], name

let index2name v ctx =
    Array.get ctx (Array.length ctx - v - 1)


let to_string ctx term =
    let rec to_string ctx term may_bracket =
        match term with
        | Apply a ->
            if may_bracket then "(" else ""
            + $"{to_string ctx a.callee true} {to_string ctx a.arg true}"
            + if may_bracket then ")" else ""
        | Abs a ->
            let (new_ctx, name) = pickfreshname a.name ctx

            if may_bracket then "(" else ""
            + $"λ{name} {to_string new_ctx a.body false}"
            + if may_bracket then ")" else ""
        | Var v -> $"{index2name v ctx}"

    to_string ctx term false

printfn "Input: %s" (to_string [| "x" |] (Abs { name = "x"; body = Var 0 }))

let ctx = [| "b" |]

let term =
    Apply
        { callee =
            Apply
                { callee = Abs { name = "x"; body = Var 0 }
                  arg = Abs { name = "x"; body = Var 1 } }
          arg = Abs { name = "x"; body = Var 0 } }

printfn "Input: %s" (to_string ctx term)

type Shift = { d: int; c: int }

let rec shift s term =
    match term with
    | Apply a ->
        Apply
            { callee = shift s a.callee
              arg = shift s a.arg }
    | Abs a ->
        Abs
            { name = a.name
              body = shift { d = s.d; c = s.c + 1 } a.body }
    | Var v -> Var(if v >= s.c then v + s.d else v)

type Substitution = { j: int; s: Term }

let rec substitute s term =
    match term with
    | Apply a ->
        Apply
            { callee = substitute s a.callee
              arg = substitute s a.arg }
    | Abs a ->
        Abs
            { name = a.name
              body =
                substitute
                    { j = s.j + 1
                      s = shift { d = 1; c = 0 } s.s }
                    a.body }
    | Var v -> if v = s.j then s.s else Var(v)

let eval_call body arg =
    let arg = shift { d = 1; c = 0 } arg
    let term = substitute { j = 0; s = arg } body

    shift { d = -1; c = 0 } term

let rec eval term =
    match term with
    | Apply { callee = Abs callee
              arg = Abs _ as arg } -> eval_call callee.body arg |> eval
    | Apply { callee = Abs _ as callee; arg = arg } -> Apply { callee = callee; arg = eval arg } |> eval
    | Apply a -> Apply { callee = eval a.callee; arg = a.arg } |> eval
    | _ -> term

printfn "Result small step: %s" (to_string ctx (eval term))

let rec eval_big_step term =
    match term with
    | Apply { callee = callee; arg = arg } ->
        match (eval_big_step callee, eval_big_step arg) with
        | (Abs callee, Abs arg) -> eval_call callee.body (Abs arg) |> eval_big_step
        | (_, _) -> term
    | _ -> term

printfn "Result big step: %s" (to_string ctx (eval_big_step term))
