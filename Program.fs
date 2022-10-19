type IfExpr = { test: Expr; cons: Expr; alt: Expr }

and Expr =
    | True
    | False
    | Zero
    | If of IfExpr
    | Succ of Expr
    | Pred of Expr
    | IsZero of Expr

module Res =
    type T =
        | Bool of bool
        | Int of int

        member this.to_int =
            match this with
            | Bool true -> 1
            | Bool false -> 0
            | Int i -> i

        member this.to_bool =
            match this with
            | Bool b -> b
            | Int i -> i > 0

        member this.to_str =
            match this with
            | Bool b -> string b
            | Int i -> string i

open Res

let rec eval expr =
    match expr with
    | True -> Bool true
    | False -> Bool false
    | Zero -> Int 0
    | Succ e -> Int((eval (e)).to_int + 1)
    | Pred e -> Int((eval (e)).to_int - 1)
    | If i ->
        if (eval (i.test)).to_bool then
            eval (i.cons)
        else
            eval (i.alt)
    | IsZero e -> Bool((eval (e)).to_int = 0)

printfn
    "%s"
    (eval (
        If(
            { test = IsZero(Zero)
              cons = Zero
              alt = Succ(Zero) }
        )
    ))
        .to_str
