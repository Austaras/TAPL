// Arithmetic Expressions
// This is actually the big step version

type IfExpr = { test: Term; cons: Term; alt: Term }

and Term =
    | True
    | False
    | Zero
    | If of IfExpr
    | Succ of Term
    | Pred of Term
    | IsZero of Term

type Res =
    | Bool of bool
    | Int of int

exception TypeError of string

let rec eval expr =
    match expr with
    | True -> Bool true
    | False -> Bool false
    | Zero -> Int 0
    | Succ e ->
        Int(
            match eval e with
            | Bool _ -> raise (TypeError "Cannot success a bool value")
            | Int i -> i + 1
        )
    | Pred e ->
        Int(
            match eval e with
            | Bool _ -> raise (TypeError "Cannot predecess a bool value")
            | Int 0 -> 0
            | Int i -> i - 1
        )
    | If i ->
        match eval i.test with
        | Bool true -> eval i.cons
        | Bool false -> eval i.alt
        | Int _ -> raise (TypeError "Cannot use a int value in if")
    | IsZero e ->
        Bool(
            match eval e with
            | Bool _ -> raise (TypeError "Cannot compare a bool value with zero")
            | Int 0 -> true
            | Int i -> false
        )

let print_res term =
    try
        match eval term with
        | Bool b -> printfn "Bool: %b" b
        | Int i -> printfn "Int: %i" i
    with TypeError(str) ->
        printfn "Error: %s" str

print_res (
    If(
        { test = IsZero(Succ(Zero))
          cons = Zero
          alt = Succ(Pred(Succ(Zero))) }
    )
)

print_res (IsZero(False))
