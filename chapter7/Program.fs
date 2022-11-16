type 't Term =
    | Var of int
    | Abs of 't
    | Apply of 't * 't
