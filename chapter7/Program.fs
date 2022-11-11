type 't Term =
    | Var of int64
    | Abs of 't
    | Apply of 't * 't
