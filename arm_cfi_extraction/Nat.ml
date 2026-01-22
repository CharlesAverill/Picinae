
(** val add : int -> int -> int **)

let rec add n m =
  match n with
  | 0 -> m
  | p -> (add p m)
