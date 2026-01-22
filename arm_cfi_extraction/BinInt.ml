open BinNums
open BinPos
open Datatypes

module Z =
 struct
  (** val double : int -> int **)

  let double = function
  | 0 -> 0
  | p -> (Coq_xO p)
  | (~-) p -> (~-) (Coq_xO p)

  (** val succ_double : int -> int **)

  let succ_double = function
  | 0 -> Coq_xH
  | p -> (Coq_xI p)
  | (~-) p -> (~-) (Pos.pred_double p)

  (** val pred_double : int -> int **)

  let pred_double = function
  | 0 -> (~-) Coq_xH
  | p -> (Pos.pred_double p)
  | (~-) p -> (~-) (Coq_xI p)

  (** val pos_sub : positive -> positive -> int **)

  let rec pos_sub x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> double (pos_sub p q)
       | Coq_xO q -> succ_double (pos_sub p q)
       | Coq_xH -> (Coq_xO p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> pred_double (pos_sub p q)
       | Coq_xO q -> double (pos_sub p q)
       | Coq_xH -> (Pos.pred_double p))
    | Coq_xH ->
      (match y with
       | Coq_xI q -> (~-) (Coq_xO q)
       | Coq_xO q -> (~-) (Pos.pred_double q)
       | Coq_xH -> 0)

  (** val compare : int -> int -> comparison **)

  let compare x y =
    match x with
    | 0 -> (match y with
            | 0 -> Eq
            | _ -> Lt
            | (~-) _ -> Gt)
    | x' -> (match y with
             | y' -> Pos.compare x' y'
             | _ -> Gt)
    | (~-) x' ->
      (match y with
       | (~-) y' -> coq_CompOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val of_N : coq_N -> int **)

  let of_N = function
  | N0 -> 0
  | Npos p -> p

  (** val pos_div_eucl : positive -> int -> int * int **)

  let rec pos_div_eucl a b =
    match a with
    | Coq_xI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = (+) (( * ) (Coq_xO Coq_xH) r) Coq_xH in
      if (<) r' b
      then (( * ) (Coq_xO Coq_xH) q),r'
      else ((+) (( * ) (Coq_xO Coq_xH) q) Coq_xH),((-) r' b)
    | Coq_xO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = ( * ) (Coq_xO Coq_xH) r in
      if (<) r' b
      then (( * ) (Coq_xO Coq_xH) q),r'
      else ((+) (( * ) (Coq_xO Coq_xH) q) Coq_xH),((-) r' b)
    | Coq_xH -> if (<=) (Coq_xO Coq_xH) b then 0,Coq_xH else Coq_xH,0

  (** val div_eucl : int -> int -> int * int **)

  let div_eucl a b =
    match a with
    | 0 -> 0,0
    | a' ->
      (match b with
       | 0 -> 0,a
       | _ -> pos_div_eucl a' b
       | (~-) b' ->
         let q,r = pos_div_eucl a' b' in
         (match r with
          | 0 -> ((~-) q),0
          | _ -> ((~-) ((+) q Coq_xH)),((+) b r)))
    | (~-) a' ->
      (match b with
       | 0 -> 0,a
       | _ ->
         let q,r = pos_div_eucl a' b in
         (match r with
          | 0 -> ((~-) q),0
          | _ -> ((~-) ((+) q Coq_xH)),((-) b r))
       | (~-) b' -> let q,r = pos_div_eucl a' b' in q,((~-) r))

  (** val div2 : int -> int **)

  let div2 = function
  | 0 -> 0
  | p -> (match p with
          | Coq_xH -> 0
          | _ -> (Pos.div2 p))
  | (~-) p -> (~-) (Pos.div2_up p)
 end
