open BinNums
open BinPos
open Datatypes

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : positive -> positive -> int

  val compare : int -> int -> comparison

  val of_N : coq_N -> int

  val pos_div_eucl : positive -> int -> int * int

  val div_eucl : int -> int -> int * int

  val div2 : int -> int
 end
