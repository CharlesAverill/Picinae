include Core_kernel

(* Integer interfaces *)
module type Num_intf = sig
  type t
  val zero: t
  val succ: t -> t
  val neg:  t -> t
  val (+): t -> t -> t
  val (-): t -> t -> t
  val ( * ): t -> t -> t
end

module type Bit_intf = sig
  type t
  val bit_and: t -> t -> t
  val bit_or: t -> t -> t
  val bit_xor: t -> t -> t
  val bit_not: t -> t

  val shift_left: t -> int -> t
  val shift_right: t -> int -> t
  val shift_right_logical: t -> int -> t
end

module type Intable_intf = sig
  type t
  val of_int: int -> t option
  val to_int: t -> int option
end

let fail s = Error.of_string @@ Printf.sprintf "%s\n**%s" s @@
  String.concat ~sep:"\n  " @@ Backtrace.to_string_list @@ Backtrace.get ()

let failf fmt = (ksprintf fail) fmt

module MakeIntExt (N: Num_intf) (B: Bit_intf with type t = N.t)
  (ConvInt: Intable_intf with type t = N.t)
  (ConvStr: Stringable.S with type t = N.t) = struct
  open N

  let align_up addr ~align =
    B.bit_and (addr + align - (succ zero)) (neg align)
  let align_down addr ~align =
    B.bit_and addr (neg align)

  let of_int_err n = Result.of_option
    ~error:(failf "Integer overflow: %d" n) @@
    ConvInt.of_int n
  let to_int_err n = Result.of_option
    ~error:(failf "Integer overflow: %s" (ConvStr.to_string n)) @@
    ConvInt.to_int n
end

module Int32 = struct
  include MakeIntExt(Int32)(Int32)(Int32)(Int32)
  include Int32
end

module Int64 = struct
  include MakeIntExt(Int64)(Int64)(struct
    include Int64
    let of_int n = Some (Int64.of_int n)
  end)(Int64)
  include Int64
end

module Continue_or_stop = struct
  include Continue_or_stop

  include Monad.Make2 (struct
      type nonrec ('a, 'b) t = ('a, 'b) t

      let bind x ~f =
        match x with
        | Stop _ as x -> x
        | Continue x -> f x
      ;;

      let map x ~f =
        match x with
        | Stop _ as x -> x
        | Continue x -> Continue (f x)
      ;;

      let map = `Custom map
      let return x = Continue x
    end)

  let guard cond ~stop =
    if cond then Continue ()
    else Stop stop

  let of_result res =
    match res with
    | Ok x -> Continue x
    | Error _ -> Stop res
end

module List = struct
  include List

  let sort_on lst ~cmp ~f = List.sort ~compare:(Comparable.lift cmp ~f) lst

  let locate ent = List.find ~f:(phys_equal ent)
end

module Option = struct
  include Option

  let guard cond = if cond then Some () else None

  let inject opt ~def ~f = match opt with
    | Some s -> f s
    | None   -> def
end

module Bigstring = struct
  include Bigstring

  let make ?max_mem_waiting_gc size ch =
    let bs = create ?max_mem_waiting_gc size in
    memset ~pos:0 ~len:size bs ch; bs
end

let init_time = UnixLabels.gettimeofday()
let is_debug = ref false
let debug s =
  if !is_debug then
    let open Float in
    let line = sprintf "[%010.3f] %s" (UnixLabels.gettimeofday() - init_time) s in
    prerr_endline line
  else ()
let debugf fmt = ksprintf debug fmt
