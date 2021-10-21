type policy = (int option * (int * int list)) list
type instr_data =
| Data of int option * int * int list * int * bool
(** val twoscomp : int -> int -> int **)

let twoscomp m n =
  if (<) n m then n else (-) n (( * ) 2 m)
(** val newsize : instr_data -> int **)

let newsize = function
| Data (iid, _, _, n0, sb) ->
  (+) (match iid with
       | Some _ -> 1
       | None -> 0)
    (let op = (land) n0 127 in
     if (=) op 23
     then if (=) ((land) n0 3968) 0 then 1 else 2
     else if (=) op 99
          then (+) 1 (if sb then 0 else 1)
          else if (=) op 103 then (+) 12 (if sb then 0 else 1) else 1)
(** val sumsizes : instr_data list -> int **)

let sumsizes l =
  (fun f l a -> List.fold_left f a l) (fun c d -> (+) c (newsize d)) l 0
(** val sum_n_sizes : int -> instr_data list -> int -> int **)

let rec sum_n_sizes n0 l b =
  match l with
  | [] -> b
  | d::t ->
    if (<) 0 n0 then sum_n_sizes ((-) n0 1) t ((+) b (newsize d)) else b
(** val newoffset :
    instr_data list -> instr_data -> int -> instr_data list -> int -> int **)

let newoffset l1 d c l2 i =
  (-)
    ((+)
      (if (<=) 0 i
       then sum_n_sizes i (d::l2) 0
       else (~-) (sum_n_sizes ((~-) i) l1 0)) c) (newsize d)
(** val decode_branch_offset : int -> int **)

let decode_branch_offset n0 =
  (lor)
    ((lor) ((lor) ((land) ((lsr) n0 9) 7) ((land) ((lsr) n0 22) 504))
      ((land) ((lsl) n0 2) 512)) ((land) ((lsr) n0 21) 1024)
(** val decode_jump_offset : int -> int **)

let decode_jump_offset n0 =
  (lor)
    ((lor) ((lor) ((land) ((lsr) n0 22) 511) ((land) ((lsr) n0 11) 512))
      ((land) ((lsr) n0 2) 261120)) ((land) ((lsr) n0 13) 262144)
(** val shrink : instr_data list -> instr_data list -> instr_data list **)

let rec shrink l1 = function
| [] -> List.rev l1
| d::t ->
  let Data (iid, oid, sd, n0, b) = d in
  shrink ((Data (iid, oid, sd, n0,
    (if b
     then true
     else let op = (land) n0 127 in
          if if (=) op 99 then true else (=) op 103
          then let o =
                 if (=) op 99
                 then newoffset l1 d 1 t
                        (twoscomp 1024 (decode_branch_offset n0))
                 else newoffset l1 d 2 t ( (List.length t))
               in
               if (<=) (-1024) o then (<) o 1024 else false
          else true)))::l1) t
(** val newtag : instr_data -> int list **)

let newtag = function
| Data (iid0, _, _, _, _) ->
  (match iid0 with
   | Some iid -> ((lor) 55 ((lsl) ((mod) iid 1048576) 12))::[]
   | None -> [])
(** val encode_jump_offset : int -> int **)

let encode_jump_offset o =
  (lor)
    ((lor) ((lor) ((lsl) ((land) o 511) 22) ((lsl) ((land) o 512) 11))
      ((lsl) ((land) o 261120) 2)) ((lsl) ((land) o 262144) 13)
(** val newjump : int -> int -> int list option **)

let newjump rd o' =
  if if (<=) (-262144) o' then (<) o' 262144 else false
  then Some
         (((lor) ((lor) 111 ((lsl) rd 7))
            (encode_jump_offset ((mod) o' 524288)))::[])
  else None
(** val encode_branch_offset : int -> int **)

let encode_branch_offset o =
  (lor)
    ((lor) ((lor) ((lsl) ((land) o 7) 9) ((lsl) ((land) o 504) 22))
      ((lsr) ((land) o 512) 2)) ((lsl) ((land) o 1024) 21)
(** val newbranch :
    instr_data list -> instr_data -> int -> instr_data list -> int -> int ->
    int list option **)

let newbranch l1 d c l2 op i =
  let Data (_, _, _, _, sb) = d in
  if sb
  then let o' = newoffset l1 d c l2 i in
       if if (<=) (-1024) o' then (<) o' 1024 else false
       then Some
              (((lor) ((land) op 33550463)
                 (encode_branch_offset ((mod) o' 2048)))::[])
       else None
  else (match newjump 0 (newoffset l1 d c l2 i) with
        | Some j -> Some (((lor) ((lxor) ((land) op 33550463) 4096) 1024)::j)
        | None -> None)
(** val newijump :
    instr_data list -> instr_data -> instr_data list -> int list option **)

let newijump l1 d l2 =
  let Data (_, oid, _, n0, _) = d in
  let rs1 = (land) ((lsr) n0 15) 31 in
  let tmp1 = if (<) rs1 31 then 31 else 29 in
  let tmp2 = if (=) rs1 30 then 29 else 30 in
  let tmp3 = if (<) 29 rs1 then rs1 else 29 in
  (match newbranch l1 d 2 l2
           ((lor) ((lor) 4195 ((lsl) tmp1 15)) ((lsl) tmp2 20))
           ((+) 1 ( (List.length l2))) with
   | Some br ->
     Some
       (((lor) ((lor) ((lor) 19 ((lsl) tmp3 7)) ((lsl) rs1 15))
          ((land) n0 4293918720))::(((lor) ((lor) 4290801683 ((lsl) tmp3 7))
                                      ((lsl) tmp3 15))::(
       ((lor) ((lor) 8195 ((lsl) tmp1 7)) ((lsl) tmp3 15))::(
       ((lor) ((lor) 133197843 ((lsl) tmp2 7)) ((lsl) tmp1 15))::(
       ((lor) 6243 ((lsl) tmp2 15))::(((lor)
                                        ((lor) 1079005203 ((lsl) tmp1 7))
                                        ((lsl) tmp1 15))::(
       ((lor) ((lor) ((lor) 51 ((lsl) tmp3 7)) ((lsl) tmp3 15))
         ((lsl) tmp1 20))::(((lor) ((lor) 8195 ((lsl) tmp1 7))
                              ((lsl) tmp3 15))::(((lor)
                                                 ((lor) 55 ((lsl) tmp2 7))
                                                 ((lsl) 
                                                 ((mod) oid 1048576) 12))::(
       ((lor) ((lor) 57696275 ((lsl) tmp2 7)) ((lsl) tmp2 15))::
       (List.append br (((lor) ((land) n0 4095) ((lsl) tmp3 15))::[]))))))))))))
   | None -> None)
(** val new_auipc :
    int -> instr_data list -> instr_data -> int list option **)

let new_auipc base l1 = function
| Data (_, _, sd, n0, _) ->
  if if (<=) 0 base then List.mem 1 sd else false
  then if (=) ((land) n0 3968) 0
       then Some (16435::[])
       else let new_target' =
              (+) ((lsl) ((+) base ( (List.length l1))) 2)
                ((land) n0 4294963200)
            in
            let new_target =
              if (<=) 2048 ((land) new_target' 4095)
              then (+) new_target' 4096
              else new_target'
            in
            let rd = (land) n0 3968 in
            Some
            (((lor) ((lor) 55 rd) ((land) new_target 4294963200))::(
            ((lor) ((lor) ((lor) 19 rd) ((lsl) rd 8))
              ((lsl) ((land) new_target 4095) 20))::[]))
  else None
(** val newinstr :
    int -> instr_data list -> instr_data -> instr_data list -> int list
    option **)

let newinstr base l1 d l2 =
  let Data (_, _, sd, n0, _) = d in
  if (<) n0 0
  then None
  else if (=) ((land) n0 4095) 55
       then if List.mem 1 sd then Some (16435::[]) else None
       else let op = (land) n0 127 in
            if (=) op 23
            then new_auipc base l1 d
            else if (=) op 99
                 then let i = twoscomp 1024 (decode_branch_offset n0) in
                      if if if if if (=) ((land) n0 256) 0
                                  then List.mem 1 sd
                                  else false
                               then List.mem i sd
                               else false
                            then (<=) 0 ((+) ( (List.length l1)) i)
                            else false
                         then (<=) i ( (List.length l2))
                         else false
                      then newbranch l1 d 1 l2 n0 i
                      else None
                 else if (=) op 103
                      then newijump l1 d l2
                      else if (=) op 111
                           then let i =
                                  twoscomp 262144 (decode_jump_offset n0)
                                in
                                if if if List.mem i sd
                                      then (<=) 0 ((+) ( (List.length l1)) i)
                                      else false
                                   then (<=) i ( (List.length l2))
                                   else false
                                then newjump ((land) ((lsr) n0 7) 31)
                                       (newoffset l1 d 1 l2 i)
                                else None
                           else if List.mem 1 sd then Some (n0::[]) else None
(** val newinstrs :
    int -> int list list -> instr_data list -> instr_data list -> int list
    list option **)

let rec newinstrs base l' l1 = function
| [] -> Some (List.rev l')
| d::t ->
  (match newinstr base l1 d t with
   | Some x -> newinstrs base ((List.append (newtag d) x)::l') (d::l1) t
   | None -> None)
(** val newtable :
    int -> int -> int list -> int -> instr_data list -> int list **)

let rec newtable base base' acc i = function
| [] -> List.rev acc
| d::t ->
  newtable base base' (((lsl) ((+) ((-) base' base) i) 7)::acc)
    ((-) ((+) i (newsize d)) 1) t
(** val todata : ((int option * (int * int list)) * int) -> instr_data **)

let todata = function
| y,n -> let iid,y0 = y in let oid,sd = y0 in Data (iid, oid, sd, n, false)
(** val newcode :
    policy -> int list -> int -> int -> int list * int list list option **)

let newcode pol l base base' =
  let d = shrink [] (List.map todata (List.combine pol l)) in
  (newtable base base' [] 0 d),(if (<) (sumsizes d) ((-) 1073741824 base')
                                then newinstrs base [] [] d
                                else None)
(** val mapaddr : policy -> int list -> int -> int **)

let mapaddr pol l addr =
  sum_n_sizes addr (shrink [] (List.map todata (List.combine pol l))) 0
