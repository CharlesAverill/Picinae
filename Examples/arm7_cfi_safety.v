Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Require Import arm7_cfi2.

(** Jump table safety.
    pol: policy prop. `pol src dest` means src is allowed to jump to dest
         in the original policy
    amap: address map. `amap a = a'` means that the instruction originally at
         index/byte-offset a gets relocated to a'.
    jt:  jump table, `jt a = zs` means that the control flow from a is allowed
         to jump or fall-through to any index/byte-offset z in zs

    Definition says that if the jump table allows a jump from the new src
    location, `amap src`, to a destination or its relocation, `amap dest`,
    then the original policy, `pol`, would have allowed that jump from/to
    the original addresses. *)
Definition jtsafe :=
  forall (pol:Z->Z->Prop) (amap:Z->Z) (jt:list Z) (src dest:Z)
    (JTOK: jt (amap src) = dest \/ jt (amap src) = (amap dest)),
    pol src dest.

