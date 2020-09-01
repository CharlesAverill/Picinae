Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import strtok_i386.
Import List.

Import X86Notations.

Definition cstring m loc s :=
  m Ⓑ[loc ⊕ N.of_nat (length s)] = 0 /\
  ~In 0 s /\
  forall n, (n < length s)%nat -> m Ⓑ[loc ⊕ N.of_nat n] = nth n s 0.

Theorem cstringcdr m loc h t :
  cstring m loc (cons h t) -> cstring m (loc + 1) t.
  unfold cstring.
  intuition; rewrite <- N.add_assoc,N.add_1_l,<- Nat2N.inj_succ; [assumption|].
  apply H2.
  simpl.
  apply lt_n_S.
  assumption.
Qed.

Theorem cstringcons m loc h t :
  h <> 0
  -> m Ⓑ[loc mod (2^32)] = h
  -> cstring m (loc+1) t
  -> cstring m loc (cons h t).
  unfold cstring.
  simpl (In _ _).
  simpl length.
  rewrite Nat2N.inj_succ,<- N.add_1_l,N.add_assoc.
  intuition.
  destruct n; [rewrite N.add_0_r;assumption|].
  rewrite Nat2N.inj_succ,<- N.add_1_l,N.add_assoc.
  simpl nth.
  apply H4.
  apply lt_S_n.
  assumption.
Qed.

Definition strtok_charset m loc char := m Ⓑ[loc ⊕ char] <> 0.

(* Definition strtok_post loc s s' := *)
(*   exists m m' esp start startstr delim delimstr, *)
(*     s V_MEM32 = Ⓜm -> *)
(*     s R_ESP = Ⓓesp -> *)
(*     s' V_MEM32 = Ⓜm' -> *)
(*     cstring m start startstr -> *)
(*     cstring m delim delimstr -> *)
(*     (start = if (m Ⓓ[esp⊕4] =? 0) then m Ⓓ[loc] else m Ⓓ[esp⊕4]) /\ *)
(*     if start =? 0 *)
(*     then s' R_EAX = Ⓓ0 *)
(*     else exists tok tokstr alld alldstr rest reststr result next, *)
(*         cstring m tok tokstr /\ *)
(*         cstring m alld alldstr /\ *)
(*         cstring m rest reststr /\ *)
(*         s' R_EAX = Ⓓresult /\ *)
(*         m' Ⓓ[loc] = next /\ *)
(*         cstring m' result tokstr /\ *)
(*         startstr = tokstr ++ alldstr ++ reststr /\ *)
(*         (forall c, List.In c alldstr -> List.In c delimstr) /\ *)
(*         match reststr with *)
(*         | nil => next = 0 *)
(*         | cons h _ => ~List.In h delimstr /\ cstring m' next reststr *)
(*         end. *)

Definition strtok_post loc m strarg delim (_:exit) s' :=
  exists m' delimstr,
    s' V_MEM32 = Ⓜm' ->
    cstring m delim delimstr ->
    let start := if strarg =? 0 then m Ⓓ[loc] else strarg in
    if start =? 0
    then s' R_EAX = Ⓓ0
    else exists startstr tok tokstr alld alldstr rest reststr,
        cstring m start startstr /\
        cstring m' tok tokstr /\
        cstring m alld alldstr /\
        cstring m rest reststr /\
        s' R_EAX = Ⓓtok /\
        startstr = tokstr ++ alldstr ++ reststr /\
        (forall c, List.In c delimstr -> ~List.In c tokstr) /\
        (forall c, List.In c alldstr -> List.In c delimstr) /\
        match reststr with
        | nil => m' Ⓓ[loc] = 0
        | cons h _ => ~List.In h delimstr /\ cstring m' (m' Ⓓ[loc]) reststr
        end.

(* Definition strtok_invs loc morig strarg string delim delimstr a s := *)
(*   let args_inv := *)
(*       vmem (s V_MEM32) =  *)
(*   let charset_inv := *)
(*       forall c, *)
(*         List.In c delimstr *)
(*         -> strtok_charset (vmem (s V_MEM32)) (vnum (s R_ESP)) c *)
(*   in *)
(*   match a with *)
(*   | 18 => *)
(*     s R_EAX = None *)
(*   end. *)
