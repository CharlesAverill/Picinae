Require Import NArith ZArith Bool Coq.Lists.List.
Require Import Lia ZifyBool ZifyN.
Require Import -(notations) arm7_cfi2.
Require Import Picinae_armv7.
Require Import Lia ZifyN ZifyNat.
Import ARM7Notations.
Import ListNotations.
Open Scope N.
Require Import Nat.


(** Definitions for reasoning about the locations in memory and sizes of
    jumptable entries. *)
Section JTAbstractions.
Local Definition jtT := list (list Z).
Fixpoint _block_of (i:nat) (lengths:list nat) : option nat :=
  match lengths with
  | l::t => if (i <? l)%nat then Some O else
      match _block_of (Nat.sub i l) t with
      | Some i' => Some (S i')
      | _ => None
      end
  | _ => None
  end.

Definition block_of (a:addr) (p:list (list Z)) ti : option nat :=
  let lengths := map (@length Z) p in
  let i := (msub 32 a (4*ti)) >> 2 in
  _block_of (N.to_nat i) lengths.

Definition jt_section jt a ti : option (N * nat) :=
  match block_of a jt ti with
  | Some i =>
      let entry_start := List.fold_left Nat.add
        (List.firstn i (List.map (@length Z) jt)) O in
      Some (4*(ti + (N.of_nat entry_start)), length (List.nth i jt []))
  | None => None
  end.

Fixpoint block_start {A:Set} (i:nat) (ls:list (list A)) :=
  match ls with
  | [] => false
  | l::t =>
      match i, length l with
      | O, S _ => true
      | _, O => block_start i t
      | S _, S _ => 
          if (i <? length l)%nat
          then false
          else block_start (Nat.sub i (length l)) t
      end
  end.
Section JTAbstractions.

(** Definitions for reasoning about the jumptable in memory. *)
Section DataDefinitions.
  (* Concatenate bits, but for Z *)
  Definition czbits (z1:Z) i (z2:Z) := Z.lor (Z.shiftl z1 (Z.of_N i)) z2.

  (* Concatenates a `list Z` of 32-bit numbers into a single number.  Returns
    the value, bitwidth pair. *)
  Definition czlist zs : Z * bitwidth := List.fold_left
    (fun '(zacc,bits_written) z => (czbits z bits_written zacc, 32+bits_written))
    zs (Z0,0).

  (* Concatenates the `list (list Z)` rewritten program into its value in memory. *)
  Definition czslist zss : Z * bitwidth :=
    List.fold_left 
    (fun '(zacc,bits_written) zs => 
      match czlist zs with
      | (z,bits) => (czbits z bits_written zacc, bits+bits_written)
      end)
    zss (Z0,0).

  Definition flatten {A:Type} (ls:list (list A)) :=
    List.fold_left (fun acc l => l++acc) ls [].
End DataDefinitions.

(* Questions:

  1. Can we abstract away from quantifying over the specific program
      and the output of the rewriter? 

  2. How will we instantiate or define the "f" address translation function? *)

(* Simplifying assumptions:

    1. Each instruction that needs a jump table has an entry in the jump table
        at the index of the instruction.  This is not true because of a rewriter
        optimization that elides duplicate table entries.  I hope we can use a
        trick to reason about this simplified version. 
    2. We assume the jump table is read from an index less than its size.  We
        leave it up to the master theorem to prove the contents of the register
        jump-target corresponds to this offset. *)


Theorem jt_safe_jmp:
  forall jt a1 base offset size mem pol zs i i' ti ai f zs'
    (* Add bounds to the Z values for clarity; they get converted to N below. *)
    (TI: (ti >= 0)%Z)
    (A1: (a1 >= 0)%Z)

    (* Tie the output of the rewriter to the rewritten instructions and jumptable. *)
    (RR: rewrite pol zs i i' ti ai = Some(zs', jt) )

    (* Two ideas for formulating the "jumptable stored in memory" hypothesis
       1. use xbits to talk about the values of bits of memory. This won't work
          if the jumptable wraps around the end of memory.
       2. axiomatize the value of aligned reads from the jumptable. *)
    (DATA: match czslist zs' with
           | (jtbits, bits) => xnbits mem (Z.to_N ti) bits = (Z.to_N jtbits)
           end)
    (DATA2: forall i, (i < length (flatten jt))%nat ->
            mem Ⓓ[4*((Z.to_N ti) + (N.of_nat i))] =  Z.to_N (nth i (flatten jt) Z0))

    (* We do not have this "f" function for translating old addresses to new,
       so we axiomatize its important properties:
          1. it maps addresses from the initial code section to addresses in the
             new code, preserving the block index and
          2. the new address is the start of its block *)
    (F: forall z z' (ZLT:z < N.of_nat (length zs)),
        block_of (f (4*(Z.to_N i+z))) zs' (Z.to_N i') = Some z'
        /\ block_start z' zs' = true)

    (* The section of the jump table corresponding to the address a1 has some base
       and size *)
    (SECN: jt_section jt (Z.to_N a1) (Z.to_N ti) = Some (base, size))
    (OFFLT: (offset < size)%nat),
    exists a2, mem Ⓓ[base + 4*(N.of_nat offset)] = f a2
              /\ In (Z.of_N a2) (pol a1).
Proof.
  intros; move mem after offset; move a1 after zs; move zs' before jt.
  (* Simplify RR *)
  unfold rewrite in RR;
  destruct (_rewrite _ _ _ _ _ _ _ _ _) eqn:_rr ;[|discriminate].
  (* Simplify SECN *)
  unfold jt_section in SECN;
  destruct (block_of (Z.to_N a1) jt (Z.to_N ti)) eqn:block_of_jt;[|discriminate];
  symmetry in SECN; inversion SECN as [[BASE LEN]]; rewrite <-BASE;
  assert (BASE':base=4*((Z.to_N ti)+(N.of_nat (fold_left Nat.add (firstn n (map (length (A:=Z)) jt)) 0%nat)))) by (subst;reflexivity);
  clear SECN BASE; rename BASE' into BASE.

  eexists; split.
