Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import memcpy_i386.

Import PArch_i386.
Import X86Notations.
Open Scope N.

Theorem memcpy_welltyped: welltyped_prog x86typctx memcpy_i386.
Proof.
  Picinae_typecheck.
Qed.

Definition memcpy_esp_inv (esp:N) (mem:addr->N) (x:exit) (s':store) :=
  match x with Exit a =>
    if N.eq_dec a (getmem LittleE 4 mem esp) then True
    else s' R_ESP = Some (VaN esp 32)
  | _ => True
  end.

Tactic Notation "destN" constr(n) "until" tactic(T) "eqn" ":" ident(H) :=
  let p := fresh n in
  destruct n as [|p] eqn:H;
  [ try solve [T]
  | repeat first [ solve[T] | destruct p as [p|p|] ] ].
Tactic Notation "focus_addr" hyp(H) constr(n) :=
  match type of H with _ = n => idtac | _ => shelve end.

Definition equal_bytes (m0 m1:addr->N) (src dst:addr) (n:N) : Prop :=
  forall i, i < n -> m0 (src+i) = m1 (dst+i).

Definition memcpy_regs_inv (src dst:addr) (len eax ecx esi edi:N) : Prop :=
  src + len = esi + ecx + eax /\ dst + len = edi + ecx + eax.

Definition memcpy_inv_set (m0 m1:addr->N) (esp:N) (a:addr) (_:exit) (s:store) (_:nat) :=
  match a with
  | 0 => Some True
  | 61 => Some (∃ ecx, s R_ECX = Ⓓecx 
                    /\ ecx = (m0 Ⓓ[esp+12] - (m0 Ⓓ[esp+12] mod 4)) 
                    /\ equal_bytes m0 m1 (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) ((m0 Ⓓ[esp+12]) mod 4))
  | 70 => Some (∃ ecx eax edi esi, 
                   s R_ECX = Ⓓecx /\ s R_EAX = Ⓓeax /\ s R_EDI = Ⓓedi /\ s R_ESI = Ⓓesi
                   /\ eax < 4
                   /\ memcpy_regs_inv (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) (m0 Ⓓ[esp+12]) eax (4*ecx) esi edi
                   /\ equal_bytes m0 m1 (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) (edi - (m0 Ⓓ[esp+4])))
  | 74 => Some (∃ ecx edi esi, 
                   s R_ECX = Ⓓecx /\ s R_EDI = Ⓓedi /\ s R_ESI = Ⓓesi
                   /\ memcpy_regs_inv (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) (m0 Ⓓ[esp+12]) 0 ecx esi edi
                   /\ equal_bytes m0 m1 (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) (edi - (m0 Ⓓ[esp+4])))
  | 77 | 85 => Some (equal_bytes m0 m1 (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) (m0 Ⓓ[esp+12]))
  | 86 => Some (∃ ecx, s R_ECX = Ⓓecx 
                    /\ ecx = (m0 Ⓓ[esp+12]) 
                    /\ m0 = m1)
  | 91 => Some (∃ ecx, s R_ECX = Ⓓecx 
                    /\ ecx = (m0 Ⓓ[esp+12] >> 2)
                    /\ equal_bytes m0 m1 (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) ((m0 Ⓓ[esp+12]) mod 2))
  | 97 => Some (∃ ecx eax edi esi, 
                      s R_ECX = Ⓓecx 
                   /\ s R_EAX = Ⓓeax 
                   /\ s R_EDI = Ⓓedi
                   /\ s R_ESI = Ⓓesi
                   /\ s R_DF = ⓑ0
                   /\ memcpy_regs_inv (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) (m0 Ⓓ[esp+12]) 0 (4*ecx) esi edi
                   /\ equal_bytes m0 m1 (m0 Ⓓ[esp+8]) (m0 Ⓓ[esp+4]) (edi - (m0 Ⓓ[esp+4])))
  | _ => None
end.

Definition memcpy_postcond (mem0 mem1:addr->N) (esp:N) (_:addr) (_:exit) (s:store) (_:nat) :=
  s R_ESP = Some (VaN (esp+4) 32) /\
  exists len src dst,
    len = mem0 (esp + 12) /\
    src = mem0 (esp + 8) /\
    dst = mem0 (esp + 4) /\
  forall i, i < len -> mem0 (src+i) = mem1 (dst+i).

Definition memcpy_inv (mem0 mem1:addr->N) (esp:N) :=
  x86_subroutine_inv memcpy_i386 (memcpy_inv_set mem0 mem1 esp) (memcpy_postcond mem0 mem1 esp) (getmem LittleE 4 mem1 esp).

Theorem memcpy_partial_correctness:
  forall s esp mem0 mem1 m n s' x
         (HI0: ~ mem_readable s (2^32 - 1)%N)
         (MDL0: models x86typctx s)
         (ESPLO: esp + 16 <= 2^32)
         (ESP0: s R_ESP = Some (VaN esp 32)) 
         (MEM0: s V_MEM32 = Some (VaM mem0 32)) (MEM1: s' V_MEM32 = Some (VaM mem1 32))
         (RET: memcpy_i386 (getmem LittleE 4 mem1 esp) = None)
         (XP0: exec_prog memcpy_i386 0 s m n s' x),
  match memcpy_inv mem0 mem1 esp x s' n with Some P => P | None => True end.
Proof.
  intros.
  destruct x as [|a'|i]; try exact I.
  eapply prog_inv. exact XP0.
  unfold memcpy_inv. destruct (getmem _ _ _ _). discriminate RET. exact I.
  intros.
  assert (ESP: memcpy_esp_inv esp mem0 (Exit a1) s1).
   admit.
  unfold memcpy_esp_inv in ESP. unfold memcpy_inv, x86_subroutine_inv in PRE.

  destruct (N.eq_dec a1 _).
  subst a1. eapply NISStep. intros. rewrite IL in RET. discriminate RET. clear n0.
  destN a1 until (exfalso; exact PRE) eqn:ADDR.
  all:unfold memcpy_inv_set in PRE.

  Local Ltac step := time x86_step.

  all: focus_addr ADDR 77.
  step.
  step.
  step.
  exact PRE.

  Unshelve. all: focus_addr ADDR 86.
  destruct PRE as [ecx [ECX [ECXEQ MEMEQ]]].
  step. 
  step. 
  Focus 2. eexists. split. reflexivity. split. rewrite ECXEQ.

  Unshelve. all: focus_addr ADDR 97. 
  destruct PRE as [ecx [eax [edi [esi [df [ECX [EAX [EDI [ESI [DF [REGS EQ]]]]]]]]]]].
  apply NISStep;
  let sz := fresh "sz" in let q := fresh "Q" in let s := fresh "s" in let x := fresh "x" in
  let LT := fresh "LT" in let IL := fresh "IL" in let XS := fresh "XS" in let XP' := fresh "XP'" in
  intros sz q s x LT IL XS XP'; clear LT;
  apply not_unfinished in XP';
  apply inj_prog_stmt in IL; destruct IL; subst sz q;
  lazymatch goal with |- context [ Exit (?x + ?y) ] => simpl (x+y) end.
  stock_store in XS.
  apply reduce_seq_if in XS; [|exact XP']. subst. simpl_exp in XS.
  simpl_stores in XS.


  