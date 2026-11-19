(* remque -- remove an element from a doubly linked queue (musl x86_64, C)

   SEMANTICS
   ---------
   musl's remque (src/search/insque.c) is

       struct node { struct node *next; struct node *prev; };
       void remque(void *element)
       {
           struct node *e = element;
           if (e->next) e->next->prev = e->prev;
           if (e->prev) e->prev->next = e->next;
       }

   The binary re-reads e->prev and e->next after the first store, exactly as
   the C abstract machine does (the stores may alias e), so the specification
   is that sequence of reads and writes (remque_mem).

   SPECIFICATION (man 3 remque, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     void remque(void *elem);
     remque removes the element pointed to by elem from the doubly linked
     list: its successor's backward link and its predecessor's forward link
     are set to bypass it (a null link is not followed).

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            remque at 0x5e979 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/remque_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = e; m = memory.  No precondition (the model does not fault on
            any address).
   Output:  At the RET (0x15e998): memory = remque_mem m e, i.e. with
            n = m[e] and q = m[e+8] (8-byte words): if n <> 0 then m1 =
            m[n+8 := q] else m1 = m; then with q' = m1[e+8]: if q' <> 0 the
            result is m1[q' := m1[e]] else m1.  RSP and RBX, RBP, R12-R15 are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.remque_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem remque_welltyped: welltyped_prog x64typctx remque_amd64.
Proof. exact welltyped. Qed.

(* addresses are taken mod 2^64 by the memory accessors *)
Definition remque_m1 (m:memory) (e:N) : memory :=
  if m Ⓠ[e] =? 0 then m else m [Ⓠ8 + m Ⓠ[e] := m Ⓠ[8 + e]].

Definition remque_mem (m:memory) (e:N) : memory :=
  let m1 := remque_m1 m e in
  if m1 Ⓠ[8 + e] =? 0 then m1 else m1 [Ⓠ m1 Ⓠ[8 + e] := m1 Ⓠ[e]].

Definition remque_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x15e998 => true
  | _ => false end | _ => false end.

Definition remque_invs (s0:store) (m e:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x15e979 => Some (s V_MEM64 = m /\ s R_RDI = e /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x15e998 => Some (s V_MEM64 = remque_mem m e /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | _ => None
  end | _ => None end.

Theorem remque_correct:
  forall prog s t s' x' m e
         (REMQUE: remque_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15e979, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (E: s R_RDI = e),
  satisfies_all prog (remque_invs s m e) remque_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m e REMQUE ENTRY MDL MEM E.
  eapply satisfies_all_pmono with (p1:=remque_amd64); [exact REMQUE| |].
    intros a s1 t1 EXIT NOCODE. unfold remque_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m e MDL MEM E START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply remque_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [E [RSP CS]]].
  repeat x64_step.
  all: split; [ unfold remque_mem, remque_m1; cbv zeta;
                repeat (match goal with BC: (?x =? 0) = _ |- context [?x =? 0] => rewrite BC end; cbv beta iota);
                sreflexivity |].
  all: conj_tac.
Qed.
