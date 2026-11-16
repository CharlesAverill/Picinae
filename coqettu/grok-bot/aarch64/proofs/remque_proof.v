(* remque -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf)

   SEMANTICS
   ---------
   musl's src/search/insque.c (struct node { next; prev; }):
       void remque(void *element) {
           struct node *e = element;
           if (e->next) e->next->prev = e->prev;
           if (e->prev) e->prev->next = e->next;
       }

   SPECIFICATION (man 3 insque, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <search.h>
            void insque(void *elem, void *prev);
            void remque(void *elem);
     DESCRIPTION
            The insque() and remque() functions manipulate doubly linked
            lists.  Each element in the list is a structure of which the
            first two elements are a forward and a backward pointer.  The
            linked list may be linear (i.e., NULL forward pointer at the end
            of the list and NULL backward pointer at the start of the list)
            or circular.
            The insque() function inserts the element pointed to by elem
            immediately after the element pointed to by prev.
            If the list is linear, then the call insque(elem, NULL) can be
            used to insert the initial list element, and the call sets the
            forward and backward pointers of elem to NULL.
            The remque() function removes the element pointed to by elem
            from the doubly linked list.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            remque at 0x51424 (ELF vaddr); 0x151424 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes 1-3, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/remque_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = elem; X30 = return address.
   Output:  If execution reaches the RET (0x151444): memory = remque_mem mem
            elem, which performs exactly the 8-byte loads and stores of the C
            code above in the same order (next at offset 0, prev at offset 8;
            later loads see earlier stores).  SP, X30 and the AAPCS64
            callee-saved registers are unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import remque_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokBitRefl GrokBytes.
Import ARM8Notations.
Open Scope N.

Theorem remque_welltyped: welltyped_prog arm8typctx remque_armv8.
Proof. Picinae_typecheck. Qed.

Theorem remque_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates remque_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem remque_preserves_x30:
  forall_endstates remque_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition ld (m a:N) : N := getmem 64 LittleE 8 m a.
Definition st (m a v:N) : N := setmem 64 LittleE 8 m a v.
(* remque(e), exactly as the machine code orders its loads and stores *)
Definition remque_mem (m e : N) : N :=
  let m1 := if ld m e =? 0 then m else st m (8 + ld m e) (ld m (8 + e)) in
  if ld m1 (8 + e) =? 0 then m1 else st m1 (ld m1 (8 + e)) (ld m1 e).

Section Invariants.
  Variables (sp mem raddr c d : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x151424 => Inv 0 (s R_X0 = c /\ s R_X1 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x151444 => Post 0 (s V_MEM64 = remque_mem mem c /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition remque_exits := make_exits 0 remque_armv8 invs.
  Definition remque_invs := make_invs 0 remque_armv8 invs.
End Invariants.

Theorem remque_partial_correctness:
  ∀ prog s sp mem raddr c d t xs'
    (PROG: remque_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x151424, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = c) (X1: s R_X1 = d),
  satisfies_all prog (remque_invs sp mem raddr c d) (remque_exits sp mem raddr c d) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=remque_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold remque_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X1 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply remque_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & X1 & MEM & SP & X30).
  repeat arm8_step.
  all: splits; try reflexivity; try assumption.
  all: unfold remque_mem, ld, st; rewrite ?BC; cbv zeta; rewrite ?BC0; reflexivity.
Qed.
