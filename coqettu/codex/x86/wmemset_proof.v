(* wmemset -- musl i386, wide-character fill

   SEMANTICS
   ---------
   Store the 32-bit wchar_t at successive four-byte locations, decrementing
   the count. Reload the original destination pointer and return it.

   SPECIFICATION (wmemset(3), Linux man-pages 6.9.1, 2024-05-02)
   ---------------------------------------------------------
     #include <wchar.h>
     wchar_t *wmemset(wchar_t *wcs, wchar_t wc, size_t n);
   Fill n wide characters with wc and return wcs.
   Source: /usr/share/man/man3/wmemset.3.gz (paraphrased).

   PROVENANCE
   ----------
   Binary: coqettu/alpine_musl/x86/lib/libc.musl-x86.so.1, musl-1.2.6-r6
   SHA256: 8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de
   Symbol: wmemset, ELF VA 0x37d10; global entry 0x47d10, RET 0x47d30.
   Lifter: Ghidra 12.0 PUBLIC, pinned ../lifter_base and Codex-local wrapper;
           strict global-address lift with generated type check.
   Model: Written by Codex (OpenAI); checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V i386 cdecl ABI)
   --------------------------------------------------
   Input:  Destination, wchar_t value and count at entry ESP+4, ESP+8, ESP+12.
           The 4*n-byte destination avoids the 16-byte entry stack region
           containing the saved return address and these three arguments.
   Output: Every requested four-byte element equals the input wchar_t;
           every read disjoint from the destination is unchanged. EAX is the
           original destination. Callee-saved registers, entry ESP and access
           permissions are preserved at RET, which pops the original address.
   Scope:  Partial correctness, including count zero. No artificial count or
           alignment bound: the finite-region bound follows from disjointness
           from the live stack. No concrete access-success/termination claim.
 *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_strings i386_memory wmemset_i386.
From Stdlib Require Import NArith Lia.
Import X86Notations.
Open Scope N.

Definition wmemset_char (s0 : store) := getmem 32 LittleE 4 (s0 V_MEM32) (8+s0 R_ESP).
Definition wmemset_count (s0 : store) := getmem 32 LittleE 4 (s0 V_MEM32) (12+s0 R_ESP).
Definition wmemset_pre (s0 : store) :=
  ~overlap 32 (s0 R_ESP) 16 (cdecl_arg s0) (4*wmemset_count s0).
Definition wmemset_registers (s0 s : store) :=
  cdecl_leaf_frame (s0[V_MEM32:=s V_MEM32]) s.
Definition wmemset_memory (s0 : store) (m : memory) :=
  memory_region_frame (s0 V_MEM32) m (cdecl_arg s0) (4*wmemset_count s0).
Definition wmemset_result (s0 : store) (m : memory) :=
  wide_filled m (cdecl_arg s0) (wmemset_char s0) (wmemset_count s0) /\ wmemset_memory s0 m.
Definition wmemset_cursor (s0 s : store) :=
  wmemset_registers s0 s /\ wmemset_memory s0 (s V_MEM32) /\ s R_ECX=wmemset_char s0 /\
  exists k, k<=wmemset_count s0 /\ s R_EAX=wmemset_count s0-k /\
    s R_EDX=(cdecl_arg s0+4*k) mod 2^32 /\ wide_filled (s V_MEM32) (cdecl_arg s0) (wmemset_char s0) k.
Definition wmemset_post (s0 s : store) :=
  cdecl_leaf_post (s0[V_MEM32:=s V_MEM32]) (cdecl_arg s0) s /\ wmemset_result s0 (s V_MEM32).
Definition wmemset_invs (s0 : store) (t : trace) : option Prop :=
  match t with (Addr a,s)::_ => match a with
  | 0x47d10 => Some (s=s0)
  | 0x47d28 => Some (wmemset_cursor s0 s)
  | 0x47d30 => Some (wmemset_post s0 s)
  | _ => None end | _ => None end.
Definition wmemset_exit := at_address 0x47d30.
Theorem wmemset_nwc : forall s1 s2, wmemset_i386 s1=wmemset_i386 s2.
Proof. reflexivity. Qed.
Theorem wmemset_preserves_callee_saved : forall v, List.In v cdecl_saved ->
  forall_endstates wmemset_i386 (fun _ s _ s' => s v=s' v).
Proof. prove_cdecl_saved. Qed.

Theorem wmemset_correct_local : forall s0 (PRE0 : wmemset_pre s0) t xs
  (ENTRY : startof t xs=(Addr 0x47d10,s0)),
  satisfies_all wmemset_i386 (wmemset_invs s0) wmemset_exit (xs::t).
Proof.
  intros s0 PRE0 t xs ENTRY. apply prove_invs.
  - simpl. rewrite ENTRY. x86_step. reflexivity.
  - intros t1 a s t2 UT SPL PRE. clear - PRE PRE0.
    destruct_inv 32 PRE.
    + subst s. repeat x86_step.
      unfold wmemset_cursor, wmemset_registers, cdecl_leaf_frame. psimpl.
      split; [repeat split; reflexivity|]. split.
      * intros a count NO. reflexivity.
      * split; [reflexivity|]. exists 0.
        unfold wmemset_count, wmemset_char, cdecl_arg. psimpl.
        repeat split; try apply N.le_0_l; try reflexivity. intros i I. clear - I. lia.
    + unfold wmemset_cursor, wmemset_registers, cdecl_leaf_frame in PRE.
      destruct PRE as ((MEM & SP & BX & SI & DI & BP & RD & WR) & FRAME & CX & k & K & AX & DX & FILLED).
      psimpl in SP. psimpl in BX. psimpl in SI. psimpl in DI.
      psimpl in BP. psimpl in RD. psimpl in WR.
      repeat x86_step.
      all: unfold wmemset_cursor, wmemset_post, wmemset_registers, cdecl_leaf_post, cdecl_leaf_frame.
      all: psimpl; elimstore; psimpl.
      all: repeat rewrite setmem_mod_l.
      all: csimpl.
      * split.
        -- split.
           ++ exact (protected_stack_load (s0 V_MEM32) (s V_MEM32) (s0 R_ESP)
                (cdecl_arg s0) (wmemset_count s0) 4 PRE0 FRAME ltac:(lia)).
           ++ repeat split; first [reflexivity|assumption].
        -- unfold wmemset_result. split; [|exact FRAME].
           assert (EQ : k=wmemset_count s0)
             by (set (n:=wmemset_count s0) in *; clearbody n; clear - K BC; lia).
           rewrite <- EQ. exact FILLED.
      * assert (LT : k<wmemset_count s0)
          by (set (n:=wmemset_count s0) in *; clearbody n; clear - K BC; lia).
        split; [repeat split; first [reflexivity|assumption]|]. split.
        -- apply memory_region_frame_step; [exact LT|exact FRAME].
        -- split; [reflexivity|]. exists (k+1). split.
           ++ set (n:=wmemset_count s0) in *; clearbody n; clear - LT; lia.
           ++ split.
              ** apply remaining_decrement; [unfold wmemset_count; apply getmem_bound|exact LT].
              ** split.
                 --- replace (4+cdecl_arg s0+4*k) with (cdecl_arg s0+4*(k+1))
                       by (set (p:=cdecl_arg s0); clearbody p; clear - p k; lia).
                     reflexivity.
                 --- apply wide_filled_step with (n:=wmemset_count s0).
                     +++ exact (protected_stack_region_bound _ _ _ PRE0).
                     +++ unfold wmemset_char. apply getmem_bound.
                     +++ exact LT.
                     +++ exact FILLED.
Qed.

Theorem wmemset_correct : forall prog (EXT : wmemset_i386 ⊆2 prog)
  s0 (PRE0 : wmemset_pre s0) t xs
  (ENTRY : startof t xs=(Addr 0x47d10,s0)),
  satisfies_all prog (wmemset_invs s0) wmemset_exit (xs::t).
Proof.
  intros prog EXT s0 PRE0 t xs ENTRY. eapply satisfies_all_pmono; [exact EXT| |].
  - intros a s tl EX NO. unfold wmemset_invs, wmemset_i386 in *.
    destruct a as [|a]; [reflexivity|].
    repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try discriminate).
  - intros xs' t' START. apply wmemset_correct_local; [exact PRE0|]. rewrite START. exact ENTRY.
Qed.

Theorem wmemset_returns : forall prog (EXT : wmemset_i386 ⊆2 prog)
  s0 (PRE0 : wmemset_pre s0) t s x s'
  (ENTRY : startof t (Addr 0x47d30,s)=(Addr 0x47d10,s0))
  (XP : exec_prog prog ((x,s')::(Addr 0x47d30,s)::t))
  (UT : unterminated wmemset_exit t),
  exists m, wmemset_result s0 m /\
    cdecl_returned (s0[V_MEM32:=m]) (cdecl_arg s0) x s' /\
    x=Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)).
Proof.
  intros prog EXT s0 PRE0 t s x s' ENTRY XP UT.
  pose proof (wmemset_correct prog EXT s0 PRE0 t (Addr 0x47d30,s) ENTRY) as SA.
  pose proof (satall_trueif_inv prog _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as INV.
  change (wmemset_post s0 s) in INV. destruct INV as [POST RESULT].
  assert (RETURN : cdecl_returned (s0[V_MEM32:=s V_MEM32]) (cdecl_arg s0) x s').
  { eapply cdecl_ret_step with (p:=prog) (ret:=0x47d30) (s:=s).
    - apply EXT. reflexivity.
    - exact POST.
    - exact (exec_prog_final _ _ _ _ XP). }
  exists (s V_MEM32). split; [exact RESULT|]. split; [exact RETURN|].
  pose proof (proj1 RETURN) as ADDRESS. simpl_stores in ADDRESS.
  pose proof (protected_stack_load (s0 V_MEM32) (s V_MEM32) (s0 R_ESP)
    (cdecl_arg s0) (wmemset_count s0) 0 PRE0 (proj2 RESULT) ltac:(lia)) as STACK.
  rewrite N.add_0_l in STACK. rewrite STACK in ADDRESS. exact ADDRESS.
Qed.
