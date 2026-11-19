(* Linked code and shared unary stack interface for wctype. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import
  i386_common i386_stack i386_stack4 i386_stack2 i386_deep_stack i386_unary_call i386_binary_call
  i386_strings i386_stringcmp i386_named_string i386_wstringcmp strcmp_proof wctype_i386 pc_thunk_bx_i386 strcmp_i386.
From Stdlib Require Import NArith Lia List Bool.
Import X86Notations.
Open Scope N.

Definition wctype_linked : program := updateall2 wctype_i386 (updateall2 pc_thunk_bx_i386 strcmp_i386).
Lemma wctype_linked_caller : wctype_i386 ⊆2 wctype_linked.
Proof.
  intros s a insn H. unfold wctype_linked,updateall2,updateall,wctype_i386,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Lemma wctype_linked_strcmp : strcmp_i386 ⊆2 wctype_linked.
Proof. intros s a insn H. unfold wctype_linked,updateall2,updateall. rewrite H. reflexivity. Qed.
Lemma wctype_linked_thunk : pc_thunk_bx_i386 ⊆2 wctype_linked.
Proof.
  intros s a insn H. unfold wctype_linked,updateall2,updateall,pc_thunk_bx_i386,strcmp_i386 in *.
  destruct a as [|a]; [discriminate|].
  repeat (destruct a as [a|a|]; cbn in *; try reflexivity; try congruence).
Qed.
Theorem wctype_linked_welltyped : welltyped_prog x86typctx wctype_linked.
Proof.
  intros s a. unfold wctype_linked,updateall2,updateall.
  destruct (strcmp_i386 s a) as [[sz q]|] eqn:M.
  - pose proof (strcmp_i386.welltyped s a) as WT. rewrite M in WT. exact WT.
  - destruct (pc_thunk_bx_i386 s a) as [[sz q]|] eqn:T.
    + pose proof (pc_thunk_bx_i386.welltyped s a) as WT. rewrite T in WT. exact WT.
    + apply wctype_i386.welltyped.
Qed.



Definition wctype_table:N:=0x85360.
Definition wctype_got:N:=0xb4f9c.
Definition wctype_bytes:list N:=97::108::110::117::109::0::97::108::112::104::97::0::98::108::97::110::107::0::99::110::116::114::108::0::100::105::103::105::116::0::103::114::97::112::104::0::108::111::119::101::114::0::112::114::105::110::116::0::112::117::110::99::116::0::115::112::97::99::101::0::117::112::112::101::114::0::120::100::105::103::105::116::0::nil.
Definition wctype_static (i:N):=nth (N.to_nat i) wctype_bytes 0.
Definition wctype_target (j:N):=wctype_table+6*j.
Definition wctype_letter (j i:N):=wctype_static (6*j+i).
Definition wctype_length (j:N):N:=if j=?11 then 6 else 5.
Definition wctype_matchb (s0:store) (j:N):=
  fixed_name_matchb (s0 V_MEM32) (cdecl_arg s0) (wctype_letter j) (wctype_length j).
Lemma wctype_length_bound:forall j,wctype_length j<=6.
Proof. intros. unfold wctype_length. destruct (j=?11);lia. Qed.
Lemma wctype_name_shape:forall j,j<12 ->wctype_letter j (wctype_length j)=0 /\
  forall i,i<wctype_length j ->wctype_letter j i<>0.
Proof.
  intros j J. pose proof (wctype_length_bound j) as L.
  assert (E:j=0 \/j=1 \/j=2 \/j=3 \/j=4 \/j=5 \/j=6 \/j=7 \/j=8 \/j=9 \/j=10 \/j=11) by lia.
  repeat destruct E as [E|E];subst j;split;try (vm_compute;reflexivity).
  all: intros i I;assert (E:i=0 \/i=1 \/i=2 \/i=3 \/i=4 \/i=5 \/i=6) by lia.
  all: repeat destruct E as [E|E];subst i;vm_compute in *;intuition discriminate.
Qed.
Lemma wctype_match_first:forall s0 j,wctype_matchb s0 j=true ->
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0)=wctype_letter j 0.
Proof.
  intros s0 j MATCH. unfold wctype_matchb in MATCH.
  pose proof (proj1 (fixed_name_matchb_spec (s0 V_MEM32) (cdecl_arg s0) (wctype_letter j) (wctype_length j)) MATCH) as ALL.
  pose proof (ALL 0 ltac:(lia)) as FIRST. rewrite N.add_0_r in FIRST. exact FIRST.
Qed.
Definition wctype_pre (s0:store):=models x86typctx s0 /\
  (forall k,nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
    ~overlap 32 (msub 32 (s0 R_ESP) 56) 56 (cdecl_arg s0+k) 1) /\
  ~overlap 32 (msub 32 (s0 R_ESP) 56) 56 wctype_table 73 /\
  (forall i,i<73 ->getmem 32 LittleE 1 (s0 V_MEM32) (wctype_table+i)=wctype_static i).
Definition wctype_result (s0:store) (value:N):=
  (exists j,j<12 /\ value=j+1 /\ wctype_matchb s0 j=true /\ forall i,i<j ->wctype_matchb s0 i=false) \/
  (value=0 /\ forall i,i<12 ->wctype_matchb s0 i=false).
Definition wctype_base (s0:store):=
  setmem 32 LittleE 4 (save4_registers s0) (msub 32 (s0 R_ESP) 20) 0x3516e.
Definition wctype_args_on (s0:store) (m:memory) (j:N):=
  setmem 32 LittleE 4 (setmem 32 LittleE 4 m (msub 32 (s0 R_ESP) 40) (wctype_target j))
    (msub 32 (s0 R_ESP) 44) (cdecl_arg s0).
Definition wctype_entry_on (s0:store) (m:memory) (j:N):=
  setmem 32 LittleE 4 (wctype_args_on s0 m j) (msub 32 (s0 R_ESP) 48) 0x351bc.
Definition wctype_after_on (s0:store) (m:memory) (j:N):=
  setmem 32 LittleE 4 (setmem 32 LittleE 4 (wctype_entry_on s0 m j)
    (msub 32 (s0 R_ESP) 52) (wctype_target j)) (msub 32 (s0 R_ESP) 56) wctype_got.
Fixpoint wctype_memory (s0:store) (calls:list N):memory:=match calls with
  | nil=>wctype_base s0
  | j::older=>wctype_after_on s0 (wctype_memory s0 older) j end.
Definition wctype_reference (s0:store) (calls:list N):=s0[V_MEM32:=wctype_memory s0 calls].
Definition wctype_frame (s0:store) (m:memory) (depth:N) (s:store):=
  s V_MEM32=m /\ s R_ESP=msub 32 (s0 R_ESP) depth /\ s A_READ=s0 A_READ /\ s A_WRITE=s0 A_WRITE.
Lemma wctype_outer_stack:forall s0 calls off,off<=8 ->
  getmem 32 LittleE 4 (wctype_memory s0 calls) (off+s0 R_ESP)=getmem 32 LittleE 4 (s0 V_MEM32) (off+s0 R_ESP).
Proof.
  intros s0 calls. induction calls as [|j older IH];intros off OFF.
  - unfold wctype_memory,wctype_base,save4_registers.
    rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia. reflexivity.
  - cbn [wctype_memory]. unfold wctype_after_on,wctype_entry_on,wctype_args_on.
    rewrite (N.add_comm off (s0 R_ESP)),!deep_stack_word_frame by lia.
    rewrite (N.add_comm (s0 R_ESP) off). apply IH;exact OFF.
Qed.
Lemma wctype_saved_read:forall s0 calls slot,slot=4 \/slot=8 \/slot=12 \/slot=16 ->
  getmem 32 LittleE 4 (wctype_memory s0 calls) (msub 32 (s0 R_ESP) slot)=
  getmem 32 LittleE 4 (save4_registers s0) (msub 32 (s0 R_ESP) slot).
Proof.
  intros s0 calls. induction calls as [|j older IH];intros slot SLOT.
  - cbn [wctype_memory]. unfold wctype_base. rewrite deep_saved_word_frame by lia. reflexivity.
  - cbn [wctype_memory]. unfold wctype_after_on,wctype_entry_on,wctype_args_on.
    rewrite !deep_saved_word_frame by lia. apply IH;exact SLOT.
Qed.
Lemma wctype_read_region:forall s0 calls p n off,
  ~overlap 32 (msub 32 (s0 R_ESP) 56) 56 p n ->off<n ->
  getmem 32 LittleE 1 (wctype_memory s0 calls) (p+off)=getmem 32 LittleE 1 (s0 V_MEM32) (p+off).
Proof.
  intros s0 calls. induction calls as [|j older IH];intros p n off NO OFF.
  - cbn [wctype_memory]. unfold wctype_base,save4_registers.
    rewrite !descending_stack_read with (total:=56) (n:=n) by (try exact NO;lia). reflexivity.
  - cbn [wctype_memory]. unfold wctype_after_on,wctype_entry_on,wctype_args_on.
    rewrite !descending_stack_read with (total:=56) (n:=n) by (try exact NO;lia). exact (IH p n off NO OFF).
Qed.
Lemma wctype_entry_read_region:forall s0 calls j p n off,
  ~overlap 32 (msub 32 (s0 R_ESP) 56) 56 p n ->off<n ->
  getmem 32 LittleE 1 (wctype_entry_on s0 (wctype_memory s0 calls) j) (p+off)=
  getmem 32 LittleE 1 (s0 V_MEM32) (p+off).
Proof.
  intros s0 calls j p n off NO OFF. unfold wctype_entry_on,wctype_args_on.
  rewrite !descending_stack_read with (total:=56) (n:=n) by (try exact NO;lia). apply wctype_read_region with (n:=n);assumption.
Qed.
Lemma wctype_input_read:forall s0 calls k,wctype_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 1 (wctype_memory s0 calls) (cdecl_arg s0+k)=
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros s0 calls k (_ & A & B & C) PREFIX.
  pose proof (wctype_read_region s0 calls (cdecl_arg s0+k) 1 0 (A k PREFIX) ltac:(lia)) as READ.
  rewrite N.add_0_r in READ. exact READ.
Qed.
Lemma wctype_entry_input_read:forall s0 calls j k,wctype_pre s0 ->nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k ->
  getmem 32 LittleE 1 (wctype_entry_on s0 (wctype_memory s0 calls) j) (cdecl_arg s0+k)=
  getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+k).
Proof.
  intros s0 calls j k (_ & A & B & C) PREFIX.
  pose proof (wctype_entry_read_region s0 calls j (cdecl_arg s0+k) 1 0 (A k PREFIX) ltac:(lia)) as READ.
  rewrite N.add_0_r in READ. exact READ.
Qed.
Lemma wctype_prefix_back:forall s0 calls j k,wctype_pre s0 ->
  nonzero_prefix (wctype_entry_on s0 (wctype_memory s0 calls) j) (cdecl_arg s0) k ->
  nonzero_prefix (s0 V_MEM32) (cdecl_arg s0) k.
Proof.
  intros s0 calls j k PRE PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i))
    (fun i=>getmem 32 LittleE 1 (wctype_entry_on s0 (wctype_memory s0 calls) j) (cdecl_arg s0+i)) _ k PREFIX).
  intros i P. apply wctype_entry_input_read;assumption.
Qed.
Lemma wctype_ro_read:forall s0 calls i,wctype_pre s0 ->i<73 ->
  getmem 32 LittleE 1 (wctype_memory s0 calls) (wctype_table+i)=wctype_static i.
Proof.
  intros s0 calls i (_ & A & B & C) I. rewrite (wctype_read_region s0 calls wctype_table 73 i B I). exact (C i I).
Qed.
Lemma wctype_entry_ro_read:forall s0 calls j i,wctype_pre s0 ->i<73 ->
  getmem 32 LittleE 1 (wctype_entry_on s0 (wctype_memory s0 calls) j) (wctype_table+i)=wctype_static i.
Proof.
  intros s0 calls j i (_ & A & B & C) I. rewrite (wctype_entry_read_region s0 calls j wctype_table 73 i B I). exact (C i I).
Qed.
Lemma wctype_name_prefix_bound:forall s0 j k,wctype_pre s0 ->j<12 ->
  nonzero_prefix (s0 V_MEM32) (wctype_target j) k ->k<=wctype_length j.
Proof.
  intros s0 j k (_ & A & B & DATA) J PREFIX.
  pose proof (wctype_length_bound j) as L. destruct (N.le_gt_cases k (wctype_length j));[assumption|]. exfalso.
  pose proof (PREFIX (wctype_length j) ltac:(lia)) as NZ.
  unfold wctype_target in NZ. rewrite <- N.add_assoc,DATA in NZ by lia.
  change (wctype_letter j (wctype_length j)<>0) in NZ. exact (NZ (proj1 (wctype_name_shape j J))).
Qed.
Lemma wctype_entry_name_read:forall s0 calls j k,wctype_pre s0 ->j<12 ->
  nonzero_prefix (s0 V_MEM32) (wctype_target j) k ->
  getmem 32 LittleE 1 (wctype_entry_on s0 (wctype_memory s0 calls) j) (wctype_target j+k)=
  getmem 32 LittleE 1 (s0 V_MEM32) (wctype_target j+k).
Proof.
  intros s0 calls j k PRE J PREFIX. pose proof (wctype_name_prefix_bound s0 j k PRE J PREFIX) as K.
  pose proof (wctype_length_bound j) as L. destruct PRE as (_ & A & B & DATA).
  unfold wctype_target. rewrite <- N.add_assoc.
  rewrite wctype_entry_read_region with (n:=73) by (try exact B;lia). reflexivity.
Qed.
Lemma wctype_name_prefix_back:forall s0 calls j k,wctype_pre s0 ->j<12 ->
  nonzero_prefix (wctype_entry_on s0 (wctype_memory s0 calls) j) (wctype_target j) k ->
  nonzero_prefix (s0 V_MEM32) (wctype_target j) k.
Proof.
  intros s0 calls j k PRE J PREFIX. refine (conditional_prefix_transfer
    (fun i=>getmem 32 LittleE 1 (s0 V_MEM32) (wctype_target j+i))
    (fun i=>getmem 32 LittleE 1 (wctype_entry_on s0 (wctype_memory s0 calls) j) (wctype_target j+i)) _ k PREFIX).
  intros i P. apply wctype_entry_name_read;assumption.
Qed.
Lemma wctype_ro_cell:forall s0 i,wctype_pre s0 ->i<73 ->
  ~overlap 32 (msub 32 (s0 R_ESP) 56) 56 (wctype_table+i) 1.
Proof.
  intros s0 i (_ & A & NO & DATA) I. apply noverlap_symmetry.
  eapply noverlap_shrink with (a1:=wctype_table) (len1:=73).
  - rewrite add_msub_l. pose proof (mp2_mod_le i 32). lia.
  - apply noverlap_symmetry;exact NO.
Qed.
Lemma wctype_callee_args:forall s0 calls j sc,j<12 ->
  wctype_frame s0 (wctype_entry_on s0 (wctype_memory s0 calls) j) 48 sc ->
  cdecl_arg sc=cdecl_arg s0 /\ strcmp_arg2 sc=wctype_target j.
Proof.
  intros s0 calls j sc J (MEM & SP & RD & WR).
  unfold cdecl_arg at 1. unfold strcmp_arg2 at 1. rewrite MEM,SP. psimpl.
  unfold wctype_entry_on,wctype_args_on. split;rewrite !deep_saved_word_frame by lia;
    rewrite getmem_setmem by lia;apply N.mod_small.
  - unfold cdecl_arg;apply getmem_bound.
  - unfold wctype_target,wctype_table. lia.
Qed.
Lemma wctype_callee_memory:forall s0 calls j sc,
  wctype_frame s0 (wctype_entry_on s0 (wctype_memory s0 calls) j) 48 sc ->
  sc R_ESI=wctype_target j ->sc R_EBX=wctype_got ->
  save_si_bx_memory sc=wctype_memory s0 (j::calls).
Proof.
  intros s0 calls j sc (MEM & SP & RD & WR) SI BX.
  unfold save_si_bx_memory. rewrite MEM,SP,SI,BX. psimpl. reflexivity.
Qed.
Lemma wctype_callee_pre:forall s0 calls j sc,wctype_pre s0 ->j<12 ->models x86typctx sc ->
  wctype_frame s0 (wctype_entry_on s0 (wctype_memory s0 calls) j) 48 sc ->strcmp_pre sc.
Proof.
  intros s0 calls j sc PRE J MDL F.
  destruct (wctype_callee_args s0 calls j sc J F) as [ARG1 ARG2].
  split;[exact MDL|]. rewrite ARG1,ARG2. split.
  - intros k PREFIX. rewrite (proj1 F) in PREFIX.
    pose proof (wctype_prefix_back s0 calls j k PRE PREFIX) as ORIGINAL.
    pose proof (proj1 (proj2 PRE) k ORIGINAL) as NO.
    rewrite (proj1 (proj2 F)). psimpl. split;
      eapply descending_stack_subregion;[| |exact NO| | |exact NO];lia.
  - intros k PREFIX. rewrite (proj1 F) in PREFIX.
    pose proof (wctype_name_prefix_back s0 calls j k PRE J PREFIX) as ORIGINAL.
    pose proof (wctype_name_prefix_bound s0 j k PRE J ORIGINAL) as K.
    pose proof (wctype_length_bound j) as L.
    pose proof (wctype_ro_cell s0 (6*j+k) PRE ltac:(lia)) as NO.
    rewrite (proj1 (proj2 F)). psimpl. unfold wctype_target. rewrite <- N.add_assoc. split;
      eapply descending_stack_subregion;[| |exact NO| | |exact NO];lia.
Qed.
Lemma wctype_callee_result:forall s0 calls j sc value,wctype_pre s0 ->j<12 ->
  wctype_frame s0 (wctype_entry_on s0 (wctype_memory s0 calls) j) 48 sc ->
  string_compare_result (sc V_MEM32) (cdecl_arg sc) (strcmp_arg2 sc) value ->
  (value=0 <->wctype_matchb s0 j=true).
Proof.
  intros s0 calls j sc value PRE J F RESULT.
  destruct (wctype_callee_args s0 calls j sc J F) as [ARG1 ARG2].
  rewrite ARG1,ARG2,(proj1 F) in RESULT.
  destruct RESULT as (k & K & PREFIX & STOP & VALUE).
  pose proof (proj2 PREFIX) as NZP.
  pose proof (string_equal_prefix_right _ _ _ _ PREFIX) as NZQ.
  pose proof (wctype_prefix_back s0 calls j k PRE NZP) as OP.
  pose proof (wctype_name_prefix_back s0 calls j k PRE J NZQ) as OQ.
  assert (READP:forall i,i<=k ->
    getmem 32 LittleE 1 (wctype_entry_on s0 (wctype_memory s0 calls) j) (cdecl_arg s0+i)=
    getmem 32 LittleE 1 (s0 V_MEM32) (cdecl_arg s0+i)).
  { intros i I. apply wctype_entry_input_read;[exact PRE|]. intros h H. apply OP. clear - H I;lia. }
  assert (READQ:forall i,i<=k ->
    getmem 32 LittleE 1 (wctype_entry_on s0 (wctype_memory s0 calls) j) (wctype_target j+i)=
    getmem 32 LittleE 1 (s0 V_MEM32) (wctype_target j+i)).
  { intros i I. apply wctype_entry_name_read;[exact PRE|exact J|]. intros h H. apply OQ. clear - H I;lia. }
  unfold wctype_matchb. apply fixed_name_compare_zero with (q:=wctype_target j).
  - intros i I. destruct PRE as (_ & A & B & DATA). pose proof (wctype_length_bound j) as L.
    unfold wctype_target,wctype_letter. rewrite <- N.add_assoc,DATA by lia. reflexivity.
  - exact (proj1 (wctype_name_shape j J)).
  - exact (proj2 (wctype_name_shape j J)).
  - exists k. split;[exact K|]. split.
    + split.
      * intros i I. rewrite <- (READP i ltac:(lia)),<- (READQ i ltac:(lia)). exact (proj1 PREFIX i I).
      * exact OP.
    + rewrite <- (READP k (N.le_refl k)),<- (READQ k (N.le_refl k)). split;assumption.
Qed.
Lemma wctype_call_return:forall s0 calls j sc value x se,
  wctype_frame s0 (wctype_entry_on s0 (wctype_memory s0 calls) j) 48 sc ->
  sc R_ESI=wctype_target j ->sc R_EBX=wctype_got ->
  cdecl_returned (save_si_bx_reference sc) value x se ->
  x=Addr 0x351bc /\ wctype_frame s0 (wctype_memory s0 (j::calls)) 44 se /\
  se R_ESI=wctype_target j /\ se R_EBX=wctype_got /\ se R_EBP=sc R_EBP /\ se R_EDI=sc R_EDI /\ se R_EAX=value.
Proof.
  intros s0 calls j sc value x se F SI BX RETURN.
  pose proof (wctype_callee_memory s0 calls j sc F SI BX) as MM.
  pose proof (save_si_bx_stack_word sc 0 ltac:(lia)) as RA. rewrite N.add_0_l in RA.
  destruct F as (MEM & SP & RD & WR).
  unfold cdecl_returned,save_si_bx_reference in RETURN. psimpl in RETURN.
  rewrite RA,MM,MEM,SP,SI,BX,RD,WR in RETURN.
  destruct RETURN as (PC & AX & ESP & MEMORY & EBX & ESI & EDI & EBP & READ & WRITE).
  unfold wctype_entry_on in PC. rewrite getmem_setmem in PC by lia. cbn in PC.
  split;[exact PC|]. split.
  - unfold wctype_frame. rewrite MEMORY,ESP,READ,WRITE. psimpl. repeat split;reflexivity.
  - exact (conj ESI (conj EBX (conj EBP (conj EDI AX)))).
Qed.
Lemma wctype_skip_step:forall s0 j,
  (forall i,i<j ->wctype_matchb s0 i=false) ->wctype_matchb s0 j=false ->
  forall i,i<j+1 ->wctype_matchb s0 i=false.
Proof.
  intros s0 j BEFORE MISS i I. destruct (N.lt_ge_cases i j);[apply BEFORE;assumption|].
  replace i with j by lia. exact MISS.
Qed.
Lemma wctype_table_first_nonzero:forall j,j<12 ->wctype_static (6*j)<>0.
Proof.
  intros j J. pose proof (proj2 (wctype_name_shape j J) 0) as NZ.
  unfold wctype_length in NZ. destruct (j=?11);specialize (NZ ltac:(lia));
    unfold wctype_letter in NZ;rewrite N.add_0_r in NZ;exact NZ.
Qed.
Lemma wctype_saved_bx:forall s0 calls,s0 R_EBX<2^32 ->
  getmem 32 LittleE 4 (wctype_memory s0 calls) (msub 32 (s0 R_ESP) 16)=s0 R_EBX.
Proof.
  intros s0 calls BOUND. rewrite wctype_saved_read by tauto. exact (save4_load_bx s0 None BOUND).
Qed.
Lemma wctype_saved_si:forall s0 calls,s0 R_ESI<2^32 ->
  getmem 32 LittleE 4 (wctype_memory s0 calls) (msub 32 (s0 R_ESP) 12)=s0 R_ESI.
Proof.
  intros s0 calls BOUND. rewrite wctype_saved_read by tauto. exact (save4_load_si s0 None BOUND).
Qed.
Lemma wctype_saved_di:forall s0 calls,s0 R_EDI<2^32 ->
  getmem 32 LittleE 4 (wctype_memory s0 calls) (msub 32 (s0 R_ESP) 8)=s0 R_EDI.
Proof.
  intros s0 calls BOUND. rewrite wctype_saved_read by tauto. exact (save4_load_di s0 None BOUND).
Qed.
Lemma wctype_saved_bp:forall s0 calls,s0 R_EBP<2^32 ->
  getmem 32 LittleE 4 (wctype_memory s0 calls) (msub 32 (s0 R_ESP) 4)=s0 R_EBP.
Proof.
  intros s0 calls BOUND. rewrite wctype_saved_read by tauto. exact (save4_load_bp s0 None BOUND).
Qed.
