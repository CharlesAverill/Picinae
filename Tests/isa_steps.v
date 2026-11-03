(* Behavioral regression tests for native ISA orchestration and its Ltac1 backend.
   Compile through picinae-env: rocq compile -R . Picinae Tests/isa_steps.v *)
From Stdlib Require Import NArith List.
Require Import Picinae_i386.
Open Scope N_scope.

(* Conditional execution exercises both continuation shapes: a conditional
   statement alone and a conditional followed by another statement. *)
Definition branch_code (_:store) (_:addr) :=
  Some (1, If (BinOp OP_EQ (Var R_EAX) (Word 0 32))
    (Seq (Move (V_TEMP 0) (Unknown 32)) (Jmp (Word 2 32)))
    (Jmp (Word 3 32))).
Definition branch_invs (initial:store) (t:trace) :=
  match t with
  | (Addr 0,_)::_ => None
  | (_,s)::_ => Some (s (V_TEMP 0) = initial (V_TEMP 0))
  | _ => None
  end.
Goal forall s, nextinv branch_code (branch_invs s) (fun _ => false)
  false ((Addr 0,s)::nil) /\
  nextinv branch_code (branch_invs s) (fun _ => false)
  false ((Addr 0,s)::nil).
Proof. intro s. split; [ x86_step | x86_step_ltac1 ]; reflexivity. Qed.

Definition seq_code (_:store) (_:addr) :=
  Some (1, Seq (If (BinOp OP_EQ (Var R_EAX) (Word 0 32))
    (Move R_EBX (Word 7 32)) (Move R_EBX (Word 9 32)))
    (Move (V_TEMP 0) (Unknown 32))).
Definition seq_invs (initial:store) (t:trace) :=
  match t with
  | (Addr 0,_)::_ => None
  | (Addr 1,s)::_ => Some (s (V_TEMP 0) = initial (V_TEMP 0) /\
      (s R_EBX = 7 \/ s R_EBX = 9))
  | _ => None
  end.
Goal forall s, nextinv seq_code (seq_invs s) (fun _ => false)
  false ((Addr 0,s)::nil) /\
  nextinv seq_code (seq_invs s) (fun _ => false)
  false ((Addr 0,s)::nil).
Proof.
  intro s. split; [ x86_step | x86_step_ltac1 ];
    (split; [ reflexivity | first [left; reflexivity | right; reflexivity] ]).
Qed.

(* Clearing stale memory facts must precede invariant fallback. *)
Goal forall s, MemAcc mem_readable s 5 32 1 ->
  nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => false) true nil /\
  nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => false) true nil.
Proof.
  intros s OLD. split; [ x86_step | x86_step_ltac1 ];
    tryif match goal with [ _:MemAcc _ _ _ _ _ |- _ ] => idtac end
      then fail "Stale memory access fact" else exact I.
Qed.

(* The low-level helper preserves symbolic iteration for user loop proofs. *)
Goal forall c s c' s' x,
  exec_stmt c s (Rep (Unknown 8) Nop) c' s' x -> True.
Proof.
  intros c s c' s' x XS. ISA_step_and_simplify XS.
  lazymatch type of XS with exec_stmt _ _ (N.iter _ _ _) _ _ _ => idtac end.
  exact I.
Qed.

(* At the instruction level a symbolic Rep is also left available for user
   loop reasoning; the repeat must terminate before invariant dispatch. *)
Definition rep_code (_:store) (_:addr) := Some (1, Rep (Var R_EAX) Nop).
Goal forall s,
  nextinv rep_code (fun _ => Some True) (fun _ => false) false ((Addr 0,s)::nil) /\
  nextinv rep_code (fun _ => Some True) (fun _ => false) false ((Addr 0,s)::nil).
Proof.
  intro s. split; [ x86_step | x86_step_ltac1 ];
    lazymatch goal with [ _:exec_stmt _ _ (N.iter _ _ _) _ _ _ |- _ ] => exact I end.
Qed.

(* A user hook may branch.  Every resulting goal must receive the remaining
   simplification stages, just as with the original Ltac1 semicolon chain. *)
Module BranchingHook.
Local Ltac simpl_memaccs H ::= split.
Goal forall c s c' s' x, exec_stmt c s Nop c' s' x -> True /\ True.
Proof.
  intros c s c' s' x XS.
  ISA_step_and_simplify XS;
    lazymatch type of XS with reset_temps _ _ = _ /\ _ = _ => exact I end.
Qed.
Goal forall c s c' s' x, exec_stmt c s Nop c' s' x -> True /\ True.
Proof.
  intros c s c' s' x XS.
  ISA_step_and_simplify_ltac1 XS;
    lazymatch type of XS with reset_temps _ _ = _ /\ _ = _ => exact I end.
Qed.
End BranchingHook.

(* The simplifier is also an overridable hook in the generic ISA interface. *)
Module BranchingSimplifierHook.
Local Ltac psimpl_hyp H ::= split.
Goal forall c s c' s' x, exec_stmt c s Nop c' s' x -> True /\ True.
Proof.
  intros c s c' s' x XS. ISA_step_and_simplify XS;
    lazymatch type of XS with reset_temps _ _ = _ /\ _ = _ => exact I end.
Qed.
End BranchingSimplifierHook.

(* Unknown applications become independent opaque variables, and the oracle
   disappears after every application in the execution result is abstracted. *)
Goal forall s c' s' x, exec_stmt archtyps s
  (Move R_EAX (BinOp OP_PLUS (Unknown 32) (Unknown 32))) c' s' x -> True.
Proof.
  intros s c' s' x XS. ISA_step_and_simplify XS.
  match goal with [ n1:N, n2:N |- _ ] => is_var n1; is_var n2 end.
  tryif match goal with [ oracle:positive -> N |- _ ] => idtac end
    then fail "Unknown oracle was not cleared" else idtac.
  exact I.
Qed.

(* Repeated loads generate duplicate access facts through different stores.
   The ISA hook must remove unrelated register updates before de-duplication. *)
Goal forall s c' s' x, exec_stmt archtyps s
  (Seq (Move R_EAX (Load (Var V_MEM32) (Word 5 32) LittleE 1))
       (Move R_EBX (Load (Var V_MEM32) (Word 5 32) LittleE 1))) c' s' x ->
  MemAcc mem_readable s 5 32 1.
Proof.
  intros s c' s' x XS. ISA_step_and_simplify XS.
  tryif match goal with [ A:MemAcc _ _ _ _ _, B:MemAcc _ _ _ _ _ |- _ ] => idtac end
    then fail "Duplicate memory access fact" else idtac.
  assumption.
Qed.

Module IgnoredVariables.
Local Ltac ignore_vars v ::= constr:(match v with R_EAX => true | _ => false end).
Ltac native_abstract H :=
  let f := ltac2:(h |- isa_abstract_ignored_vars (picinae_hyp_ident h)) in f H.
Ltac check_ignored H :=
  lazymatch type of H with
  | update (update (update ?s R_EAX ?old) R_EAX ?n) R_EBX (?x+2) = ?s' =>
      is_var old; is_var n
  end.
Goal forall (s:store) (n:N),
  update (update (update s R_EAX n) R_EAX (n+1)) R_EBX (n+2) = s -> True.
Proof. intros s n H. native_abstract H. check_ignored H. exact I. Qed.
Goal forall (s:store) (n:N),
  update (update (update s R_EAX n) R_EAX (n+1)) R_EBX (n+2) = s -> True.
Proof. intros s n H. abstract_ignored_vars H. check_ignored H. exact I. Qed.
End IgnoredVariables.

(* A dependent goal can prevent clearing the terminal True accumulator.  The
   original helper stops its repeat and still succeeds in that situation. *)
Goal forall XS:True /\ True, XS = XS.
Proof. intro XS. ltac2:(isa_destruct_memaccs @XS). reflexivity. Qed.
Goal forall XS:True /\ True, XS = XS.
Proof. intro XS. destruct_memaccs XS. reflexivity. Qed.

(* Projection can also be blocked by a proof dependency. Do not backtrack to
   the non-duplicate branch and split off an extra copy of P in that case. *)
Goal forall (P:Prop) (proof:P) (XS:True /\ (P /\ True)), XS = XS.
Proof.
  intros P proof XS. ltac2:(isa_destruct_memaccs @XS).
  lazymatch goal with [ ACCs:P /\ True |- _ ] => idtac end.
  reflexivity.
Qed.
Goal forall (P:Prop) (proof:P) (XS:True /\ (P /\ True)), XS = XS.
Proof.
  intros P proof XS. destruct_memaccs XS.
  lazymatch goal with [ ACCs:P /\ True |- _ ] => idtac end.
  reflexivity.
Qed.

(* Both ISA entry-point graphs remain usable independently. A call to the other
   ISA backend is made an immediate failure. The legacy path also disables the
   public simplifier hooks to ensure it uses the explicit legacy entry points. *)
Module NativeOnly.
Local Ltac ISA_step_ltac1 ::= fail "Legacy ISA dispatcher called".
Local Ltac ISA_invseek_ltac1 ::= fail "Legacy instruction stepping called".
Local Ltac ISA_invhere_ltac1 ::= fail "Legacy invariant stepping called".
Local Ltac ISA_step_and_simplify_ltac1 H ::= fail "Legacy simplification called".
Local Ltac step_stmt H ::= fail "Legacy statement dispatcher called".
Local Ltac abstract_ignored_vars H ::= fail "Legacy abstraction called".
Local Ltac destruct_memaccs H ::= fail "Legacy memory dispatcher called".
Goal forall s, nextinv seq_code (seq_invs s) (fun _ => false)
  false ((Addr 0,s)::nil).
Proof.
  intro s. x86_step;
    (split; [ reflexivity | first [left; reflexivity | right; reflexivity] ]).
Qed.
End NativeOnly.

Module LegacyOnly.
Local Ltac ISA_step ::= fail "Native ISA dispatcher called".
Local Ltac ISA_invseek ::= fail "Native instruction stepping called".
Local Ltac ISA_invhere ::= fail "Native invariant stepping called".
Local Ltac ISA_step_and_simplify H ::= fail "Native simplification called".
Local Ltac psimpl_hyp H ::= fail "Native simplifier called".
Local Ltac psimpl_goal ::= fail "Native simplifier called".
Goal forall s, nextinv seq_code (seq_invs s) (fun _ => false)
  false ((Addr 0,s)::nil).
Proof.
  intro s. x86_step_ltac1;
    (split; [ reflexivity | first [left; reflexivity | right; reflexivity] ]).
Qed.
End LegacyOnly.

(* Loading all five ISAs must not redirect an earlier alias to the last loaded
   module. Each alias executes a real conditional instruction and its hooks. *)
Require Import Picinae_amd64 Picinae_armv7 Picinae_armv8 Picinae_riscv.

Module Alias_i386.
Import Picinae_i386 IL_i386 Theory_i386 ISA_i386.
Definition code (_:store) (_:addr) := Some (1,
  Seq (If (Var R_EAX) (Move R_EAX (Word 7 32)) (Move R_EAX (Word 9 32)))
      (Move (V_TEMP 0) (Unknown 32))).
Definition invs (initial:store) (t:trace) := match t with
  | (Addr 0,_)::_ => None
  | (Addr 1,s)::_ => Some (s (V_TEMP 0) = initial (V_TEMP 0) /\
      (s R_EAX = 7 \/ s R_EAX = 9))
  | _ => None end.
Goal forall s, nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil) /\
  nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil).
Proof.
  intro s. split; [ x86_step | x86_step_ltac1 ];
    (split; [ reflexivity | first [left; reflexivity | right; reflexivity] ]).
Qed.

Goal forall s c' s' x, exec_stmt archtyps s
  (Seq (Move R_EAX (Load (Var V_MEM32) (Word 5 32) LittleE 1))
       (Move R_EBX (Load (Var V_MEM32) (Word 5 32) LittleE 1))) c' s' x ->
  MemAcc mem_readable s 5 32 1.
Proof.
  intros s c' s' x XS. ISA_step_and_simplify XS.
  tryif match goal with [ A:MemAcc _ _ _ _ _, B:MemAcc _ _ _ _ _ |- _ ] => idtac end
    then fail "Duplicate memory access fact" else idtac.
  assumption.
Qed.
End Alias_i386.

Module Alias_amd64.
Import Picinae_amd64 IL_amd64 Theory_amd64 ISA_amd64.
Definition code (_:store) (_:addr) := Some (1,
  Seq (If (Var R_RAX) (Move R_RAX (Word 7 64)) (Move R_RAX (Word 9 64)))
      (Move (V_TEMP 0) (Unknown 64))).
Definition invs (initial:store) (t:trace) := match t with
  | (Addr 0,_)::_ => None
  | (Addr 1,s)::_ => Some (s (V_TEMP 0) = initial (V_TEMP 0) /\
      (s R_RAX = 7 \/ s R_RAX = 9))
  | _ => None end.
Goal forall s, nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil) /\
  nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil).
Proof.
  intro s. split; [ x64_step | x64_step_ltac1 ];
    (split; [ reflexivity | first [left; reflexivity | right; reflexivity] ]).
Qed.

Goal forall s c' s' x, exec_stmt archtyps s
  (Seq (Move R_RAX (Load (Var V_MEM64) (Word 5 64) LittleE 1))
       (Move R_RBX (Load (Var V_MEM64) (Word 5 64) LittleE 1))) c' s' x ->
  MemAcc mem_readable s 5 64 1.
Proof.
  intros s c' s' x XS. ISA_step_and_simplify XS.
  tryif match goal with [ A:MemAcc _ _ _ _ _, B:MemAcc _ _ _ _ _ |- _ ] => idtac end
    then fail "Duplicate memory access fact" else idtac.
  assumption.
Qed.
End Alias_amd64.

Module Alias_armv7.
Import Picinae_armv7 IL_arm7 Theory_arm7 ISA_arm7.
Definition code (_:store) (_:addr) := Some (1,
  Seq (If (Var R_R0) (Move R_R0 (Word 7 32)) (Move R_R0 (Word 9 32)))
      (Move (V_TEMP 0) (Unknown 32))).
Definition invs (initial:store) (t:trace) := match t with
  | (Addr 0,_)::_ => None
  | (Addr 1,s)::_ => Some (s (V_TEMP 0) = initial (V_TEMP 0) /\
      (s R_R0 = 7 \/ s R_R0 = 9))
  | _ => None end.
Goal forall s, nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil) /\
  nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil).
Proof.
  intro s. split; [ arm7_step | arm7_step_ltac1 ];
    (split; [ reflexivity | first [left; reflexivity | right; reflexivity] ]).
Qed.

Goal forall s c' s' x, exec_stmt archtyps s
  (Seq (Move R_R0 (Load (Var V_MEM32) (Word 5 32) LittleE 1))
       (Move R_R1 (Load (Var V_MEM32) (Word 5 32) LittleE 1))) c' s' x ->
  MemAcc mem_readable s 5 32 1.
Proof.
  intros s c' s' x XS. ISA_step_and_simplify XS.
  tryif match goal with [ A:MemAcc _ _ _ _ _, B:MemAcc _ _ _ _ _ |- _ ] => idtac end
    then fail "Duplicate memory access fact" else idtac.
  assumption.
Qed.
End Alias_armv7.

Module Alias_armv8.
Import Picinae_armv8 IL_arm8 Theory_arm8 ISA_arm8.
Definition code (_:store) (_:addr) := Some (1,
  Seq (If (Var R_X0) (Move R_X0 (Word 7 64)) (Move R_X0 (Word 9 64)))
      (Move (V_TEMP 0) (Unknown 64))).
Definition invs (initial:store) (t:trace) := match t with
  | (Addr 0,_)::_ => None
  | (Addr 1,s)::_ => Some (s (V_TEMP 0) = initial (V_TEMP 0) /\
      (s R_X0 = 7 \/ s R_X0 = 9))
  | _ => None end.
Goal forall s, nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil) /\
  nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil).
Proof.
  intro s. split; [ arm8_step | arm8_step_ltac1 ];
    (split; [ reflexivity | first [left; reflexivity | right; reflexivity] ]).
Qed.

Goal forall s c' s' x, exec_stmt archtyps s
  (Seq (Move R_X0 (Load (Var V_MEM64) (Word 5 64) LittleE 1))
       (Move R_X1 (Load (Var V_MEM64) (Word 5 64) LittleE 1))) c' s' x ->
  MemAcc mem_readable s 5 64 1.
Proof.
  intros s c' s' x XS. ISA_step_and_simplify XS.
  tryif match goal with [ A:MemAcc _ _ _ _ _, B:MemAcc _ _ _ _ _ |- _ ] => idtac end
    then fail "Duplicate memory access fact" else idtac.
  assumption.
Qed.
End Alias_armv8.

Module Alias_riscv.
Import Picinae_riscv IL_RISCV Theory_RISCV ISA_RISCV.
Definition code (_:store) (_:addr) := Some (1,
  Seq (If (Var R_T0) (Move R_T0 (Word 7 32)) (Move R_T0 (Word 9 32)))
      (Move V_TMP (Unknown 32))).
Definition invs (initial:store) (t:trace) := match t with
  | (Addr 0,_)::_ => None
  | (Addr 1,s)::_ => Some (s V_TMP = initial V_TMP /\
      (s R_T0 = 7 \/ s R_T0 = 9))
  | _ => None end.
Goal forall s, nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil) /\
  nextinv code (invs s) (fun _ => false) false ((Addr 0,s)::nil).
Proof.
  intro s. split; [ r5_step | r5_step_ltac1 ];
    (split; [ reflexivity | first [left; reflexivity | right; reflexivity] ]).
Qed.

Goal forall s c' s' x, exec_stmt archtyps s
  (Seq (Move R_T0 (Load (Var V_MEM32) (Word 5 32) LittleE 1))
       (Move R_T1 (Load (Var V_MEM32) (Word 5 32) LittleE 1))) c' s' x ->
  MemAcc mem_readable s 5 32 1.
Proof.
  intros s c' s' x XS. ISA_step_and_simplify XS.
  tryif match goal with [ A:MemAcc _ _ _ _ _, B:MemAcc _ _ _ _ _ |- _ ] => idtac end
    then fail "Duplicate memory access fact" else idtac.
  assumption.
Qed.
End Alias_riscv.
