Require Export Picinae_pilbox32.
Require Export Picinae_pilbox32_interpreter.

Require Import NArith.
Require Import ZArith.
Require Import List.
Open Scope N.
Import ListNotations.

Definition id := N.

(* iid - id for the instruction
   oid - id to check for with dynamic jumps
   n   - instruction encoding
   a   - instruction address *)
Inductive inst_data := Data (iid: option id) (oid: list id) (n: N) (a: N).

(* generate code to check for each id in a list
   ids - list of valid destination ids
   r0  - register with the real id
   r1  - scratch register to load constants into *)
Fixpoint check_id_insts (ids: list id) (r0: N) (r1: N): list p32_asm :=
  match ids with
  | id::t => let tail := check_id_insts t r0 r1 in
      [
        PIL_li r1 id;                                    (* load next valid id *)
        PIL_beq r0 r1 (4 + 4 * Z.of_nat (length tail))   (* if match, branch to the end *)
      ] ++ tail                                          (* otherwise, check the rest of the ids *)
  | nil => [PIL_beq 0 0 0]                               (* no valid ids, abort (infinite loop) *)
  end.

(* add an id check to a jmpr instruction
   data - data of the jmpr instruction
   rs1  - register that holds the destination *)
Definition rewrite_jmpr (data: inst_data) (rs1: N) : list N :=
  let r0 := if rs1 == 0 then 2 else 0 in
  let r1 := if rs1 == 1 then 2 else 1 in
  let sp := 6 in
  match data with Data _ oid _ _ =>
    map assemble_insn ([
      PIL_st   r0  sp  0;                (* save r0 and r1 to the stack *)
      PIL_st   r1  sp  4;
      PIL_ld   r0  rs1 4                 (* load the real id *)
    ] ++ check_id_insts oid r0 r1 ++ [   (* compare against all valid id *)
      PIL_ld   r0  sp  0;                (* restore r0 and r1 *)
      PIL_ld   r1  sp  4;
      PIL_jmpr rs1                       (* jump *)
    ]) end.

(* add a label to a rewritten instruction
   i    - id of the instruction
   rw_n - rewritten encoding of a single instruction *)
Definition add_id (i: option id) (rw_n: list N) : list N :=
  match i with
  | Some i => assemble_insn (PIL_beq 0 0 8)::i::rw_n
  | None => rw_n
  end.

(* rewrite a single instruction
   data - data of the instruction to rewrite *)
Definition rewrite_inst (data: inst_data) : list N :=
  match data with Data id _ n _ =>
    let inst := p32_decode n in
    let new_n := match inst with
                 | PIL_jmpr rs1 => rewrite_jmpr data rs1
                 | _ => n::nil
                 end in
    add_id id new_n
  end.

(* get a list of the new starting addresses for each old instruction
   rw_ns - list of all rewritten instruction encodings
   a     - base address *)
Fixpoint new_addrs (rw_ns: list (list N)) (a: N) : list N :=
  match rw_ns with
  | n::ns => a::new_addrs ns (a + 4 * N.of_nat (length n))
  | _ => a::nil (* also add the address of the end of the program, so we can compute last_addrs easily *)
  end.

(* get the immediate value of a jump/branch instruction
   inst - the instruction *)
Definition get_imm (inst: p32_asm) :=
  match inst with
  | PIL_beq rs1 rs2 si => si
  | PIL_blt rs1 rs2 si => si
  | PIL_bne rs1 rs2 si => si
  | PIL_bl si => si
  | PIL_jl i => Z.of_N i
  | PIL_jmp i => Z.of_N i
  | _ => 0%Z
  end.

(* get a list of the new destination addresses of jump/branch instructions in the original program
   data      - data of the original program
   new_addrs - new starting addresses of each instruction in the rewritten program
   base      - base address of the program *)
Fixpoint new_targets (data: list inst_data) (new_addrs: list N) (base: N) : list N :=
  match data with
  | Data _ _ n a::t => nth match p32_decode n with
                           | PIL_beq _ _ _ | PIL_blt _ _ _ | PIL_bne _ _ _ | PIL_bl _ => (Z.to_nat ((Z.of_N a) + get_imm (p32_decode n)) - N.to_nat base) / 4
                           | PIL_jl _ | PIL_jmp _ => (Z.to_nat (get_imm (p32_decode n)) - N.to_nat base) / 4
                           | _ => 0
                       end new_addrs 0::new_targets t new_addrs base
  | _ => nil
  end.

(* change the destination of a direct jump/branch, does nothing if a different instruction, returns None if the target is not reachable
   n        - encoding of the instruction
   a        - address of the instruction
   new_dest - new address the instruction should go to *)
Definition replace_target (n: N) (a: N) (new_dest: N) : option N :=
  let new_inst := match p32_decode n with
                  | PIL_beq rs1 rs2 si => PIL_beq rs1 rs2 (Z.of_N new_dest - Z.of_N a)
                  | PIL_blt rs1 rs2 si => PIL_blt rs1 rs2 (Z.of_N new_dest - Z.of_N a)
                  | PIL_bne rs1 rs2 si => PIL_blt rs1 rs2 (Z.of_N new_dest - Z.of_N a)
                  | PIL_bl si => PIL_bl (Z.of_N new_dest - Z.of_N a)
                  | PIL_jl i => PIL_jl new_dest
                  | PIL_jmp i => PIL_jmp new_dest
                  | a => a end in
  let new_n := assemble_insn new_inst in
  (* check if the immediate value is representable in the instruction encoding *)
  if Z.eqb (get_imm (p32_decode new_n)) (get_imm new_inst) then Some new_n else None.

(* replace the last element of a list *)
Fixpoint replace_last {T: Type} (ts: list T) (last: T) : list T :=
  match ts with
  | a::nil => last::nil
  | a::t => a::replace_last t last
  | nil => nil
  end.

(* fix the destinations of the jump/branch instructions of a rewritten program, return None if an instruction could not be fixed
   ns             - list of instruction encodings of the original program
   last_addrs     - list of addresses of the last instruction of each rewritten instruction
                      (we only need to fix the last instruction,
                       since the rewriter only prepends instructions to each original instruction,
                       and the inserted jumps/branches are already correct)
   new_targets    - list of new targets for each original instruction (ignored if not a jump)
   rewritten_prog - rewritten program to fix the jump targets of *)
Fixpoint fix_targets (ns: list N) (last_addrs: list N) (new_targets: list N) (rewritten_prog: list (list N)) : option (list (list N)) :=
  match ns, last_addrs, new_targets, rewritten_prog with
  | n::ns, last_addr::last_addrs, new_target::new_targets, rewritten_n::rewritten_prog =>
      let new_last := (replace_target n last_addr new_target) in
      let rest := fix_targets ns last_addrs new_targets rewritten_prog in
      match new_last, rest with
      | Some new_last, Some rest => Some (replace_last rewritten_n new_last::rest)
      | _, _ => None end
  | _, _, _, _ => Some nil
  end.

(* turn a list of inst encodings to a list of inst_data
   label - instruction labeling
   pol   - policy to enforce
   ns    - list of instruction encodings
   a     - starting address *)
Fixpoint to_data (label: N -> option id) (pol: N -> list id) (ns: list N) (a: N) : list inst_data :=
  match ns with
  | n::ns => (Data (label a) (pol a) n a)::(to_data label pol ns (a+4))
  | nil => nil
  end.

(* rewrite a program
   label - instruction labeling
   pol   - policy to enforce
   ns    - list of instruction encodings of the program
   a     - starting address of the program *)
Definition rewrite (label: N -> option id) (pol: N -> list id) (ns: list N) (a: N) : list (list N) :=
  let data := to_data label pol ns a in
  let rewritten_prog := map rewrite_inst data in
  (* everything after is just to fix jump/branch targets from the original program *)
  let new_addrs := new_addrs rewritten_prog a in
  let new_targets := new_targets data new_addrs a in
  let last_addrs := (map (fun a => a-4) (tail new_addrs)) in
  match fix_targets ns last_addrs new_targets rewritten_prog with
  | Some fixed => fixed
  | None => nil
  end.

(* get all ids used in a labeling
   label - instruction labeling
   ns - original program encoding
   a - starting address of the program *)
Fixpoint all_ids (label: N -> option id) (ns: list N) (a: N) : list id :=
  match ns, label a with
  | n::t, Some id => id::all_ids label t (a+4)
  | n::t, None => all_ids label t (a+4)
  | nil, _ => nil
  end.

(* rewrite a program, but return nil if an id appears in the rewritten program where it shouldn't *)
Definition rewrite_check_id (label: N -> option id) (pol: N -> list id) (ns: list N) (a: N)  :=
  (* first, rewrite the program using a labeling only with Ns we already know appear in the rewritten program *)
  let label' := (fun a => match label a with
                          (* we know that this instruction will be added to the program *)
                          | Some _ => Some (assemble_insn (PIL_beq 0 0 8))
                          | _ => None end) in
  let rw := concat (rewrite label' pol ns a) in
  (* now check if any of the ids appear in the new program *)
  let all_ids := all_ids label ns a in
  let any_id_in_rw := existsb (fun id => existsb (fun n => N.eqb id n) rw) all_ids in
  if any_id_in_rw then nil else rewrite label pol ns a.

(*** simple test ***)

Definition my_label n :=
  match n with
  | 0 => Some 1
  | 16 => Some 111
  | 20 => Some 222
  | _ => None
  end.

Definition my_policy n :=
  match n with
  | 0 => [111]
  | 12 => [222; 123; 232232323]
  | _ => [333]
  end.

Definition my_prog := (* random gibberish *)
  map assemble_insn [
    PIL_add 0 0 1;
    PIL_add 3 1 2;
    PIL_bl 12;
    PIL_jmpr 3;
    PIL_jmpr 2;
    PIL_bl 8;
    PIL_bl (-8);
    PIL_bl (-8);
    PIL_bl 0
  ].

Definition my_rewritten_prog := rewrite my_label my_policy my_prog 0.
Compute my_prog.
Compute my_rewritten_prog.
Compute map (map p32_decode) my_rewritten_prog.

(* This Section defines properties of rewriters with an aim of being general.
   In other words, this should be reusable for rewriters implemented in different
   ways. E.g. we define a Property of indices (N), `is_abort`, that is agnostic
   to the definition of this property.

   The safety property is formalized according to the email thread we had.

   The other two properties, `rewritten_is_faithful` and `original_has_simulation`
   are formalized according to the paper "Sound Transpilation from Binary␍
   to Machine-Independent Code"  with signifcant differences from reasoning about
   an assembly program that lives in the same address space as memory writes, 
   rather than a BIL program.

   Below, when we say 'executions' we mean an exeuction trace of an original binary
   and its corresponding execution on the rewritten binary. *)
Section RRCorrectness.
  (* Parameters: |-- label  --|      |- policy -|     program  entry *)
  Variable rr : (N -> option id) -> (N -> list id) -> list N -> N -> option (list (list N)).
  Variable label : N -> option id.
  Variables policy : N -> list id.
  Variable program  : list N.
  Variable entry : addr.
  Variable program' : list (list N).
  Variable is_abort : N -> Prop.
  (* Added `is_aborted` as a trace Property for easy reading, but similar
     name may be confusing. *)
  Variable is_aborted : trace -> Prop.
  (* For correctness we're reasoning over traces which operate at the
     level of addresses* so we need to translate from an address to the 
     corresponding index. 

    * really `exits`, defined in Picinae_core.v, which can be exceptions,
      but that's irrelevant here *)
  Variable index_of_addr : addr -> option N.

  (* Difine a similarity of states proposition that must hold between
     the states of executions at the beginning of each block.

     E.g. 
     Definition similar_states s1 s2 : Prop :=
        forall v, match v with
        | R_R0 | R_R1 | R_R2 
        | R_R3 | R_R4 | R_R5 
        | R_SP | R_LR | R_PC => s1 v = s2 v
        | _ => True
        end.
   *)
  Variable similar_states : store -> store -> Prop.
  Variables binary binary' : N.

  (* find and return the length of the smallest prefix of r's output list whose 
    list-flattened length equals or exceeds index.
    Think of iindex n as the nth instruction in the flattened rrprog - instruction index,
    The output is the number of blocks you need to take from rrprog the block with 
      that instruction.
    If the list is empty then the iindex is out of bounds... return 0 I guess... *)
  Fixpoint block_index_impl (rrprog : list (list N)) (iindex : N) : N :=
    match rrprog with
    | [] => 0%N
    | h :: t => 
        (* Here the comparison is `Gt` because an n element list goes up to index n-1, not n *)
        match N.compare (N.of_nat (length h)) iindex with
        | Gt => 1
        | _ =>  N.succ (block_index_impl t (iindex - (N.of_nat (length h))))
        end
    end.

  Print stepsof.

  Definition block_index (iindex : N) : N := block_index_impl program' iindex.

  (* Helper function to get the total length (number of instructions) in the first n blocks of rrprog *)
  Definition block_prefix_length (rrprog : list (list N)) (num_blocks : nat) : N:=
    N.of_nat (List.fold_left (fun acc l => acc + (length l))%nat (firstn num_blocks rrprog) O).

  (* True iff iindex is the index of a first instruction within a block output by r *)
  Definition block_start (iindex : N) : Prop :=
    (* Reasoning:
       If the first n-1 blocks have |iindex| instructions then the instruction at iindex
       is the first (0th) instruction of block n. *)
    match N.compare (block_prefix_length program' (N.to_nat (N.pred (block_index iindex)))) iindex with
    | Eq => True
    | _ => False
    end.
  
  Fixpoint reverse {A:Type} (l:list A) := List.fold_left (fun acc x => x::acc) l [].

  Fixpoint flatten_1 {A:Type} (l:list (list A)) : list A :=
    List.fold_left (fun acc l => acc ++ l) l [].

  Definition code_prop (s : store) (code : list N) (base_addr:N) : Prop :=
    (* Memory stores the program *)
    xnbits (s V_MEM32) (base_addr * 8) ((4 * (N.of_nat (length code))) * 8) =
      List.fold_left (fun acc insn => cbits acc 32 insn) (reverse code) 0
    (* The program is executable *)
    /\ xnbits (s A_EXEC) base_addr (4 * (N.of_nat (length code))) = N.ones (4 * (N.of_nat (length code)))
    (* The program is not writeable *)
    /\ xnbits (s A_WRITE) base_addr (4 * (N.of_nat (length code))) = 0.


  (* I decided to make Pol take an `option id` instead of `id`. We can revisit this.
     Reasoning: `label` is a partial function so it returns an option. Allowing Pol
     to take an option and including the hypothesis that it is never true for 'None'
     seemed like an easier interface for expressing the RPol definition rather than
     adding another helper function or redirection. *)
  Variable Pol : addr -> option id -> Prop.
  Hypothesis PolNeverNone : forall a opt_id, Pol a opt_id -> exists id, opt_id = Some id.
  Definition RPol (addr_from addr_to : addr) :=
    Pol (block_index addr_from) (label (block_index addr_to)) /\ block_start addr_to (* policy-permitted jump *)
      \/ block_index addr_from = block_index addr_to (* execution hasn't left the current block yet *)
      \/ is_abort addr_to. (* jumps to "abort" are always safe *)

  (* This wraps RPol, handling inputs of steps of traces of the form
     (final exit-store pair, initial exit-store pair).

     I'm undecided whether we should prove anything if either exit is
     not an Addr - i.e. a hardware execution occurred. 

     This could reasonably happen in a program, but with the proposed
     CFG definition we cannot list any such jumps as OK because we
     assume all jumps are from code to code.
   *)
  Definition RPolStep (xs_xs : ((exit * store) * (exit * store))) :=
    match xs_xs with
    | ((Addr addr_to,_), (Addr addr_from,_)) => RPol addr_from addr_to
    | _ => True 
    end.


  (* For safety we only care that the trace respects the policy.
     Below, in `correctness`, we'll prove that the rewritten program
     behaves similarly to the original. *)
  Definition safety :=
    (*  t' - the trace of the executions of program and program' resp. 
        s0' - the initial store of the executions.
     *)
    forall (t' : trace) (s0' : store) (xs' : prod exit store)
    (RR: rr label policy program entry = Some program')
    (* Both traces start at the entry *)
    (ENTRY: startof t' xs' = (Addr entry, s0'))
    (* Relate the program given as a list of instruction encodings with the initial store *)
    (BIN: code_prop s0' (flatten_1 program') entry)
    (* The trace represents a valid execution of the program *)
    (EXEC: exec_prog p32_prog t'),
      Forall RPolStep (stepsof t').

  (*  An adaptation of the 1st part of Theorem 1 (page 204) from 
      "Sound Transpilation from Binary to Machine-Independent Code"
      by Metere et al. 

      This states that all executions by the original either have a
      corresponding execution that catches up to a similar end state
      or aborts. *)
  Definition original_has_simulation :=
    (* program' is the rewritten program *)
    forall (RR: rr label policy program entry = Some program'),
    forall (t : trace) (s0 s0' : store) (xs : prod exit store)
    (* Both traces start at the entry *)
    (ENTRY: startof t xs = (Addr entry,s0))
    (* Relate the program given as a list of instruction encodings with the initial store *)
    (BIN: code_prop s0 program entry /\ code_prop s0' (flatten_1 program') entry)
    (* The trace represents a valid execution of the program *)
    (EXEC: exec_prog p32_prog t)
    (* Assert the initial states are similar *)
    (SIM: similar_states s0 s0')
    (* The program has taken at least 1 step *)
    (STEPS: (length t > 1)%nat),
    (* There is a trace of the rewritten program that simulates the original or aborts *)
      exists (t' : trace) (xs' : prod exit store), 
         startof t' xs' = (Addr entry, s0') ->
         exec_prog p32_prog t' ->
         (length t' > 1)%nat 
         /\ (is_aborted t' \/ match t, t' with 
                              | (_,s)::_, (_,s')::_  => similar_states s s' 
                              | _, _ => False 
                              end).

  (*  An adaptation of the second part (see above). 
    
      This states that all executions by the rewritten program that end at the
      beginning of a rewritten block (corresponding to just before the execution
      of the instruction) and have not aborted have a corresponding execution
      of the original program that catchus up to them. *)
  Definition rewritten_is_faithful :=
    (* program' is the rewritten program *)
    forall (RR: rr label policy program entry = Some program'),
    (*  t,t' - the trace of the executions of program and program' resp. 
        s0,s0' - the initial store of the executions.
        xs,xs' - the "current" exit-store pair of the executions.
     *)
    forall (t' : trace) (s0 s0' s': store) (xs xs' : prod exit store) (a':addr)
    (* Both traces start at the entry *)
    (ENTRY: startof t' xs' = (Addr entry, s0'))
    (* Relate the program given as a list of instruction encodings with the initial store *)
    (BIN: code_prop s0 program entry /\ code_prop s0' (flatten_1 program') entry)
    (* The trace represents a valid execution of the program *)
    (EXEC': exec_prog p32_prog t')
    (* Assert the initial states are similar *)
    (SIM: similar_states s0 s0')
    (STEPS': (length t' > 1)%nat)
    (* Bind the latest state of t' to the start of a block. *)
    (XS' : head t' = Some xs' /\ xs' = (Addr a', s'))
    (START': match index_of_addr a' with Some n => block_start n | _ => False end)
    (UNTERM': is_aborted t' -> False),
      exists (t:trace), forall (a:addr) (s:store)
      (START: startof t xs = (Addr entry,s0))
      (STEPS: (length t > 1)%nat)
      (END: head t = Some (Addr a, s)),
      exec_prog p32_prog t /\ similar_states s s'.
End RRCorrectness.

Definition p32_rr label pol program entry :=
  Some (rewrite_check_id label pol program entry).

Theorem forall_stepsof_ind :
  forall (X:Type) (P: X * X -> Prop)
    (NIL: Forall P (stepsof nil))
    (SINGLE: forall x, Forall P (stepsof [x]))
    (IND: forall a h l (HEAD: P (a, h)) (TAIL: Forall P (stepsof (h::l))), Forall P (stepsof (a::h::l))),
    forall l : list X, Forall P (stepsof l).
Proof.
  intros. induction l.
  - apply Forall_nil.
  - induction l.
    -- apply SINGLE.
    -- apply IND.
       Check Forall_ind.

(* Safety proof for our specific rewriter. *)
Theorem p32_rr_safe :
  forall program program' label policy entry is_abort (pol : addr -> option id -> Prop),
    safety p32_rr label policy program entry program' is_abort pol.
Proof.
  unfold safety, exec_prog in *; intros. 
  (* Would be nice to induct over `stepsof t'` so our inductive step has an
     obvious last step, but we should also keep the relationship between the steps of t'
     and t' starting at the entry obvious.

     Maybe we should have a custom induction principle with 2 base cases - 
     a base case for an empty trace, a base case for a singleton trace,
     and then an induction step that works on a trace with at least one element
     and proves the prop holds for traces with an additional (thus 2 total) specified
     head element. *)
  induction t'.

  - apply Forall_nil.
  - 
Abort.
