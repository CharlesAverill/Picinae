Require Export Picinae_pilbox32.
Require Export Picinae_pilbox32_interpreter.

Require Import NArith.
Require Import ZArith.
Require Import List.
Open Scope N.
Import ListNotations.

(* id - label for the instruction
   oid - label to check for with dynamic jumps
   n - instruction encoding
   a - instruction address *)
Inductive inst_data := Data (id: option N) (oid: N) (n: N) (a: N).

(* add a label check to a jmpr instruction where the destination is rs1 *)
Definition rewrite_jmpr (data: inst_data) (rs1: N) : list N :=
  match data with Data _ oid _ _ =>
    map assemble_insn [
      PIL_st 0 6 0;       (*   st r0  sp  0 *) (* save r0 and r1 to the stack *)
      PIL_st 1 6 4;       (*   st r1  sp  4 *)
      PIL_ld 0 rs1 4;     (*   ld r0  rs1 4 *) (* load the real label and expected label *)
      PIL_li 1 oid;       (*   li r1  oid   *)
      PIL_bne 0 1 0;      (*  bne r0  r1  0 *) (* infinite loop if no match *)
      PIL_ld 0 6 0;       (*   ld r0  sp  0 *) (* restore r0 and r1 *)
      PIL_ld 1 6 4;       (*   ld r1  sp  4 *)
      PIL_jmpr rs1        (* jmpr rs1       *) (* jump *)
    ] end.

(* add a label at the start of a list of instructions *)
Definition add_id (id: option N) (rw_n: list N) : list N :=
  match id with
  | Some id => assemble_insn (PIL_beq 0 0 8)::id::rw_n
  | None => rw_n
  end.

(* rewrite a single instruction *)
Definition rewrite_inst (data: inst_data) : list N :=
  match data with Data id _ n _ =>
    let inst := p32_decode n in
    let new_n := match inst with
                 | PIL_jmpr rs1 => rewrite_jmpr data rs1
                 | _ => n::nil
                 end in
    add_id id new_n
  end.

(* get a list of the new starting addresses for each old instruction *)
Fixpoint new_addrs (rw_ns: list (list N)) (a: N) : list N :=
  match rw_ns with
  | n::ns => a::new_addrs ns (a + 4 * N.of_nat (length n))
  | _ => a::nil
  end.

(* get a list of the new destination addresses of jump/branch instructions *)
Fixpoint new_targets (data: list inst_data) (rw_as: list N) (base: N) : list N :=
  match data with
  | Data _ _ n a::t => nth match p32_decode n with
                           | PIL_beq rs1 rs2 si => (Z.to_nat ((Z.of_N a) + si) - N.to_nat base) / 4
                           | PIL_blt rs1 rs2 si => (Z.to_nat ((Z.of_N a) + si) - N.to_nat base) / 4
                           | PIL_bne rs1 rs2 si => (Z.to_nat ((Z.of_N a) + si) - N.to_nat base) / 4
                           | PIL_bl si => (Z.to_nat ((Z.of_N a) + si) - N.to_nat base) / 4
                           | PIL_jl i => (N.to_nat i - N.to_nat base) / 4
                           | PIL_jmp i => (N.to_nat i - N.to_nat base) / 4
                           | _ => 0
                       end rw_as 0::new_targets t rw_as base
  | _ => nil
  end.

(* change the destination of a direct jump/branch at addr a *)
Definition replace_target (n: N) (a: N) (new_dest: N) : N :=
    assemble_insn match p32_decode n with
    | PIL_beq rs1 rs2 si => PIL_beq rs1 rs2 (Z.of_N new_dest - Z.of_N a)
    | PIL_blt rs1 rs2 si => PIL_blt rs1 rs2 (Z.of_N new_dest - Z.of_N a)
    | PIL_bne rs1 rs2 si => PIL_blt rs1 rs2 (Z.of_N new_dest - Z.of_N a)
    | PIL_bl si => PIL_bl (Z.of_N new_dest - Z.of_N a)
    | PIL_jl i => PIL_jl new_dest
    | PIL_jmp i => PIL_jmp new_dest
    | a => a
  end.

(* replace the last element of a list *)
Fixpoint replace_last {T: Type} (ts: list T) (last: T) : list T :=
  match ts with
  | a::nil => last::nil
  | a::t => a::replace_last t last
  | nil => nil
  end.

(* fix the destinations of the jump/branch instructions of a rewritten program *)
Fixpoint fix_targets (ns: list N) (rw_as: list N) (rw_ts: list N) (rw_ns: list (list N)) : list (list N) :=
  match ns, rw_as, rw_ts, rw_ns with
  | n::ns, rw_a::rw_as, rw_t::rw_ts, rw_n::rw_ns =>
      let new_last := (replace_target n (rw_a-4) rw_t) in
      replace_last rw_n new_last::fix_targets ns rw_as rw_ts rw_ns
  | _, _, _, _ => nil
  end.

(* turn a list of inst encodings to a list of inst_data *)
Fixpoint to_data (label: N -> option N) (Pol: N -> N) (ns: list N) (a: N) : list inst_data :=
  match ns with
  | n::ns => (Data (label a) (Pol a) n a)::(to_data label Pol ns (a+4))
  | nil => nil
  end.

(* rewrite a program starting at address a *)
Definition rewrite (label: N -> option N) (Pol: N -> N) (ns: list N) (a: N) : list (list N) :=
  let data := to_data label Pol ns a in
  let rw_ns := map rewrite_inst data in
  let rw_as := new_addrs rw_ns a in
  let rw_ts := new_targets data rw_as a in
  fix_targets ns (tail rw_as) rw_ts rw_ns.

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
  | 0 => 111
  | 12 => 222
  | _ => 333
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
