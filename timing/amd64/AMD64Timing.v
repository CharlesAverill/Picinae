Require Export Picinae_amd64.
Export X64Notations.
Require Export TimingAutomation.
Require Export NArith.
Require Import ZArith.
Require Export Lia.
Require Import List.
Import ListNotations.

Module Type ProgramInformation.
    Parameter entry_addr : addr.
    Parameter exits : trace -> bool.
    (* Binary representation of the program to be decoded *)
    Parameter lifted_prog : program.
    Parameter time_of_addr : store -> addr -> N.
End ProgramInformation.

Module AMD64Timing (prog : ProgramInformation) <: TimingModule IL_amd64.
    Export prog.

    Definition time_inf : N := 2^64.

    Definition time_of_addr := prog.time_of_addr.
End AMD64Timing.

(* Instantiate the Timing Automation module with RISC-V values *)
(* Provide CPUTimingBehavior and ProgramInformation *)
Module AMD64TimingAutomation := 
    TimingAutomation IL_amd64 Theory_amd64 Statics_amd64 FInterp_amd64
    PSimpl_amd64_v1_1.
