Require Import Picinae_core.
Require Export Picinae_timing.
Require Import Picinae_i386.
Require Export NArith.

Module i386Timing.
    Definition store := store.
    Definition stmt := stmt.

    Definition time_of_stmt (s : option (N * stmt)) : nat :=
        match s with None => 0 | Some (_, s') => match s' with
        | Move _ _ => 2
        | If _ _ _ => 6
        | Jmp _ => 9
        | _ => 0
        end end.

    Definition empty_store : store := fun _ => VaN 0 32.
End i386Timing.

Module i386T := MakeTimingContents(i386Timing).
Export i386T.
