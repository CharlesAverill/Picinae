Require Import Picinae_core.
Require Export Picinae_timing.
Require Import Picinae_i386.
Require Export NArith.

Module i386Timing.
    Definition store := store.
    Definition stmt := stmt.
    Definition empty_store : store := fun _ => VaN 0 32.
End i386Timing.
