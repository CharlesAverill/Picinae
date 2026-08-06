(** #<link rel="stylesheet" href="sf.css"># *)
(** * Picinae Auto *)

(* ################################################################# *)
(** * Introduction *)

(** This chapter focuses on the automation tools that make Picinae work smoothly.
    It covers:

      * The step tactic
      * How the MDL hypothesis is used
      * The destruct_inv tactic
      * The Picinae_typecheck tactic
      * The psimpl tactic

    Like the Foundation chapter, this is geared towards developers and maintainers
    who will need to understand the internals when adding features and when things
    break.  Users who are solely interested in program verification can safely skip
    this chapter.

    This material covers the files ...
    The typedness of expressions and statements comes from Picinae_statics and the rest from core. *)

(* ################################################################# *)
(** * Setting It Up *)

Require Export Picinae_core.
Require Import NArith.
Require Import Structures.Equalities.

Open Scope N.

(* ================================================================= *)
(** ** A Small Architecture Specification *)

