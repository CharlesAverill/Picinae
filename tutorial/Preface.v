(** #<link rel="stylesheet" href="sf.css"># *)
(** * Preface *)

(* ################################################################# *)
(** * Welcome *)

(** This electronic book dives deeper into the practice of _reasoning
    about the properties of specific programs_.  This book introduces
    the reader to Picinae -- a platform for instruction level abstract
    execution -- and demonstrates its power to reason over trace
    properties of code.  After a brief demonstration of the user
    interface, it covers the techniques and theory used in making
    Picinae a sound and practical tool for handling proofs about any
    instruction set architecture.

    As with all of the books in the _Software Foundations_ series,
    this one is one hundred percent formalized and machine-checked:
    the entire text is literally a script for Coq.  It is intended to
    be read alongside (or inside) an interactive session with Coq.
    All the details in the text are fully formalized in Coq, and most
    of the exercises are designed to be worked using Coq.

    The book builds on the material from _Programming Language
    Foundations_
    (_Software Foundations_, volume 2). *)

(* ################################################################# *)
(** * Overview *)

(** The book develops two main conceptual threads:

    (1) the Picinae user interface for proving trace properties of
        code and extending its functionality to new architectures; and

    (2) the theory used to develop an interface that makes reasoning
    over many coding styles convenient (including recursion (TODO),
    self-modifying code (TODO), call-return pairs, tail-calls (TODO),
    and of course, loops.)

    The intended order of the chapters is:

      0. Preface.v (this file)
      1. Basics.v
      2. BasicLoops.v
      3. AbsAndPracs.v
      4. Foundation.v
      5. PicinaeAuto.v
  *)

(* ================================================================= *)
(** ** User Interface *)

(** TODO *)

(* ================================================================= *)
(** ** Theory *)

(** TODO *)

(* ================================================================= *)
(** ** Further Reading *)

(** This text is intended to be self contained, but readers looking
    for a deeper treatment of Picinae can refer to the technical
    report at [Permanent URL]. *)

(* ################################################################# *)
(** * Practicalities *)
(* ================================================================= *)
(** ** Recommended Citation Format *)

(** If you want to refer to this volume in your own writing, please
    do so as follows:

    @book            {Buzzetti:SF8,
    author       =   {Ilan Buzzetti and
		     Charles Averill and
		     Kevin W. Hamlen},
    editor       =   {Kevin W. Hamlen},
    title        =   "Picinae Foundations",
    series       =   "Software Foundations",
    volume       =   "8",
    year         =   "2025",
    publisher    =   "Electronic textbook",
    note         =   {Version 0.0a,
                      \URL{} },
    }
*)

(* ################################################################# *)
(** * Note for Instructors *)

(** If you plan to use these materials in your own course, you will
    undoubtedly find things you'd like to change, improve, or add.
    Your contributions are welcome!  Please see the [Preface]
    to _Logical Foundations_ for instructions. *)

(* ################################################################# *)
(** * Thanks *)

(** Development of the _Software Foundations_ series has been
    supported, in part, by the National Science Foundation under the
    CSGrad4US Grant <...> and Other Grants <...> *)
