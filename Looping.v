Inductive end_t: Prop := END.
Inductive mark_t: Prop := MARK.
Inductive start_t: Prop := START.

Ltac intros_start :=
  (* Intros until we reach the START, then introduce that too *)
  repeat progress lazymatch goal with
                  | [|- ?orig_goal] =>
                      lazymatch orig_goal with
                      | start_t -> _ => idtac
                      | _ => intro
                      end
                  end; intro.

(* Revert until we reverted everything or reached the START. Then revert
 * the block as well if we have it. *)
Ltac to_start :=
  repeat progress lazymatch goal with
                  | [H: _ |- _] =>
                      lazymatch type of H with
                      | start_t => idtac
                      | _ => revert H
                      end
                  end;
  try lazymatch goal with
      | [S: start_t |- _] => revert S
      end;

  (* We might have reverted everything, so introduce up to start and revert
   * again *)
  intros_start;
  lazymatch goal with
  | [S: start_t |- _] => revert S
  end.

(* Initializes/enters a loop *)
Ltac init :=
  let Start := fresh "START" in generalize START; intro Start.

Ltac init_end :=
  let End := fresh "END" in generalize END; intro End.

(* Revert/introduce premises to what it was before we entered this loop and exit
 * the loop by removing the block thing *)
Ltac final := to_start; intro;
  (* Remove all block premises.  *)
  repeat lazymatch goal with
         | [E: end_t |- _] => clear E
         | [S: start_t |- _] => clear S
         | [M: mark_t |- _] => clear M
         end.

(* Next premise. Reverts the bottom premise, or errors out reached the end. This
 * is a primitive next tactic. If you are manipulating the context in any way
 * during execution, you may want to use bnext instead *)
Ltac next :=
  lazymatch goal with
  | [H: _ |- _] =>
      lazymatch type of H with
      | end_t => fail "Reached end"
      | _ => revert H
      end
  end.

Ltac get_or_else tac or_else :=
  lazymatch goal with
  | [H: _ |- _] =>
      lazymatch type of H with
      | end_t => or_else ()
      | _ => tac H
      end
  | [|- _] => or_else ()
  end.

Ltac get tac :=
  get_or_else tac ltac:(fun _ => idtac).

Ltac bookmark :=
  let Mark := fresh "MARK" in generalize MARK; intro Mark; revert Mark.

(* Searches for the first bookmark and removes it *)
Ltac unbookmark := to_start;
  (* loop next until we reach bookmark *)
  repeat progress (get ltac:(fun H =>
    lazymatch type of H with
    | mark_t => fail "Bookmarked"
    | _ => next
    end));
  (* Remove bookmark *)
  lazymatch goal with
  | [M: mark_t |- _] => clear M
  | _ => fail "No bookmarks found"
  end.

(* High level initialization based on bookmarks *)
Ltac binit := to_start; bookmark.

(* High level next implementation: take the first bookmark, and then mark the
 * premise above it. This allows us to remember where we are in the loop
 * iteration *)
Ltac bnext := unbookmark;
  get ltac:(fun H => revert H; bookmark).

Ltac to_bookmark := unbookmark; bookmark.
