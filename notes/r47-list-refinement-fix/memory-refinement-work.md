# Remaining memory-refinement proof work

The original 30 statements are retained. Four are not exported:
`ring_insert_memory`, `ring_remove_memory`, `ring_insert_refines`,
`ring_remove_refines`. Their original unverified proof attempts remain verbatim
in the prerequisite's `initial-attempt.v.txt`; they are not checked proofs.

The following is a proposed proof decomposition, not a certificate.

1. Use the finite `ring_segment` helpers to split a represented chain at
   `left++right` or `left++P::right`. A segment keeps its two exterior link
   values explicit. This avoids induction that incorrectly treats the prefix
   as a complete ring with a new header/count.
2. Prove `NoDup (left++right)` implies disjoint prefix/suffix membership.
   Combine `ring_last_member`, a nonempty-last membership lemma, and
   `ring_node_not_sentinel` to exclude the right cursor from the prefix and
   the predecessor from the suffix. Only real nodes must be distinct from
   the embedded sentinel; the two neighbor pointers may alias each other.
3. For insertion, derive unchanged word reads outside the six actual write
   addresses using `ring_insert_word_frame`. For an existing real node Q,
   use `ring_object_fields_separate` and
   `ring_node_link_field_separate` to show:

   - value, owner, container unchanged;
   - next becomes P exactly if Q=predecessor, otherwise unchanged;
   - previous becomes P exactly if Q=index, otherwise unchanged.

   The new P's five fields follow from `insert_end_memory_fields` plus the
   original fresh value/owner facts. The node relation is an implication
   derived from exact store expressions, never a postcondition premise.
4. Apply `ring_segment_change_back` to the prefix and
   `ring_segment_change_front` to the suffix. Compose around the new node
   with `ring_segment_app`, then recover `ring_chain_segment`.
5. Header count/index follow from the existing memory-fields lemma. Sentinel
   value is outside the footprint. For the first link, split on left=[]:
   the empty-prefix predecessor is sentinel, so its next write is header+12;
   otherwise that header word is framed. For the back link, split on right=[]:
   the empty-suffix cursor is sentinel, so its previous write is header+16;
   otherwise frame it. For nonempty suffixes, ring_last ignores its initial
   default, which proves the new and old back values coincide. Use the exact
   mathematical count bound to eliminate modular increment. Preserve the
   ghost maps V and O unchanged.
6. For removal, derive the analogous kept-node relation from
   `list_remove_mem_effects` and its four-byte outside-frame conclusion:
   next becomes successor only at predecessor, previous becomes predecessor
   only at successor, other fields unchanged. Removed-item fields and
   cleared container are already supplied by the checked local contract.
   Split out the selected node, patch both segments, and concatenate them.
   Header front/back cases mirror insertion. Count decreases as a natural
   cardinality using `ring_count_remove`; `ring_remove_geometry` and
   `ring_remove_cursor_valid` cover output layout and both cursor branches.
7. Only after both memory theorems check, restore the original composed IL
   proofs, fixing elaboration/projection issues if necessary without changing
   their statements. Query all four original main theorems with the supplied
   assumptions harness. Main IL bridges should inherit only the documented
   baseline dependent functional extensionality; pure memory facts should
   remain closed.

Keep all arithmetic proof contexts free of memory terms. The broad initial
`firstorder` tactic in fresh geometry hit 3M; an explicit finite membership
proof passed that point at 459448 KiB peak RSS (approximately
449 MiB), so that isolated failure is not a resource impossibility result.
