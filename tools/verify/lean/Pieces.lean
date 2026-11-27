import Algorithms

/-! # The Pipeline's folding of piece values, proved to give the specification's tree

`threads/src/pipeline.rs` hashes a long message in pieces, whole subtrees of `2^b` chunks (64 for a
Room), and folds their values with a lazy stack: `push_piece` first settles the merges it put
off (`merge_pieces`: the top two merged until one value is left for each 1-bit of the count
before), then pushes; `finish_pieces` settles once more and folds the stack onto the last piece's
value, top first. `fold_multi_cvs` does so for a message's parts, `drain_pieces` for its Rooms as
they finish (the first Room's piece gives its two halves, pushed as their parent).

This file models those four functions (`mergePieces`, `pushLazy`, `finishPieces`, `foldMulti`)
and proves the fold is the definition's tree: settled, the lazy stack is the full subtrees of the
pieces so far (`merge_lazy`, from `Algorithms.lean`'s eager `push_subtrees`); finished, it is the
tree over the pieces (`foldMulti_eq`); and that tree is the message's (`blake3_pieces`, by
`treeOf_row`). `u64::count_ones` is `popc` here. -/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Blake3.Algorithms

variable {α : Type} [Inhabited α] (merge : α → α → α)

/-- The number of 1-bits of `n` (`u64::count_ones`). -/
def popc (n : Nat) : Nat := if n = 0 then 0 else n % 2 + popc (n / 2)
termination_by n
decreasing_by omega

theorem popc_zero : popc 0 = 0 := by rw [popc]; simp

theorem popc_two_mul_add (m r : Nat) (hr : r < 2) : popc (2 * m + r) = r + popc m := by
  by_cases h : 2 * m + r = 0
  · have : m = 0 := by omega
    have : r = 0 := by omega
    subst_vars; rw [popc_zero]
  · rw [popc, if_neg h]
    congr 1
    · omega
    · congr 1; omega

/-- Taking the top bit off takes one 1-bit off. -/
theorem popc_top (n : Nat) (hn : 0 < n) : popc n = popc (n - 2 ^ n.log2) + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h1 : n = 1
    · subst h1; rw [show (1 : Nat).log2 = 0 by decide]; simp [popc]
    have h2 : 2 ≤ n := by omega
    have lo := Nat.log2_self_le (n := n / 2) (by omega)
    have hi := Nat.lt_log2_self (n := n / 2)
    rw [Nat.pow_succ] at hi
    have hlog : n.log2 = (n / 2).log2 + 1 := by
      have a : (n / 2).log2 + 1 ≤ n.log2 := (Nat.le_log2 (by omega)).2 (by rw [Nat.pow_succ]; omega)
      have b : n.log2 < (n / 2).log2 + 2 := (Nat.log2_lt (by omega)).2 (by rw [Nat.pow_succ, Nat.pow_succ]; omega)
      omega
    have ih2 := ih (n / 2) (by omega) (by omega)
    rw [hlog, Nat.pow_succ,
      show n - 2 ^ (n / 2).log2 * 2 = 2 * (n / 2 - 2 ^ (n / 2).log2) + n % 2 by omega,
      popc_two_mul_add _ _ (by omega)]
    conv => lhs; rw [show n = 2 * (n / 2) + n % 2 by omega]
    rw [popc_two_mul_add _ _ (by omega), ih2]
    omega

/-- A prefix has one full subtree for each 1-bit of its length. -/
theorem length_subtrees : ∀ (ys : List α), (subtrees merge ys).length = popc ys.length := by
  suffices ∀ n (ys : List α), ys.length = n → (subtrees merge ys).length = popc ys.length from fun ys => this _ ys rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ys hn
    by_cases hy : ys = []
    · subst hy; simp [subtrees_nil, popc_zero]
    have h0 : 0 < ys.length := List.length_pos_iff.2 hy
    have lo := Nat.log2_self_le (n := ys.length) (by omega)
    have hp := Nat.two_pow_pos ys.length.log2
    rw [subtrees_cons _ ys hy, List.length_cons, ih _ (by simp; omega) _ rfl, List.length_drop, popc_top _ h0]

/-! The stacks here are top first: the head is the top (the code's `stack[used - 1]`). -/

/-- `n` merges of the top two (`merge_pieces`'s loop): the one below, merged with the top. -/
def settle : Nat → List α → List α
  | 0, l => l
  | n + 1, b :: a :: rest => settle n (merge a b :: rest)
  | _ + 1, l => l

theorem length_settle : ∀ n (l : List α), n < l.length → (settle merge n l).length = l.length - n := by
  intro n
  induction n with
  | zero => intro l _; rfl
  | succ n ih =>
    intro l hl
    match l, hl with
    | b :: a :: rest, hl => rw [settle, ih _ (by simp at hl ⊢; omega)]; simp

/-- `Algorithms.push` merges the top two while its count is even: some number of top merges. -/
theorem push_settle : ∀ (st : List α) (x : α) (c : Nat), ∃ n, n ≤ st.length ∧ push merge st x c = settle merge n (x :: st) := by
  intro st
  induction st with
  | nil => intro x c; exact ⟨0, by simp, by rw [push]; rfl⟩
  | cons s rest ih =>
    intro x c
    by_cases h : c % 2 = 0 ∧ 0 < c
    · obtain ⟨n, hn, he⟩ := ih (merge s x) (c / 2)
      refine ⟨n + 1, by simp; omega, ?_⟩
      rw [push_even merge s rest x c h.1 h.2, he, settle]
    · refine ⟨0, by simp, ?_⟩
      rw [push]; split
      · omega
      · rfl

/-- `merge_pieces`: settle the lazy merges of `count` pieces, down to one value for each 1-bit of
`count`. -/
def mergePieces (st : List α) (count : Nat) : List α := settle merge (st.length - popc count) st

/-- `push_piece`: settle, then push the next whole piece's value. -/
def pushLazy (st : List α) (preceding : Nat) (piece : α) : List α := piece :: mergePieces merge st preceding

/-- `finish_pieces`: settle, then fold the stack onto the last piece, the top first (`finish`). -/
def finishPieces (st : List α) (count : Nat) (last : α) : α := finish merge (mergePieces merge st count) last

/-- The stack after pushing `wholes` in turn, each with the count before it. -/
def lazy (wholes : List α) : List α :=
  (wholes.foldl (fun (p : List α × Nat) v => (pushLazy merge p.1 p.2 v, p.2 + 1)) ([], 0)).1

/-- `fold_multi_cvs`: every whole piece pushed, then finished with the last. -/
def foldMulti (wholes : List α) (last : α) : α := finishPieces merge (lazy merge wholes) wholes.length last

theorem lazy_append (ys : List α) (u : α) : lazy merge (ys ++ [u]) = pushLazy merge (lazy merge ys) ys.length u := by
  have : ∀ (zs : List α), (zs.foldl (fun (p : List α × Nat) v => (pushLazy merge p.1 p.2 v, p.2 + 1)) ([], 0)).2 = zs.length := by
    intro zs
    suffices ∀ (zs : List α) (q : List α × Nat), (zs.foldl (fun (p : List α × Nat) v => (pushLazy merge p.1 p.2 v, p.2 + 1)) q).2 = q.2 + zs.length by
      simpa using this zs ([], 0)
    intro zs
    induction zs with
    | nil => intro q; simp
    | cons z zs ih => intro q; rw [List.foldl_cons, ih]; simp; omega
  simp only [lazy, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [this]

/-- **The lazy stack settled is the prefix's full subtrees.** -/
theorem merge_lazy : ∀ (ys : List α), mergePieces merge (lazy merge ys) ys.length = (subtrees merge ys).reverse := by
  suffices ∀ n (ys : List α), ys.length = n → mergePieces merge (lazy merge ys) ys.length = (subtrees merge ys).reverse from
    fun ys => this _ ys rfl
  intro n
  induction n with
  | zero => intro ys h; rw [List.length_eq_zero_iff.1 h]; simp [mergePieces, lazy, popc_zero, settle, subtrees_nil]
  | succ n ih =>
    intro ys hn
    have hne : ys ≠ [] := by intro h; subst h; simp at hn
    obtain ⟨zs, u, rfl⟩ : ∃ zs u, ys = zs ++ [u] := ⟨ys.dropLast, ys.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    have hz : zs.length = n := by simp at hn; omega
    rw [lazy_append, pushLazy, ih zs hz]
    -- The eager push does some top merges; the lengths say how many.
    have hpush := push_subtrees merge zs.length 0 zs [u] (by simp) (by simp)
    rw [treeOf_single] at hpush
    obtain ⟨m, hm, he⟩ := push_settle merge (subtrees merge zs).reverse u (zs.length + 1)
    rw [hpush] at he
    rw [List.length_reverse, length_subtrees] at hm
    have hlen := congrArg List.length he
    rw [List.length_reverse, length_settle merge m _ (by simp [length_subtrees]; omega), length_subtrees, List.length_cons,
      List.length_reverse, length_subtrees] at hlen
    rw [mergePieces, List.length_cons, List.length_reverse, length_subtrees, List.length_append, List.length_singleton]
    rw [show popc zs.length + 1 - popc (zs.length + 1) = m by simp at hlen; omega, ← he]

/-- **`fold_multi_cvs` is the tree over the pieces.** Whole pieces pushed lazily, settled, then
folded onto the last: the tree's root over the pieces' values. -/
theorem foldMulti_eq (wholes : List α) (last : α) : foldMulti merge wholes last = treeOf merge (wholes ++ [last]) := by
  rw [foldMulti, finishPieces, merge_lazy, finish, List.foldl_reverse,
    treeOf_append merge 0 wholes [last] (by simp) (by simp) (by simp), treeOf_single]

/-! ## For BLAKE3's messages -/

/-- **A message hashed in pieces** (`fold_multi_cvs`, `submit_multi_slice`; a batch's are hashed
whole): its chunks cut into pieces of `2^b` chunks, each piece's tree computed apart, the whole
ones pushed lazily and the last folded on: the definition's output. -/
theorem blake3_pieces (key : Vector Word 8) (mode : Word) (input : ByteArray) (outLen : Nat) (b : Nat)
    (h : 2 ^ b < (chunkNodes key mode input).size) :
    let vs := row (parent key mode) (2 ^ b) (chunkNodes key mode input).toList
    blake3 key mode input outLen = output (foldMulti (parent key mode) vs.dropLast vs.getLast!) outLen := by
  intro vs
  have hne : (chunkNodes key mode input).toList ≠ [] := by
    have hp := Nat.two_pow_pos b
    intro e; have := congrArg List.length e; rw [Array.length_toList, List.length_nil] at this; omega
  have hv : vs ≠ [] := by
    have hp := Nat.two_pow_pos b
    intro e; have := congrArg List.length e
    simp only [vs, row, List.length_map, length_groups _ (Nat.two_pow_pos b), Array.length_toList, List.length_nil] at this
    have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos b)).2 (show 1 * 2 ^ b ≤ (chunkNodes key mode input).size + 2 ^ b - 1 by omega)
    omega
  have split : vs.dropLast ++ [vs.getLast!] = vs := by
    cases hc : vs with
    | nil => exact absurd hc hv
    | cons a l => rw [List.getLast!, List.dropLast_concat_getLast]
  rw [foldMulti_eq, split, blake3_tree, treeOf_row (parent key mode) b _ hne]

/-- **A message fed through Rooms** (`drain_pieces`): a room is 64 chunks, and the first room's
piece gives its two halves; pushed as one value, their parent, that is the first room's tree. -/
theorem room_first (key : Vector Word 8) (mode : Word) (room : List Node) (h : room.length = 2 ^ 6) :
    treeOf (parent key mode) room =
      parent key mode (treeOf (parent key mode) (room.take (2 ^ 5))) (treeOf (parent key mode) (room.drop (2 ^ 5))) :=
  treeOf_full (parent key mode) 5 room h

end Blake3.Algorithms

#print axioms Blake3.Algorithms.merge_lazy
#print axioms Blake3.Algorithms.foldMulti_eq
#print axioms Blake3.Algorithms.blake3_pieces
#print axioms Blake3.Algorithms.room_first
