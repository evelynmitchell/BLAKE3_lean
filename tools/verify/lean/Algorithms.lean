import Blake3
import Theorems

/-! # The algorithms the library computes the tree with, proved to compute `Blake3.lean`'s

`Blake3.lean` defines BLAKE3's tree by recursion: the left subtree of `n ≥ 2` chunks holds
`leftCount n` of them. The library never evaluates it so: its `Hasher` pushes chunks on a stack of
subtrees and merges as it goes (`src/hasher.rs`), and the pool and the grouped calls cut the input
into subtrees, hash each on its own, and merge their values (`threads/src/lanes.rs`,
`src/each.rs`). This file writes those algorithms down and proves each gives the definition's
result, for every input.

The tree theorems are about the tree's shape, so they hold for any function merging two values
(`merge`); `tree` is `treeOf` with BLAKE3's parent node as the merge (`tree_eq`), and `blake3_*`
state them for BLAKE3's own chunks. What remains outside: that the Rust implements these
algorithms. The tests compare the Rust with the definition (`test_vectors/lean_vectors.json`); the
models here are what those tests' passing would be about. -/

set_option linter.unusedSectionVars false

namespace Blake3.Algorithms

/-! ## The tree over a list -/

variable {α : Type} [Inhabited α] (merge : α → α → α)

/-- `tree`'s recursion over a list: one element is its own tree; more split at `leftCount`, the
largest power of 2 below their count. (The empty list, which `tree` never has, gives `default`.) -/
def treeOf (xs : List α) : α :=
  if _ : xs.length ≤ 1 then xs.headD default
  else merge (treeOf (xs.take (leftCount xs.length))) (treeOf (xs.drop (leftCount xs.length)))
termination_by xs.length
decreasing_by
  · simp only [List.length_take]; have := leftCount_lt xs.length (by omega); omega
  · simp only [List.length_drop]; have := leftCount_pos xs.length; omega

theorem treeOf_single (x : α) : treeOf merge [x] = x := by
  rw [treeOf]; simp

theorem treeOf_split (xs : List α) (h : 2 ≤ xs.length) :
    treeOf merge xs = merge (treeOf merge (xs.take (leftCount xs.length))) (treeOf merge (xs.drop (leftCount xs.length))) := by
  rw [treeOf]; simp only [show ¬ xs.length ≤ 1 by omega, dite_false]

/-- A parent of two nodes, as `tree` makes one. -/
def parent (key : Vector Word 8) (mode : Word) (l r : Node) : Node := parentNode key mode l.cv r.cv

/-- `tree`'s recursion over an array's indices is `treeOf` over the elements between them. -/
theorem go_eq (key : Vector Word 8) (mode : Word) (chunks : Array Node) :
    ∀ n start, 0 < n → start + n ≤ chunks.size →
      tree.go key mode chunks start n = treeOf (parent key mode) ((chunks.toList.drop start).take n) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro start hn hs
    rw [tree.go]
    by_cases h1 : n ≤ 1
    · have : n = 1 := by omega
      subst this
      have hlt : start < chunks.toList.length := by simp; omega
      rw [List.drop_eq_getElem_cons hlt]
      simp only [treeOf_single, Array.getElem_toList, List.take_succ_cons, List.take_zero, dite_true, Nat.le_refl]
      exact getElem!_pos chunks start (by omega)
    · rw [dite_eq_right_of_eq_false (eq_false h1)]
      simp only []
      have hk := leftCount_lt n (by omega)
      have hp := leftCount_pos n
      have hlen : ((chunks.toList.drop start).take n).length = n := by simp; omega
      rw [treeOf_split _ ((chunks.toList.drop start).take n) (by omega), hlen,
        ih _ hk start hp (by omega), ih _ (by omega) (start + leftCount n) (by omega) (by omega)]
      simp only [parent, List.take_take, List.drop_take, List.drop_drop, Nat.min_eq_left (Nat.le_of_lt hk)]

/-- `Blake3.lean`'s `tree` is `treeOf` with BLAKE3's parent node as the merge. -/
theorem tree_eq (key : Vector Word 8) (mode : Word) (chunks : Array Node) (h : 0 < chunks.size) :
    tree key mode chunks = treeOf (parent key mode) chunks.toList := by
  rw [tree, go_eq key mode chunks _ 0 h (by omega)]
  simp [List.take_of_length_le]

/-! ## Powers of two -/

/-- Adding less than `2^k` to a positive multiple of `2^k` keeps its top bit. -/
theorem log2_add (a c k : Nat) (ha : 0 < a) (hk : 2 ^ k ∣ a) (hc : c < 2 ^ k) :
    (a + c).log2 = a.log2 := by
  have lo := Nat.log2_self_le (n := a) (by omega)
  have hi := Nat.lt_log2_self (n := a)
  rw [Nat.pow_succ] at hi
  have hka : k ≤ a.log2 := (Nat.le_log2 (by omega)).2 (Nat.le_of_dvd ha hk)
  -- 2^k divides 2 * 2^log2 a - a, which is positive, so it is at least 2^k.
  have hP : 2 ^ k ∣ 2 ^ a.log2 * 2 := Nat.dvd_trans (Nat.pow_dvd_pow 2 hka) (Nat.dvd_mul_right _ 2)
  have hd := Nat.le_of_dvd (by omega) (Nat.dvd_sub hP hk)
  have h1 : (a + c).log2 < a.log2 + 1 := (Nat.log2_lt (by omega)).2 (by rw [Nat.pow_succ]; omega)
  have h2 : a.log2 ≤ (a + c).log2 := (Nat.le_log2 (by omega)).2 (by omega)
  omega

/-! ## The full subtrees of a prefix -/

/-- The full subtrees `xs` makes, largest first: cut at the top bit of its length, then the rest
likewise (one subtree for each 1-bit of the length). -/
def subtrees (xs : List α) : List α :=
  if _ : xs = [] then []
  else treeOf merge (xs.take (2 ^ xs.length.log2)) :: subtrees (xs.drop (2 ^ xs.length.log2))
termination_by xs.length
decreasing_by
  have : 0 < xs.length := List.length_pos_iff.2 ‹_›
  have := Nat.two_pow_pos xs.length.log2
  simp only [List.length_drop]; omega

theorem subtrees_nil : subtrees merge ([] : List α) = [] := by
  rw [subtrees]; simp

theorem subtrees_cons (xs : List α) (h : xs ≠ []) :
    subtrees merge xs = treeOf merge (xs.take (2 ^ xs.length.log2)) :: subtrees merge (xs.drop (2 ^ xs.length.log2)) := by
  rw [subtrees]; simp [h]

/-- `2^k` divides the part past a positive multiple's top bit. -/
theorem dvd_sub_top (a k : Nat) (ha : 0 < a) (hk : 2 ^ k ∣ a) : 2 ^ k ∣ a - 2 ^ a.log2 :=
  Nat.dvd_sub hk (Nat.pow_dvd_pow 2 ((Nat.le_log2 (by omega)).2 (Nat.le_of_dvd ha hk)))

/-- The root over a prefix whose length `2^k` divides and a last part of `1` to `2^k` elements: the
prefix's full subtrees, each the left child of the next node down, the last part's tree at the
bottom. -/
theorem treeOf_append (k : Nat) : ∀ (ys zs : List α), 2 ^ k ∣ ys.length → 0 < zs.length → zs.length ≤ 2 ^ k →
    treeOf merge (ys ++ zs) = (subtrees merge ys).foldr merge (treeOf merge zs) := by
  suffices ∀ n (ys zs : List α), ys.length = n → 2 ^ k ∣ ys.length → 0 < zs.length → zs.length ≤ 2 ^ k →
      treeOf merge (ys ++ zs) = (subtrees merge ys).foldr merge (treeOf merge zs) from
    fun ys zs => this _ ys zs rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ys zs hn hk hz0 hzk
    by_cases hy : ys = []
    · subst hy; simp [subtrees_nil]
    have hy0 : 0 < ys.length := List.length_pos_iff.2 hy
    have lo := Nat.log2_self_le (n := ys.length) (by omega)
    have hpos := Nat.two_pow_pos ys.length.log2
    -- The split of the whole is at the prefix's top bit.
    have hsplit : leftCount (ys ++ zs).length = 2 ^ ys.length.log2 := by
      rw [leftCount, List.length_append,
        show ys.length + zs.length - 1 = ys.length + (zs.length - 1) by omega,
        log2_add ys.length (zs.length - 1) k hy0 hk (by omega)]
    rw [treeOf_split _ _ (by simp; omega), hsplit, subtrees_cons _ ys hy, List.foldr_cons,
      List.take_append_of_le_length lo, List.drop_append_of_le_length lo]
    rw [ih (ys.length - 2 ^ ys.length.log2) (by omega) (ys.drop (2 ^ ys.length.log2)) zs (by simp)
      (by simpa using dvd_sub_top ys.length k hy0 hk) hz0 hzk]

/-- A list of `2^k` elements is one full subtree. -/
theorem subtrees_pow (k : Nat) (b : List α) (hb : b.length = 2 ^ k) : subtrees merge b = [treeOf merge b] := by
  have : b ≠ [] := by intro h; subst h; simp at hb; have := Nat.two_pow_pos k; omega
  rw [subtrees_cons _ b this, hb, Nat.log2_two_pow, ← hb, List.take_length, List.drop_length, subtrees_nil]

/-- A full subtree of `2^(k+1)` elements is the parent of its halves. -/
theorem treeOf_full (k : Nat) (b : List α) (hb : b.length = 2 ^ (k + 1)) :
    treeOf merge b = merge (treeOf merge (b.take (2 ^ k))) (treeOf merge (b.drop (2 ^ k))) := by
  rw [treeOf_split _ b (by rw [hb, Nat.pow_succ]; have := Nat.two_pow_pos k; omega), hb, full_splits_in_half]

/-- Two full subtrees of `2^k` elements each are the halves of one. -/
theorem treeOf_pair (k : Nat) (a b : List α) (ha : a.length = 2 ^ k) (hb : b.length = 2 ^ k) :
    treeOf merge (a ++ b) = merge (treeOf merge a) (treeOf merge b) := by
  rw [treeOf_full _ k _ (by rw [List.length_append, ha, hb, Nat.pow_succ]; omega), List.take_left' ha, List.drop_left' ha]

/-- Past a prefix whose length `2^k` divides, fewer than `2^k` more elements add their own subtrees
below the prefix's. -/
theorem subtrees_append (k : Nat) : ∀ (ys zs : List α), 2 ^ k ∣ ys.length → zs.length < 2 ^ k →
    subtrees merge (ys ++ zs) = subtrees merge ys ++ subtrees merge zs := by
  suffices ∀ n (ys zs : List α), ys.length = n → 2 ^ k ∣ ys.length → zs.length < 2 ^ k →
      subtrees merge (ys ++ zs) = subtrees merge ys ++ subtrees merge zs from
    fun ys zs => this _ ys zs rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ys zs hn hk hz
    by_cases hy : ys = []
    · subst hy; simp [subtrees_nil]
    have hy0 : 0 < ys.length := List.length_pos_iff.2 hy
    have lo := Nat.log2_self_le (n := ys.length) (by omega)
    have hpos := Nat.two_pow_pos ys.length.log2
    have htop : (ys ++ zs).length.log2 = ys.length.log2 := by
      rw [List.length_append, log2_add ys.length zs.length k hy0 hk hz]
    rw [subtrees_cons _ (ys ++ zs) (by simp [hy]), subtrees_cons _ ys hy, htop,
      List.take_append_of_le_length lo, List.drop_append_of_le_length lo, List.cons_append,
      ih (ys.length - 2 ^ ys.length.log2) (by omega) (ys.drop (2 ^ ys.length.log2)) zs (by simp)
        (by simpa using dvd_sub_top ys.length k hy0 hk) hz]

/-! ## The stack -/

/-- Push full subtree `x` onto a stack (top first), `count` the number of subtrees of its size so
far, itself included: while that count is even, the top is its left sibling, so merge the two and
go up a level. -/
def push : List α → α → Nat → List α
  | s :: rest, x, count =>
    if h : count % 2 = 0 ∧ 0 < count then push rest (merge s x) (count / 2) else x :: s :: rest
  | [], x, _ => [x]
termination_by _ _ count => count
decreasing_by omega

theorem push_odd (st : List α) (x : α) (count : Nat) (h : count % 2 = 1) : push merge st x count = x :: st := by
  cases st with
  | nil => rw [push]
  | cons s rest => rw [push]; split <;> first | rfl | omega

theorem push_even (s : α) (rest : List α) (x : α) (count : Nat) (h : count % 2 = 0) (h0 : 0 < count) :
    push merge (s :: rest) x count = push merge rest (merge s x) (count / 2) := by
  rw [push]; split
  · rfl
  · omega

/-- Pushing a full subtree of `2^k` elements, after a prefix of `q` subtrees of its size, leaves the
full subtrees of the prefix and it. -/
theorem push_subtrees : ∀ q k (ys b : List α), ys.length = q * 2 ^ k → b.length = 2 ^ k →
    push merge (subtrees merge ys).reverse (treeOf merge b) (q + 1) = (subtrees merge (ys ++ b)).reverse := by
  intro q
  induction q using Nat.strongRecOn with
  | ind q ih =>
    intro k ys b hy hb
    have hpos := Nat.two_pow_pos k
    rcases Nat.mod_two_eq_zero_or_one q with he | ho
    · -- No carry: the new subtree goes on top.
      obtain ⟨r, rfl⟩ : ∃ r, q = 2 * r := ⟨q / 2, by omega⟩
      rw [push_odd _ _ _ _ (by omega),
        subtrees_append _ (k + 1) ys b ⟨r, by rw [hy, Nat.pow_succ]; ac_rfl⟩ (by rw [hb, Nat.pow_succ]; omega),
        subtrees_pow _ k b hb, List.reverse_append]
      rfl
    · -- A carry: the top is the left sibling; their parent is pushed a level up.
      obtain ⟨r, rfl⟩ : ∃ r, q = 2 * r + 1 := ⟨q / 2, by omega⟩
      have hlen : 2 * r * 2 ^ k ≤ ys.length := by rw [hy]; exact Nat.mul_le_mul_right _ (by omega)
      have hys := List.take_append_drop (2 * r * 2 ^ k) ys
      have hlast : (ys.drop (2 * r * 2 ^ k)).length = 2 ^ k := by
        simp only [List.length_drop, hy, Nat.add_mul, Nat.one_mul]; omega
      have hfirst : (ys.take (2 * r * 2 ^ k)).length = r * 2 ^ (k + 1) := by
        rw [List.length_take, Nat.min_eq_left hlen, Nat.pow_succ]; ac_rfl
      rw [← hys, subtrees_append _ (k + 1) _ _ ⟨r, by rw [hfirst, Nat.pow_succ]; ac_rfl⟩ (by rw [hlast, Nat.pow_succ]; omega),
        subtrees_pow _ k _ hlast, List.reverse_append, List.reverse_singleton, List.singleton_append,
        push_even _ _ _ _ _ (by omega) (by omega), show (2 * r + 1 + 1) / 2 = r + 1 by omega]
      have hb2 : (ys.drop (2 * r * 2 ^ k) ++ b).length = 2 ^ (k + 1) := by
        rw [List.length_append, hlast, hb, Nat.pow_succ]; omega
      rw [← treeOf_pair merge k _ _ hlast hb,
        ih r (by omega) (k + 1) _ _ hfirst hb2, List.append_assoc]

/-- Each piece is a full subtree in place: `2^k` elements after a prefix whose length `2^k`
divides. -/
def Aligned (pieces : List (List α)) : Prop :=
  ∀ i (h : i < pieces.length), ∃ k, pieces[i].length = 2 ^ k ∧ 2 ^ k ∣ (pieces.take i).flatten.length

/-- One step of pushing pieces: the stack, and the elements pushed so far. -/
def pushPiece (p : List α × Nat) (piece : List α) : List α × Nat :=
  (push merge p.1 (treeOf merge piece) (p.2 / piece.length + 1), p.2 + piece.length)

/-- The stack (top first) after pushing each piece's tree in turn. -/
def pushAll (pieces : List (List α)) : List α := (pieces.foldl (pushPiece merge) ([], 0)).1

/-- The root from a stack and the tree of the part after it: each stacked subtree the left child
of the node above the last part, top of the stack first. -/
def finish (stack : List α) (last : α) : α := stack.foldl (fun acc s => merge s acc) last

/-- The stack and count that pushing `done` leaves. -/
def state (done : List (List α)) : List α × Nat := ((subtrees merge done.flatten).reverse, done.flatten.length)

theorem pushPiece_state (done : List (List α)) (p : List α) (k : Nat) (hk : p.length = 2 ^ k)
    (hd : 2 ^ k ∣ done.flatten.length) : pushPiece merge (state merge done) p = state merge (done ++ [p]) := by
  obtain ⟨q, hq⟩ := hd
  rw [state, pushPiece, hk, hq, Nat.mul_div_cancel_left _ (Nat.two_pow_pos k),
    push_subtrees merge q k _ p (by rw [hq, Nat.mul_comm]) hk, state, List.flatten_append, List.flatten_singleton,
    List.length_append, hq, hk]

theorem foldl_state : ∀ (ps done : List (List α)), Aligned (done ++ ps) →
    ps.foldl (pushPiece merge) (state merge done) = state merge (done ++ ps) := by
  intro ps
  induction ps with
  | nil => intro done _; simp
  | cons p rest ih =>
    intro done ha
    obtain ⟨k, hk, hd⟩ := ha done.length (by simp)
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero,
      List.take_left' rfl] at hk hd
    rw [List.foldl_cons, pushPiece_state merge done p k hk hd, ih (done ++ [p]) (by simpa using ha), List.append_assoc,
      List.singleton_append]

theorem pushAll_eq (pieces : List (List α)) (ha : Aligned pieces) :
    pushAll merge pieces = (subtrees merge pieces.flatten).reverse := by
  have := foldl_state merge pieces [] (by simpa using ha)
  rw [show state merge [] = (([] : List α), 0) by simp [state, subtrees_nil], List.nil_append] at this
  rw [pushAll, this, state]

/-- **Cut and merge.** Pieces that are full subtrees in place, pushed in order, then a last part of
`1` to `2^k` elements after them, where `2^k` divides their length: the root is the tree's. -/
theorem cut_and_merge (pieces : List (List α)) (last : List α) (k : Nat) (ha : Aligned pieces)
    (hk : 2 ^ k ∣ pieces.flatten.length) (h0 : 0 < last.length) (hl : last.length ≤ 2 ^ k) :
    finish merge (pushAll merge pieces) (treeOf merge last) = treeOf merge (pieces.flatten ++ last) := by
  rw [pushAll_eq merge pieces ha, finish, List.foldl_reverse, treeOf_append merge k _ _ hk h0 hl]

theorem flatten_singletons (xs : List α) : (xs.map ([·])).flatten = xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [List.map_cons, List.flatten_cons, ih, List.singleton_append]

/-- **The incremental stack.** Chunks pushed one at a time, every chunk but the last, then the last
chunk at the bottom of the root's spine: the root is the tree's. -/
theorem incremental (xs : List α) (x : α) :
    finish merge (pushAll merge (xs.map ([·]))) x = treeOf merge (xs ++ [x]) := by
  have ha : Aligned (xs.map ([·])) := fun i h => ⟨0, by simp, by simp⟩
  have := cut_and_merge merge (xs.map ([·])) [x] 0 ha (by simp) (by simp) (by simp)
  rw [treeOf_single] at this
  rw [this, flatten_singletons]

/-! ## Extended output -/

theorem flatMap_flatten_map {α β γ : Type} (g : β → List γ) (f : α → List β) (L : List α) :
    ((L.map f).flatten).flatMap g = L.flatMap (fun a => (f a).flatMap g) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [List.flatMap_append, ih]

theorem bytesLE_length (ws : List Word) : (bytesLE ws).data.toList.length = 4 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [bytesLE, List.flatMap_cons, List.toList_toArray, List.length_append, List.length_cons, List.length_nil] at ih ⊢; omega

/-- Output block `i` of a root: its compression at counter `i` with `ROOT`, as bytes. -/
def blockBytes (root : Node) (i : Nat) : List UInt8 :=
  (bytesLE (BLAKE3_COMPRESS root.h root.m i.toUInt64 root.len (root.flags ||| ROOT)).toList).data.toList
/-- The first `B` output blocks. -/
def stream (root : Node) (B : Nat) : List UInt8 := (List.range B).flatMap (blockBytes root)

theorem blockBytes_length (root : Node) (i : Nat) : (blockBytes root i).length = 64 := by
  rw [blockBytes, bytesLE_length]; simp

theorem stream_length (root : Node) (B : Nat) : (stream root B).length = 64 * B := by
  induction B with
  | zero => rfl
  | succ B ih => rw [stream, List.range_succ, List.flatMap_append, List.length_append, ← stream, ih]; simp [blockBytes_length]; omega

/-- `output` is the first `n` bytes of the first `⌈n / 64⌉` blocks. -/
theorem output_data (root : Node) (n : Nat) : (output root n).data.toList = (stream root ((n + 63) / 64)).take n := by
  have : blockBytes root = fun i => (BLAKE3_COMPRESS root.h root.m i.toUInt64 root.len (root.flags ||| ROOT)).toList.flatMap
      fun (w : Word) => [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8] := by
    funext i; simp [blockBytes, bytesLE]
  simp [output, stream, bytesLE, flatMap_flatten_map, this]

theorem stream_add (root : Node) (B C : Nat) :
    stream root (B + C) = stream root B ++ (List.range C).flatMap (fun j => blockBytes root (B + j)) := by
  rw [stream, List.range_add, List.flatMap_append, List.flatMap_map, ← stream]

/-- A shorter output is a prefix of a longer one. -/
theorem output_prefix (root : Node) (n m : Nat) (h : n ≤ m) : output root n = (output root m).extract 0 n := by
  apply ByteArray.ext
  apply Array.toList_inj.1
  rw [ByteArray.data_extract, Array.toList_extract, output_data, output_data, List.extract]
  have hB : (n + 63) / 64 ≤ (m + 63) / 64 := Nat.div_le_div_right (by omega)
  rw [show (m + 63) / 64 = (n + 63) / 64 + ((m + 63) / 64 - (n + 63) / 64) by omega, stream_add,
    List.drop_zero, Nat.sub_zero, List.take_take, Nat.min_eq_left h,
    List.take_append_of_le_length (by rw [stream_length]; omega)]

/-- Bytes `64 i` to `64 i + 64` of an output are the root's compression at counter `i`: any block
of output is computed alone, from its counter (seeking). -/
theorem output_block (root : Node) (m i : Nat) (h : 64 * i + 64 ≤ m) :
    (output root m).extract (64 * i) (64 * i + 64) =
      bytesLE (BLAKE3_COMPRESS root.h root.m i.toUInt64 root.len (root.flags ||| ROOT)).toList := by
  apply ByteArray.ext
  apply Array.toList_inj.1
  rw [ByteArray.data_extract, Array.toList_extract, output_data, List.extract,
    show (m + 63) / 64 = i + (1 + ((m + 63) / 64 - i - 1)) by omega, stream_add, List.range_add,
    List.flatMap_append, List.range_one, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.add_zero,
    Nat.add_sub_cancel_left, List.drop_take, List.drop_append_of_le_length (by rw [stream_length]; omega)]
  rw [List.drop_of_length_le (by rw [stream_length]; omega), List.nil_append, List.take_take,
    show min 64 (m - 64 * i) = 64 by omega, Nat.add_zero,
    List.take_append_of_le_length (by rw [blockBytes_length]; omega),
    List.take_of_length_le (by rw [blockBytes_length]; omega), blockBytes]

/-! ## Counters -/

/-- A chunk's counter: for an input under `2^64` bytes the chunk index fits in 64 bits, so the
counter is the index itself (no wrap). The same holds for an output block's counter, by
`output_counter`. -/
theorem chunk_counter (size i : Nat) (hs : size < 2 ^ 64) (hi : i < max 1 ((size + 1023) / 1024)) :
    i.toUInt64.toNat = i := by
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

theorem output_counter (outLen i : Nat) (hs : outLen < 2 ^ 64) (hi : i < (outLen + 63) / 64) :
    i.toUInt64.toNat = i := by
  rw [Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-! ## BLAKE3's chunks -/

/-- The chunk nodes `blake3` builds its tree over. -/
def chunkNodes (key : Vector Word 8) (mode : Word) (input : ByteArray) : Array Node :=
  (Array.range (max 1 ((input.size + 1023) / 1024))).map fun i =>
    chunkNode key mode (input.extract (1024 * i) (1024 * (i + 1))) i

theorem blake3_tree (key : Vector Word 8) (mode : Word) (input : ByteArray) (outLen : Nat) :
    blake3 key mode input outLen = output (treeOf (parent key mode) (chunkNodes key mode input).toList) outLen := by
  rw [← tree_eq key mode _ (by simp [chunkNodes]; omega)]
  rfl

/-- **The incremental stack, for BLAKE3.** Every chunk but the last pushed one at a time, then the
last at the bottom of the root's spine: the definition's output. -/
theorem blake3_incremental (key : Vector Word 8) (mode : Word) (input : ByteArray) (outLen : Nat) :
    let chunks := (chunkNodes key mode input).toList
    blake3 key mode input outLen =
      output (finish (parent key mode) (pushAll (parent key mode) (chunks.dropLast.map ([·]))) chunks.getLast!) outLen := by
  intro chunks
  have hne : chunks ≠ [] := by
    intro h; have := congrArg List.length h; simp [chunks, chunkNodes] at this
  have split : ∀ l : List Node, l ≠ [] → l.dropLast ++ [l.getLast!] = l := by
    intro l h
    cases l with
    | nil => contradiction
    | cons a l => rw [List.getLast!, List.dropLast_concat_getLast]
  rw [blake3_tree, incremental, split chunks hne]

/-- **Cut and merge, for BLAKE3.** The chunks cut into full subtrees in place, each hashed alone and
pushed in order, then a last part of `1` to `2^k` chunks after `2^k`-aligned pieces: the
definition's output. -/
theorem blake3_cut_and_merge (key : Vector Word 8) (mode : Word) (input : ByteArray) (outLen : Nat)
    (pieces : List (List Node)) (last : List Node) (k : Nat)
    (hcut : pieces.flatten ++ last = (chunkNodes key mode input).toList) (ha : Aligned pieces)
    (hk : 2 ^ k ∣ pieces.flatten.length) (h0 : 0 < last.length) (hl : last.length ≤ 2 ^ k) :
    blake3 key mode input outLen =
      output (finish (parent key mode) (pushAll (parent key mode) pieces) (treeOf (parent key mode) last)) outLen := by
  rw [blake3_tree, cut_and_merge _ pieces last k ha hk h0 hl, hcut]


end Blake3.Algorithms

#print axioms Blake3.Algorithms.tree_eq
#print axioms Blake3.Algorithms.cut_and_merge
#print axioms Blake3.Algorithms.incremental
#print axioms Blake3.Algorithms.blake3_incremental
#print axioms Blake3.Algorithms.blake3_cut_and_merge
#print axioms Blake3.Algorithms.output_prefix
#print axioms Blake3.Algorithms.output_block
#print axioms Blake3.Algorithms.chunk_counter
#print axioms Blake3.Algorithms.output_counter
