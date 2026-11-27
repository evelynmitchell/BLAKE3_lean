import Blake3
import Theorems

/-! # The algorithms the library computes the tree with, proved to compute `Blake3.lean`'s

`Blake3.lean` defines BLAKE3's tree by recursion: the left subtree of `n ≥ 2` chunks holds
`leftCount n` of them. The library never evaluates it so: its `Hasher` pushes chunks on a stack of
subtrees and merges as it goes (`src/hasher.rs`), and the pool and the grouped calls cut the input
into subtrees, hash each on its own, and merge their values (`threads/src/lanes.rs`,
`src/each.rs`); the `Hasher`'s stack may hold a subtree as a row of its parts' values, merged a
layer at a time; and `b3sum --outboard` writes the tree above a file's 16 KiB groups, built a layer at a time
and walked by index. This file writes those algorithms down and proves each gives the definition's
result, for every input.

The tree theorems are about the tree's shape, so they hold for any function merging two values
(`merge`); `tree` is `treeOf` with BLAKE3's parent node as the merge (`tree_eq`), and `blake3_*`
state them for BLAKE3's own chunks. What remains outside: that the Rust implements these
algorithms. The tests compare the Rust with the definition (`test_vectors/lean_vectors.json`); the
models here are what those tests' passing would be about. -/

set_option linter.unusedSectionVars false
-- `if_pos`, `if_neg`, `dif_neg`: their replacements take the condition as an equation.
set_option linter.deprecated false

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

/-! ## Rows

The `Hasher`'s stack (`CvStack`, `src/hasher.rs`) may hold a full subtree as a row: the values of
its `n` equal parts (`n` a power of two), not its one value. Rows merge with rows a layer of parents
at a time; a row becomes its one value when the output needs it or it meets a single value. These
theorems show a row is that subtree's value, deferred: condensing one gives the subtree's tree, and
merging two then condensing gives the parent of their trees. -/

/-- One layer of parents: each two adjacent values merged. -/
def layer : List α → List α
  | a :: b :: rest => merge a b :: layer rest
  | xs => xs

/-- `xs` cut into consecutive groups of `s`. -/
def groups (s : Nat) (xs : List α) : List (List α) :=
  if _ : 0 < s ∧ xs ≠ [] then xs.take s :: groups s (xs.drop s) else []
termination_by xs.length
decreasing_by
  have := List.length_pos_iff.2 ‹0 < s ∧ xs ≠ []›.2
  simp only [List.length_drop]; omega

theorem groups_nil (s : Nat) : groups s ([] : List α) = [] := by
  rw [groups]; simp

theorem groups_cons (s : Nat) (xs : List α) (hs : 0 < s) (h : xs ≠ []) :
    groups s xs = xs.take s :: groups s (xs.drop s) := by
  rw [groups]; simp [hs, h]

theorem groups_append (s : Nat) (hs : 0 < s) : ∀ (A B : List α), s ∣ A.length → groups s (A ++ B) = groups s A ++ groups s B := by
  suffices ∀ n (A B : List α), A.length = n → s ∣ A.length → groups s (A ++ B) = groups s A ++ groups s B from
    fun A B => this _ A B rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro A B hn hd
    by_cases hA : A = []
    · subst hA; simp [groups_nil]
    have h0 : 0 < A.length := List.length_pos_iff.2 hA
    have hle : s ≤ A.length := Nat.le_of_dvd h0 hd
    rw [groups_cons s (A ++ B) hs (by simp [hA]), groups_cons s A hs hA, List.take_append_of_le_length hle,
      List.drop_append_of_le_length hle,
      ih (A.length - s) (by omega) (A.drop s) B (by simp) (by simpa using Nat.dvd_sub hd (Nat.dvd_refl s)),
      List.cons_append]

/-- A full subtree held as a row: the trees of its consecutive parts of `s` elements. -/
def row (s : Nat) (xs : List α) : List α := (groups s xs).map (treeOf merge)

/-- A layer of parents over a row is the row of parts twice as long: halving a row's width. -/
theorem layer_row (b : Nat) : ∀ (xs : List α), 2 ^ (b + 1) ∣ xs.length →
    layer merge (row merge (2 ^ b) xs) = row merge (2 ^ (b + 1)) xs := by
  suffices ∀ n (xs : List α), xs.length = n → 2 ^ (b + 1) ∣ xs.length →
      layer merge (row merge (2 ^ b) xs) = row merge (2 ^ (b + 1)) xs from
    fun xs => this _ xs rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs hn hd
    have hp := Nat.two_pow_pos b
    by_cases hx : xs = []
    · subst hx; simp [row, groups_nil, layer]
    have h0 : 0 < xs.length := List.length_pos_iff.2 hx
    have hle : 2 ^ (b + 1) ≤ xs.length := Nat.le_of_dvd h0 hd
    have h2 : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
    have hd2 : xs.drop (2 ^ b) ≠ [] := by
      intro h; have := congrArg List.length h; simp at this; omega
    rw [row, groups_cons _ xs (by omega) hx, groups_cons _ (xs.drop (2 ^ b)) (by omega) hd2, List.drop_drop,
      List.map_cons, List.map_cons, layer, ← treeOf_pair merge b _ _ (by simp; omega) (by simp; omega),
      ← List.take_add, ← h2, ← row,
      ih (xs.length - 2 ^ (b + 1)) (by omega) _ (by simp)
        (by simpa using Nat.dvd_sub hd (Nat.dvd_refl _)),
      row, row, groups_cons _ xs (by omega) hx, List.map_cons]

/-- A layer over rows side by side, each of an even width, is each row's layer side by side: so
`CvStack::condense` may run several rows' layers through one tile of parents. -/
theorem layer_append : ∀ (r s : List α), r.length % 2 = 0 → layer merge (r ++ s) = layer merge r ++ layer merge s := by
  suffices ∀ n (r s : List α), r.length = n → r.length % 2 = 0 → layer merge (r ++ s) = layer merge r ++ layer merge s from
    fun r s => this _ r s rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro r s hn he
    match r with
    | [] => rfl
    | [_] => simp at he
    | a :: b :: rest =>
      simp only [List.cons_append, layer]
      rw [ih rest.length (by simp at hn; omega) rest s rfl (by simp at he; omega)]

/-- `a` layers of parents. -/
def condense : Nat → List α → List α
  | 0, r => r
  | a + 1, r => condense a (layer merge r)

/-- **A row condenses to its subtree's tree.** A full subtree of `2^(a+b)` elements, held as the row of
its `2^a` parts of `2^b`: `a` layers of parents give its tree (`CvStack::get`, `condense`,
`narrow`). -/
theorem condense_row : ∀ (a b : Nat) (xs : List α), xs.length = 2 ^ (a + b) →
    condense merge a (row merge (2 ^ b) xs) = [treeOf merge xs] := by
  intro a
  induction a with
  | zero =>
    intro b xs hx
    have hp := Nat.two_pow_pos b
    have hne : xs ≠ [] := by intro h; subst h; simp at hx; omega
    rw [Nat.zero_add] at hx
    rw [condense, row, groups_cons _ xs hp hne, List.take_of_length_le (by omega), List.drop_of_length_le (by omega),
      groups_nil]
    rfl
  | succ a ih =>
    intro b xs hx
    rw [condense, layer_row merge b xs ⟨2 ^ a, by rw [hx, ← Nat.pow_add]; congr 1; omega⟩,
      ih (b + 1) xs (by rw [hx]; congr 1; omega)]

/-- **Two rows merge into their parent's row.** Sibling full subtrees `A` and `B`, each held as the
row of its parts of `2^b`: one layer of parents over the two rows side by side is the parent
subtree's row, of parts of `2^(b+1)`, as wide as each (`CvStack::merge`). -/
theorem merge_rows (b : Nat) (A B : List α) (hA : 2 ^ b ∣ A.length)
    (hd : 2 ^ (b + 1) ∣ (A ++ B).length) :
    layer merge (row merge (2 ^ b) A ++ row merge (2 ^ b) B) = row merge (2 ^ (b + 1)) (A ++ B) := by
  rw [row, row, ← List.map_append, ← groups_append _ (Nat.two_pow_pos b) A B hA, ← row, layer_row merge b _ hd]

/-- Merging two rows and condensing gives the parent of the subtrees' trees: rows only defer the
merges a single-valued stack makes, whatever the width (`4` to `ROW`) each is held at. -/
theorem merge_rows_value (a b : Nat) (A B : List α) (hA : A.length = 2 ^ (a + b)) (hB : B.length = 2 ^ (a + b)) :
    condense merge a (layer merge (row merge (2 ^ b) A ++ row merge (2 ^ b) B)) = [merge (treeOf merge A) (treeOf merge B)] := by
  have hlen : (A ++ B).length = 2 ^ (a + (b + 1)) := by
    rw [List.length_append, hA, hB, show a + (b + 1) = (a + b) + 1 by omega, Nat.pow_succ]; omega
  rw [merge_rows merge b A B (hA ▸ Nat.pow_dvd_pow 2 (by omega))
      (hlen ▸ Nat.pow_dvd_pow 2 (by omega)),
    condense_row merge a (b + 1) _ hlen, treeOf_pair merge (a + b) A B hA hB]

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


/-! ## The outboard

`b3sum --outboard` (`b3sum/src/outboard.rs`) writes the tree above a file's 16 KiB groups: each
parent as its two children's values, in pre-order. It builds the values a layer at a time from the
groups' (`build`), then walks them by index from the root (`node`). `lval` and `nodes` are those two,
with a layer's count of whole values `whole`; `obao` is the specification's outboard, the pre-order
of the tree over the groups. -/

/-- The specification's outboard over values `vs` (the groups' trees): each parent of the tree over
them as its two children's trees, in pre-order (the parent, its left subtree, its right subtree). -/
def obao (vs : List α) : List (α × α) :=
  if _ : vs.length ≤ 1 then []
  else (treeOf merge (vs.take (leftCount vs.length)), treeOf merge (vs.drop (leftCount vs.length))) ::
    (obao (vs.take (leftCount vs.length)) ++ obao (vs.drop (leftCount vs.length)))
termination_by vs.length
decreasing_by
  · simp only [List.length_take]; have := leftCount_lt vs.length (by omega); omega
  · simp only [List.length_drop]; have := leftCount_pos vs.length; omega

/-- The values of layer `h` whole below its last, of `g` group values: `(g - 1) / 2^h`. -/
def whole (g h : Nat) : Nat := (g - 1) / 2 ^ h

/-- Value `j` of layer `h`, as `build` computes it: a group's own at layer 0; above, the parent of
values `2j` and `2j + 1` below where `2j + 1` is a whole value or the last, else value `2j` passed
up as it is. -/
def lval (vs : List α) : Nat → Nat → α
  | 0, j => vs[j]!
  | h + 1, j => if 2 * j + 1 ≤ whole vs.length h then merge (lval vs h (2 * j)) (lval vs h (2 * j + 1)) else lval vs h (2 * j)

/-- Node `i` of layer `h` and the nodes below it, in pre-order, as `node` writes them: a parent as
its two children's values; one whose right child is past its layer is no parent. -/
def nodes (vs : List α) : Nat → Nat → List (α × α)
  | 0, _ => []
  | h + 1, i =>
    if whole vs.length h < 2 * i + 1 then nodes vs h (2 * i)
    else (lval merge vs h (2 * i), lval merge vs h (2 * i + 1)) :: (nodes vs h (2 * i) ++ nodes vs h (2 * i + 1))

/-- The groups under node `i` of layer `h`. -/
def seg (vs : List α) (h i : Nat) : List α := (vs.drop (i * 2 ^ h)).take (2 ^ h)

theorem seg_succ (vs : List α) (h i : Nat) : seg vs (h + 1) i = seg vs h (2 * i) ++ seg vs h (2 * i + 1) := by
  simp only [seg]
  rw [show (2 * i + 1) * 2 ^ h = 2 * i * 2 ^ h + 2 ^ h by rw [Nat.add_mul, Nat.one_mul],
    show i * 2 ^ (h + 1) = 2 * i * 2 ^ h by rw [Nat.pow_succ]; ac_rfl, ← List.drop_drop,
    Nat.pow_succ, Nat.mul_two, List.take_add]

/-- Every value `build` computes is the tree of the groups under it, and every list of nodes `node`
writes is the specification's outboard over them. -/
theorem lval_nodes (vs : List α) (g : Nat) (hg : vs.length = g) : ∀ h i, i * 2 ^ h < g →
    lval merge vs h i = treeOf merge (seg vs h i) ∧ nodes merge vs h i = obao merge (seg vs h i) := by
  intro h
  induction h with
  | zero =>
    intro i hi
    simp only [Nat.pow_zero, Nat.mul_one] at hi
    have hs : seg vs 0 i = [vs[i]] := by
      simp only [seg, Nat.pow_zero, Nat.mul_one]
      rw [List.drop_eq_getElem_cons (by omega)]; rfl
    refine ⟨?_, ?_⟩
    · rw [hs, treeOf_single, lval]; exact getElem!_pos vs i (by omega)
    · rw [hs, nodes, obao]; simp
  | succ h ih =>
    intro i hi
    have hp := Nat.two_pow_pos h
    have hi2 : 2 * i * 2 ^ h < g := by rw [Nat.pow_succ] at hi; rw [show 2 * i * 2 ^ h = i * (2 ^ h * 2) by ac_rfl]; exact hi
    obtain ⟨ihl, ihn⟩ := ih (2 * i) hi2
    have hlen1 : (seg vs h (2 * i)).length = min (2 ^ h) (g - 2 * i * 2 ^ h) := by simp [seg, hg]
    by_cases hw : whole g h < 2 * i + 1
    · -- No right child: the groups past the left are none.
      have hnone : seg vs h (2 * i + 1) = [] := by
        simp only [seg, whole] at hw ⊢
        have : g ≤ (2 * i + 1) * 2 ^ h := by
          have := (Nat.div_lt_iff_lt_mul hp).1 hw; omega
        rw [List.drop_of_length_le (by omega), List.take_nil]
      rw [seg_succ, hnone, List.append_nil, lval, nodes, hg, if_neg (by omega), if_pos hw]
      exact ⟨ihl, ihn⟩
    · -- Both children: the left whole, the right of 1 to 2^h groups.
      have hle : (2 * i + 1) * 2 ^ h ≤ g - 1 := (Nat.le_div_iff_mul_le hp).1 (by simp only [whole] at hw; omega)
      obtain ⟨ihlr, ihnr⟩ := ih (2 * i + 1) (by omega)
      have hl : (seg vs h (2 * i)).length = 2 ^ h := by rw [hlen1]; rw [Nat.add_mul, Nat.one_mul] at hle; omega
      have hr0 : 0 < (seg vs h (2 * i + 1)).length := by simp [seg, hg]; omega
      have hr : (seg vs h (2 * i + 1)).length ≤ 2 ^ h := by simp only [seg, List.length_take]; omega
      have hsplit : leftCount (seg vs (h + 1) i).length = 2 ^ h := by
        rw [seg_succ, List.length_append, hl, leftCount,
          show 2 ^ h + (seg vs h (2 * i + 1)).length - 1 = 2 ^ h + ((seg vs h (2 * i + 1)).length - 1) by omega,
          log2_add _ _ h hp (Nat.dvd_refl _) (by omega), Nat.log2_two_pow]
      have hlen : 2 ≤ (seg vs (h + 1) i).length := by rw [seg_succ, List.length_append]; omega
      have htake : (seg vs (h + 1) i).take (2 ^ h) = seg vs h (2 * i) := by
        rw [seg_succ]; exact List.take_left' hl
      have hdrop : (seg vs (h + 1) i).drop (2 ^ h) = seg vs h (2 * i + 1) := by
        rw [seg_succ]; exact List.drop_left' hl
      refine ⟨?_, ?_⟩
      · rw [lval, hg, if_pos (by omega), ihl, ihlr, treeOf_split merge _ hlen, hsplit, htake, hdrop]
      · conv => rhs; rw [obao]
        rw [dif_neg (by omega), nodes, hg, if_neg hw, ihl, ihlr, ihn, ihnr, hsplit, htake, hdrop]

/-- **The outboard.** Over `g ≥ 2` group values, with `H = log2 (g - 1)` the top layer (the one
of one whole value): the nodes `node` writes from the root, node 0 of the layer above the top,
are the specification's outboard, and the top's two values merge to the tree's root. -/
theorem outboard (vs : List α) (hg : 2 ≤ vs.length) :
    nodes merge vs ((vs.length - 1).log2 + 1) 0 = obao merge vs ∧
      merge (lval merge vs (vs.length - 1).log2 0) (lval merge vs (vs.length - 1).log2 1) = treeOf merge vs := by
  have hi := Nat.lt_log2_self (n := vs.length - 1)
  have lo := Nat.log2_self_le (n := vs.length - 1) (by omega)
  have hseg : seg vs ((vs.length - 1).log2 + 1) 0 = vs := by
    simp only [seg, Nat.zero_mul, List.drop_zero]; exact List.take_of_length_le (by omega)
  obtain ⟨hl, hn⟩ := lval_nodes merge vs vs.length rfl _ 0 (by simp; omega)
  rw [hseg] at hl hn
  refine ⟨hn, ?_⟩
  rw [← hl, lval, if_pos ?_]
  simp only [whole, Nat.mul_zero, Nat.zero_add]
  exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2 (by omega)

/-- `xs` cut into groups of `s`: `⌈|xs| / s⌉` of them. -/
theorem length_groups (s : Nat) (hs : 0 < s) : ∀ (xs : List α), (groups s xs).length = (xs.length + s - 1) / s := by
  suffices ∀ n (xs : List α), xs.length = n → (groups s xs).length = (xs.length + s - 1) / s from fun xs => this _ xs rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs hn
    by_cases hx : xs = []
    · subst hx; simp only [groups_nil, List.length_nil, Nat.zero_add]; exact (Nat.div_eq_of_lt (by omega)).symm
    have h0 : 0 < xs.length := List.length_pos_iff.2 hx
    rw [groups_cons s xs hs hx, List.length_cons, ih (xs.length - s) (by omega) (xs.drop s) (by simp)]
    simp only [List.length_drop]
    by_cases hle : s ≤ xs.length
    · rw [show xs.length + s - 1 = (xs.length - s + s - 1) + s by omega, Nat.add_div_right _ hs]
    · rw [show xs.length - s = 0 by omega]
      rw [Nat.div_eq_of_lt (by omega), show xs.length + s - 1 = (xs.length - 1) + s by omega, Nat.add_div_right _ hs,
        Nat.div_eq_of_lt (by omega)]

/-- Past `2^b` elements, the tree splits at `2^b` times where the tree over its groups of `2^b`
splits. -/
theorem leftCount_groups (b n : Nat) (hn : 2 ^ b < n) :
    leftCount n = 2 ^ b * leftCount ((n + 2 ^ b - 1) / 2 ^ b) := by
  have hp := Nat.two_pow_pos b
  have hq : (n + 2 ^ b - 1) / 2 ^ b - 1 = (n - 1) / 2 ^ b := by
    rw [show n + 2 ^ b - 1 = (n - 1) + 2 ^ b by omega, Nat.add_div_right _ hp]; rfl
  have q1 : 1 ≤ (n - 1) / 2 ^ b := (Nat.le_div_iff_mul_le hp).2 (by omega)
  have lo := Nat.log2_self_le (n := (n - 1) / 2 ^ b) (by omega)
  have hi := Nat.lt_log2_self (n := (n - 1) / 2 ^ b)
  have hd := Nat.div_mul_le_self (n - 1) (2 ^ b)
  have hm := Nat.lt_mul_div_succ (n - 1) hp
  have h1 : ((n - 1) / 2 ^ b).log2 + b ≤ (n - 1).log2 :=
    (Nat.le_log2 (by omega)).2 (by rw [Nat.pow_add]; exact Nat.le_trans (Nat.mul_le_mul_right _ lo) hd)
  have h2 : (n - 1).log2 < ((n - 1) / 2 ^ b).log2 + b + 1 := by
    apply (Nat.log2_lt (by omega)).2
    rw [show ((n - 1) / 2 ^ b).log2 + b + 1 = (((n - 1) / 2 ^ b).log2 + 1) + b by omega, Nat.pow_add]
    exact Nat.lt_of_lt_of_le hm (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hi)
  rw [leftCount, leftCount, hq, show (n - 1).log2 = ((n - 1) / 2 ^ b).log2 + b by omega, Nat.pow_add, Nat.mul_comm]

/-- **Groups lift.** The tree over a list is the tree over its groups' trees, for groups of any
power of two: the tree over a file's 16 KiB groups, which the outboard holds, is the file's. -/
theorem treeOf_row (b : Nat) : ∀ (xs : List α), xs ≠ [] → treeOf merge xs = treeOf merge (row merge (2 ^ b) xs) := by
  suffices ∀ n (xs : List α), xs.length = n → xs ≠ [] → treeOf merge xs = treeOf merge (row merge (2 ^ b) xs) from
    fun xs => this _ xs rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro xs hn hx
    have hp := Nat.two_pow_pos b
    have h0 : 0 < xs.length := List.length_pos_iff.2 hx
    by_cases hs : xs.length ≤ 2 ^ b
    · rw [row, groups_cons _ xs hp hx, List.take_of_length_le hs, List.drop_of_length_le hs, groups_nil,
        List.map_cons, List.map_nil, treeOf_single]
    -- The split: the left part's groups are the left part of the groups.
    have hL := leftCount_groups b xs.length (by omega)
    have hg : (row merge (2 ^ b) xs).length = (xs.length + 2 ^ b - 1) / 2 ^ b := by
      rw [row, List.length_map, length_groups _ hp]
    have hg2 : 2 ≤ (xs.length + 2 ^ b - 1) / 2 ^ b := (Nat.le_div_iff_mul_le hp).2 (by omega)
    have hlt := leftCount_lt xs.length (by omega)
    have hpos := leftCount_pos xs.length
    have hrows : row merge (2 ^ b) xs = row merge (2 ^ b) (xs.take (leftCount xs.length)) ++ row merge (2 ^ b) (xs.drop (leftCount xs.length)) := by
      rw [row, row, row, ← List.map_append, ← groups_append _ hp _ _ (by simp; rw [Nat.min_eq_left (by omega), hL]; exact Nat.dvd_mul_right _ _),
        List.take_append_drop]
    have hleft : (row merge (2 ^ b) (xs.take (leftCount xs.length))).length = leftCount (row merge (2 ^ b) xs).length := by
      rw [hg, row, List.length_map, length_groups _ hp, List.length_take, Nat.min_eq_left (by omega), hL,
        show 2 ^ b * leftCount ((xs.length + 2 ^ b - 1) / 2 ^ b) + 2 ^ b - 1 = (2 ^ b - 1) + leftCount ((xs.length + 2 ^ b - 1) / 2 ^ b) * 2 ^ b by
          rw [Nat.mul_comm]; omega,
        Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt (by omega), Nat.zero_add]
    have hA : (xs.take (leftCount xs.length)).length < n := by rw [List.length_take]; omega
    have hB : (xs.drop (leftCount xs.length)).length < n := by rw [List.length_drop]; omega
    have hA0 : xs.take (leftCount xs.length) ≠ [] := by
      intro h; have := congrArg List.length h; rw [List.length_take, List.length_nil] at this; omega
    have hB0 : xs.drop (leftCount xs.length) ≠ [] := by
      intro h; have := congrArg List.length h; rw [List.length_drop, List.length_nil] at this; omega
    rw [treeOf_split merge xs (by omega), treeOf_split merge (row merge (2 ^ b) xs) (by omega), ← hleft, hrows,
      List.take_left' rfl, List.drop_left' rfl,
      ← ih _ hA (xs.take (leftCount xs.length)) rfl hA0, ← ih _ hB (xs.drop (leftCount xs.length)) rfl hB0]

/-- **The outboard, for BLAKE3.** For an input of more than one group of 16 chunks (16 KiB), over
its groups' trees: the parent pairs `b3sum --outboard` writes are the specification's outboard,
and the top layer's two values merge to the root, so the hash is the definition's. -/
theorem blake3_outboard (key : Vector Word 8) (mode : Word) (input : ByteArray) (outLen : Nat)
    (h : 16 < (chunkNodes key mode input).size) :
    let vs := row (parent key mode) (2 ^ 4) (chunkNodes key mode input).toList
    nodes (parent key mode) vs ((vs.length - 1).log2 + 1) 0 = obao (parent key mode) vs ∧
      blake3 key mode input outLen =
        output (parent key mode (lval (parent key mode) vs (vs.length - 1).log2 0)
          (lval (parent key mode) vs (vs.length - 1).log2 1)) outLen := by
  intro vs
  have hv : 2 ≤ vs.length := by
    simp only [vs, row, List.length_map, length_groups _ (Nat.two_pow_pos 4), Array.length_toList]
    exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos 4)).2 (by simp; omega)
  obtain ⟨hn, hr⟩ := outboard (parent key mode) vs hv
  refine ⟨hn, ?_⟩
  have hne : (chunkNodes key mode input).toList ≠ [] := by
    intro e; have := congrArg List.length e; rw [Array.length_toList, List.length_nil] at this; omega
  rw [hr, blake3_tree, treeOf_row (parent key mode) 4 _ hne]

end Blake3.Algorithms

#print axioms Blake3.Algorithms.tree_eq
#print axioms Blake3.Algorithms.cut_and_merge
#print axioms Blake3.Algorithms.incremental
#print axioms Blake3.Algorithms.blake3_incremental
#print axioms Blake3.Algorithms.blake3_cut_and_merge
#print axioms Blake3.Algorithms.condense_row
#print axioms Blake3.Algorithms.merge_rows
#print axioms Blake3.Algorithms.merge_rows_value
#print axioms Blake3.Algorithms.layer_append
#print axioms Blake3.Algorithms.lval_nodes
#print axioms Blake3.Algorithms.outboard
#print axioms Blake3.Algorithms.treeOf_row
#print axioms Blake3.Algorithms.blake3_outboard
#print axioms Blake3.Algorithms.output_prefix
#print axioms Blake3.Algorithms.output_block
#print axioms Blake3.Algorithms.chunk_counter
#print axioms Blake3.Algorithms.output_counter
