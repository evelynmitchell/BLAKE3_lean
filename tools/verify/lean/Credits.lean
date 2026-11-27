/-! # A room's credit count, at its real size

`threads/src/pipeline.rs` counts each room's credits in one `usize` word (`Rooms::refs`): a Room
is handed out with `ROOM_CREDITS` (2^30) on the count (`init_taken`); each commit spends one of the
Room's own, which its piece carries to a worker, and at `ROOM_CREDITS - 1` commits the Room takes a
new set rather than give out its last (`Room::take_credit`); a worker gives its piece's credit
back when it has read the bytes (`Rooms::release_n`); the Room's drop gives back what it has left
(`Room::drop`). The room is free when the count is 0. `Pipeline::drop` stamps the word's top bit,
`ROOM_CLOSING_BIT` (2^63). A short message's commit spends a credit too, which its slot, then
its group, holds until the group gives back its members' credits at once; an empty commit to a
message fed through rooms spends none (`commit_multi` returns first).

`PipeRooms.tla` checks these steps' schedules with 3 credits. Here they are at 2^30, on 64-bit
words, for every sequence of steps: each keeps the count equal to the Room's unspent credits plus
the credits out to pieces, no step wraps the word, the count stays below the closing bit, a room
is free exactly when no Room and no piece holds it, and a Room's drop wakes the owner exactly when
it frees the room.

The one assumption: at most `2^32` credits out of one room at once, to pieces and short messages.
They are bounded by the Pipeline's piece nodes and message slots, fixed allocations of far fewer. -/

namespace Blake3.Credits

/-- `ROOM_CREDITS`, 2^30. -/
def C : Nat := 1073741824
/-- `ROOM_CLOSING_BIT`, 2^63. -/
def CLOSING : Nat := 9223372036854775808
/-- A `usize` word on the 64-bit targets the library builds for: 2^64. -/
def WORD : Nat := 18446744073709551616
/-- The most credits out to one room's pieces at once (the assumption above): 2^32. -/
def PIECES : Nat := 4294967296

/-- One room: its count, whether a Room holds it and that Room's commits, and the credits its
pieces hold. -/
structure Room where
  refs : Nat
  held : Bool
  commits : Nat
  out : Nat

/-- Held, the count is the Room's unspent credits and the pieces' credits, and the Room's commits
stay below `C`, so it always has one left; not held, the count is the pieces' credits. At most
`PIECES` credits are out. -/
def Inv (r : Room) : Prop :=
  (r.held = true → r.refs = (C - r.commits) + r.out ∧ r.commits < C) ∧
  (r.held = false → r.refs = r.out) ∧ r.out ≤ PIECES

/-- `init_taken`: a free room handed out (only when its count is 0). -/
def take (r : Room) : Room := { r with refs := C, held := true, commits := 0 }

/-- `take_credit` and the commit's piece: at `C - 1` commits the Room adds `C - 1` to the count
and starts over; then it spends one, which goes out with the piece. -/
def commit (r : Room) : Room :=
  if r.commits = C - 1 then { r with refs := r.refs + (C - 1), commits := 1, out := r.out + 1 }
  else { r with commits := r.commits + 1, out := r.out + 1 }

/-- `release_n(room, n)`: credits out given back, `n` of them: a room piece's one when its worker
has read the bytes (`run_room_piece`), a group's members' at once (`run_group`), an aborted or
dropped short message's one (`abort_slot`, `Pipeline::drop`). -/
def release (r : Room) (n : Nat) : Room := { r with refs := r.refs - n, out := r.out - n }

/-- `Room::drop`: the unspent credits back (`fetch_sub`). -/
def drop (r : Room) : Room := { r with refs := r.refs - (C - r.commits), held := false, commits := 0 }

/-! ## Each step keeps the invariant, within its precondition -/

theorem take_inv (r : Room) (h : Inv r) (hfree : r.refs = 0) (hnot : r.held = false) : Inv (take r) := by
  obtain ⟨_, h2, h3⟩ := h
  have := h2 hnot
  simp only [Inv, take, C] at *
  refine ⟨fun _ => ⟨by omega, by omega⟩, fun h => by simp at h, by omega⟩

theorem commit_inv (r : Room) (h : Inv r) (hheld : r.held = true) (hout : r.out < PIECES) : Inv (commit r) := by
  obtain ⟨h1, _, h3⟩ := h
  obtain ⟨hr, hc⟩ := h1 hheld
  unfold commit
  split <;> simp only [Inv, C, PIECES] at * <;>
    exact ⟨fun _ => ⟨by omega, by omega⟩, fun h => by simp [hheld] at h, by omega⟩

theorem release_inv (r : Room) (n : Nat) (h : Inv r) (hout : n ≤ r.out) : Inv (release r n) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Inv, release]
  refine ⟨fun hh => ?_, fun hh => ?_, by omega⟩
  · obtain ⟨hr, hc⟩ := h1 hh; exact ⟨by omega, hc⟩
  · have := h2 hh; omega

theorem drop_inv (r : Room) (h : Inv r) (hheld : r.held = true) : Inv (drop r) := by
  obtain ⟨h1, _, h3⟩ := h
  obtain ⟨hr, hc⟩ := h1 hheld
  simp only [Inv, drop]
  exact ⟨fun h => by simp at h, fun _ => by omega, h3⟩

/-! ## What the invariant gives -/

theorem refs_bound (r : Room) (h : Inv r) : r.refs ≤ C + PIECES := by
  obtain ⟨h1, h2, h3⟩ := h
  cases hh : r.held
  · have := h2 hh; omega
  · have := h1 hh; omega

/-- The count never reaches the closing bit: that bit is only ever the stamp. -/
theorem refs_lt_closing (r : Room) (h : Inv r) : r.refs < CLOSING := by
  have := refs_bound r h
  simp only [C, PIECES, CLOSING] at *; omega

/-- No step wraps the word: a commit's renewal adds within it, a release and a drop subtract
at most the count. -/
theorem commit_no_wrap (r : Room) (h : Inv r) : r.refs + (C - 1) < WORD := by
  have := refs_bound r h
  simp only [C, PIECES, WORD] at *; omega

theorem release_no_wrap (r : Room) (n : Nat) (h : Inv r) (hout : n ≤ r.out) : n ≤ r.refs := by
  obtain ⟨h1, h2, _⟩ := h
  cases hh : r.held
  · have := h2 hh; omega
  · have := h1 hh; omega

theorem drop_no_wrap (r : Room) (h : Inv r) (hheld : r.held = true) : C - r.commits ≤ r.refs := by
  have := (h.1 hheld).1; omega

/-- A held Room's commits fit its `u32` field. -/
theorem commits_fit (r : Room) (h : Inv r) (hheld : r.held = true) : r.commits < 2 ^ 32 := by
  have := (h.1 hheld).2; simp only [C] at this; omega

/-- **A room is free exactly when no Room and no piece holds it** (`try_take_room` hands out only
a count of 0): a held Room always has a credit unspent. -/
theorem free_iff (r : Room) (h : Inv r) : r.refs = 0 ↔ (r.held = false ∧ r.out = 0) := by
  obtain ⟨h1, h2, _⟩ := h
  cases hh : r.held
  · have := h2 hh; simp; omega
  · have := h1 hh; simp only [C] at this; simp; omega

/-- **A Room's drop wakes the owner exactly when it frees the room**: `Room::drop` notifies when
the count it subtracted from (`prev`) was its unspent credits alone, which is when no piece holds
a credit. -/
theorem drop_wakes_iff_frees (r : Room) (h : Inv r) (hheld : r.held = true) :
    r.refs = C - r.commits ↔ (drop r).refs = 0 := by
  have := (h.1 hheld).1
  simp only [drop]; omega

/-- After `Pipeline::drop` (no work in flight, so no credit out), a surviving Room's count is its
unspent credits alone: its drop's assertion (`prev & !ROOM_CLOSING_BIT == unused`) holds. -/
theorem survivor_count (r : Room) (h : Inv r) (hheld : r.held = true) (hidle : r.out = 0) :
    r.refs = C - r.commits := by
  have := (h.1 hheld).1; omega

end Blake3.Credits

#print axioms Blake3.Credits.take_inv
#print axioms Blake3.Credits.commit_inv
#print axioms Blake3.Credits.release_inv
#print axioms Blake3.Credits.drop_inv
#print axioms Blake3.Credits.refs_lt_closing
#print axioms Blake3.Credits.commit_no_wrap
#print axioms Blake3.Credits.release_no_wrap
#print axioms Blake3.Credits.drop_no_wrap
#print axioms Blake3.Credits.commits_fit
#print axioms Blake3.Credits.free_iff
#print axioms Blake3.Credits.drop_wakes_iff_frees
#print axioms Blake3.Credits.survivor_count
