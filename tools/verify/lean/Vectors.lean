import Blake3

/-! `test_vectors/lean_vectors.json`: the definition's own outputs (`c2sp/BLAKE3/Blake3.lean`), in
the official test vectors' format, for the library's tests to compare its calls against.

    lake build vectors && .lake/build/bin/vectors ../../../test_vectors/lean_vectors.json

The official vectors (`test_vectors/test_vectors.json`) are official BLAKE3's outputs at 35 input
lengths. These are the definition's, at the lengths `lengths` lists: either side of each block
boundary in the first chunk, of every chunk count up to 17 (each kernel's lanes), and of every power
of two from 32 to 4096 chunks (the `Hasher`'s rows, the batch tables, and the pool's pieces and
split). The input, key and context are the official vectors': byte i of the input is i % 251. -/

open Blake3

def hexByte (b : UInt8) : String :=
  let d := "0123456789abcdef".toList
  s!"{d[b.toNat / 16]!}{d[b.toNat % 16]!}"

def hex (b : ByteArray) : String := String.join (b.toList.map hexByte)

def key : String := "whats the Elvish word for friend"
def context : String := "BLAKE3 2019-12-27 16:29:52 test vectors context"

/-- Chunk counts: each to 17, and either side of each power of two from 32 to 4096. -/
def chunkCounts : List Nat :=
  (List.range 16).map (· + 2) ++ ((List.range 8).map fun k => 2 ^ (k + 5)).flatMap fun p => [p - 1, p, p + 1]

def lengths : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 63, 64, 65, 127, 128, 129, 1023, 1024, 1025] ++
    chunkCounts.flatMap fun c => [1024 * c - 1, 1024 * c, 1024 * c + 1]

/-- Output bytes: 33 blocks and 3 bytes for roots of each kind (a single block, a chunk's last
block, a parent), past the 32 blocks one wide extended-output call computes; otherwise the official
vectors' 131, two blocks and 3 bytes. -/
def outLen (n : Nat) : Nat :=
  if [0, 1, 64, 65, 1024, 1025, 2048, 2049].contains n then 64 * 33 + 3 else 64 * 2 + 3

def comment : String :=
  "The outputs of the Lean definition of BLAKE3 (c2sp/BLAKE3/Blake3.lean), written by " ++
  "tools/verify/lean/Vectors.lean, in the format of test_vectors.json: the same input pattern " ++
  "(byte i is i % 251), key and context string. Do not edit: regenerate it."

def case (n : Nat) : String :=
  let input : ByteArray := ⟨(Array.range n).map fun i => (i % 251).toUInt8⟩
  let out := outLen n
  s!"    \{\n      \"input_len\": {n},\n      \"hash\": \"{hex (Blake3.hash input out)}\",\n" ++
  s!"      \"keyed_hash\": \"{hex (keyed_hash key.toUTF8 input out)}\",\n" ++
  s!"      \"derive_key\": \"{hex (derive_key context.toUTF8 input out)}\"\n    }"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (.userError "usage: vectors OUT.json")
  let head := s!"\{\n  \"_comment\": \"{comment}\",\n  \"key\": \"{key}\",\n  \"context_string\": \"{context}\",\n"
  IO.FS.writeFile path (head ++ "  \"cases\": [\n" ++ ",\n".intercalate (lengths.map case) ++ "\n  ]\n}\n")
  IO.println s!"vectors: {lengths.length} cases, input lengths up to {lengths.getLast!} bytes, written to {path}"
