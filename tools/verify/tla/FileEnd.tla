---- MODULE FileEnd ----
\* b3sum's reads to a file's end (b3sum/src/file_end.rs and its callers),
\* against every answer the kernel may give each read. One file, read one
\* of four ways (`path`):
\*   "warm"    linux_pipe.rs's small and medium files without a ring:
\*             cached_then_plain (a read that may not wait, then waiting
\*             reads), then finish_sync_hash (pread_rest_capped, promoted to
\*             streaming past SMALL_MEM_CAP), or for a descriptor that has no
\*             position, hash_open_file's sequential stream.
\*   "open"    main.rs's hash_open_file_ex for a small file:
\*             read_sequential_capped, promoted to update_from_counted.
\*   "known"   main.rs's read_to_its_end: says + 1 bytes asked first, then
\*             read_to_end (BLAKE3 #424).
\*   "direct"  direct.rs's read: a piece's read must give its bytes exactly,
\*             then one byte more at the size must give 0 (BLAKE3 #424), or
\*             the caller reads the file another way.
\* The file may grow (appends: what #424 was) while it is read; nothing else
\* changes it. A byte is a unit; `at` is how many bytes the reader holds
\* (and, read sequentially, the descriptor's offset).
EXTENDS Integers, FiniteSets

CONSTANTS MaxLen,   \* the most the file grows to
          Cap,      \* SMALL_MEM_CAP: the most a buffer holds before streaming
          Piece,    \* direct.rs's PIECE
          MaxIntr   \* EINTRs in one run (each is retried)

VARIABLES path, seek, hint, dst, len, pc, at, flags, intr, zeroAt, realErr, result

vars == <<path, seek, hint, dst, len, pc, at, flags, intr, zeroAt, realErr, result>>

Min(a, b) == IF a < b THEN a ELSE b
\* A read's answer as the system call gives it: a count, or a failure's errno.
EINTR == -1  ESPIPE == -2  EAGAIN == -3  EIO == -4
Done(kind, n) == result' = [kind |-> kind, n |-> n] /\ pc' = "done"

\* Every answer the kernel may give a read of `want` bytes at `off`: a read
\* that may not wait (RWF_NOWAIT) may give 0 before the end (Linux 5.9 and
\* 5.10) or fail (EAGAIN, EOPNOTSUPP, a sandbox's EPERM, EIO); a waiting
\* read gives 0 only at the end, or fails for real (EIO). A descriptor with
\* no position (a pipe) refuses positioned reads (ESPIPE).
Answers(off, want, nowait, positioned) ==
    LET bytes == IF off < len THEN 1..Min(want, len - off) ELSE {}
        intrs == IF intr < MaxIntr THEN {EINTR} ELSE {}
    IN intrs \cup
       IF positioned /\ ~seek THEN {ESPIPE}
       ELSE IF nowait THEN bytes \cup {0, EAGAIN, EIO}
       ELSE (IF off >= len THEN {0} ELSE bytes) \cup {EIO}

\* What a read's answer says, kept for the properties: where a waiting read
\* gave 0 (the file was that long), and whether one failed for real.
Asked(off, r, nowait) ==
    /\ zeroAt' = IF r = 0 /\ ~nowait THEN zeroAt \cup {off} ELSE zeroAt
    /\ realErr' = (realErr \/ (r = EIO /\ ~nowait))
    /\ intr' = IF r = EINTR THEN intr + 1 ELSE intr

Init == /\ path \in {"warm", "open", "known", "direct"}
        /\ seek \in BOOLEAN
        /\ hint \in 0..MaxLen        \* the size fstat said
        /\ len = hint
        /\ dst \in 1..Cap            \* the warm path's slot or buffer
        /\ pc = CASE path = "warm" -> "probe" [] path = "open" -> "seqcap"
                  [] path = "known" -> "known" [] path = "direct" -> "piece"
        /\ (path = "direct") => (seek /\ hint > Piece)
        /\ at = 0 /\ flags = "nowait" /\ intr = 0
        /\ zeroAt = {} /\ realErr = FALSE
        /\ result = [kind |-> "none", n |-> 0]

Append == /\ pc # "done" /\ len < MaxLen /\ len' = len + 1
          /\ UNCHANGED <<path, seek, hint, dst, pc, at, flags, intr, zeroAt, realErr, result>>

\* cached_then_plain: the first read asks the page cache alone.
Probe == /\ pc = "probe"
         /\ IF at = dst
            THEN /\ pc' = "rest"                      \* NeedMore(at)
                 /\ UNCHANGED <<at, flags, intr, zeroAt, realErr, result>>
            ELSE \E r \in Answers(at, dst - at, flags = "nowait", TRUE):
                 /\ Asked(at, r, flags = "nowait")
                 /\ CASE r = EINTR -> UNCHANGED <<pc, at, flags, result>>
                      [] r = ESPIPE -> /\ pc' = (IF at = 0 THEN "seqstream" ELSE "rest")
                                         /\ UNCHANGED <<at, flags, result>>
                      [] r \in {EAGAIN, EIO} ->
                            IF flags = "nowait" THEN /\ pc' = "rest"  \* NeedMore(at)
                                                     /\ UNCHANGED <<at, flags, result>>
                            ELSE Done("err", 0) /\ UNCHANGED <<at, flags>>
                      [] r = 0 ->
                            IF flags = "wait" THEN Done("hash", at) /\ UNCHANGED <<at, flags>>
                            ELSE flags' = "wait" /\ UNCHANGED <<pc, at, result>>
                      [] OTHER -> at' = at + r /\ flags' = "wait" /\ UNCHANGED <<pc, result>>
         /\ UNCHANGED <<path, seek, hint, dst, len>>

\* pread_rest_capped: waiting positioned reads up to Cap, then streaming.
Rest == /\ pc = "rest"
        /\ IF at >= Cap
           THEN /\ pc' = "posstream"
                /\ UNCHANGED <<at, intr, zeroAt, realErr, result>>
           ELSE \E r \in Answers(at, Cap - at, FALSE, TRUE):
                /\ Asked(at, r, FALSE)
                /\ CASE r = EINTR -> UNCHANGED <<pc, at, result>>
                     [] r = ESPIPE -> IF at = 0 THEN pc' = "seqcap" /\ UNCHANGED <<at, result>>
                                        ELSE Done("err", 0) /\ UNCHANGED at
                     [] r = EIO -> Done("err", 0) /\ UNCHANGED at
                     [] r = 0 -> Done("hash", at) /\ UNCHANGED at
                     [] OTHER -> at' = at + r /\ UNCHANGED <<pc, result>>
        /\ UNCHANGED <<path, seek, hint, dst, len, flags>>

\* read_sequential_capped: waiting reads up to Cap, then streaming.
SeqCap == /\ pc = "seqcap"
          /\ IF at >= Cap
             THEN /\ pc' = "seqstream"
                  /\ UNCHANGED <<at, intr, zeroAt, realErr, result>>
             ELSE \E r \in Answers(at, Cap - at, FALSE, FALSE):
                  /\ Asked(at, r, FALSE)
                  /\ CASE r = EINTR -> UNCHANGED <<pc, at, result>>
                       [] r = EIO -> Done("err", 0) /\ UNCHANGED at
                       [] r = 0 -> Done("hash", at) /\ UNCHANGED at
                       [] OTHER -> at' = at + r /\ UNCHANGED <<pc, result>>
          /\ UNCHANGED <<path, seek, hint, dst, len, flags>>

\* finish_hash_streaming_from_prefix and update_from_counted (fill): reads,
\* positioned (PreadReader) or not, to a read that gives 0. Bytes streamed
\* are hashed as they come, so no buffer holds them.
Stream == /\ pc \in {"posstream", "seqstream"}
          /\ \E r \in Answers(at, MaxLen, FALSE, pc = "posstream"):
             /\ Asked(at, r, FALSE)
             /\ CASE r = EINTR -> UNCHANGED <<pc, at, result>>
                  [] r \in {EIO, ESPIPE} -> Done("err", 0) /\ UNCHANGED at
                  [] r = 0 -> Done("hash", at) /\ UNCHANGED at
                  [] OTHER -> at' = at + r /\ UNCHANGED <<pc, result>>
          /\ UNCHANGED <<path, seek, hint, dst, len, flags>>

\* read_to_its_end: says + 1 bytes asked; a positive short read is not the end.
Known == /\ pc = "known"
         /\ IF at > hint
            THEN /\ pc' = "seqstream"                 \* read_to_end
                 /\ UNCHANGED <<at, intr, zeroAt, realErr, result>>
            ELSE \E r \in Answers(at, hint + 1 - at, FALSE, FALSE):
                 /\ Asked(at, r, FALSE)
                 /\ CASE r = EINTR -> UNCHANGED <<pc, at, result>>
                      [] r = EIO -> Done("err", 0) /\ UNCHANGED at
                      [] r = 0 -> Done("hash", at) /\ UNCHANGED at
                      [] OTHER -> at' = at + r /\ UNCHANGED <<pc, result>>
         /\ UNCHANGED <<path, seek, hint, dst, len, flags>>

\* direct.rs's read: each piece asks PIECE bytes at its start and must get
\* exactly its share of the size (an EINTR or a failure is a short read);
\* else None, and the caller reads the file another way ("fallback").
DirectPiece == /\ pc = "piece"
               /\ IF at >= hint
                  THEN /\ pc' = "more"
                       /\ UNCHANGED <<at, intr, zeroAt, realErr, result>>
                  ELSE \E r \in Answers(at, Piece, FALSE, TRUE):
                       /\ Asked(at, r, FALSE)
                       /\ IF r = Min(Piece, hint - at)
                          THEN at' = at + r /\ UNCHANGED <<pc, result>>
                          ELSE Done("fallback", 0) /\ UNCHANGED at
               /\ UNCHANGED <<path, seek, hint, dst, len, flags>>

\* One byte more, at the size: only a 0 says the file ends there.
DirectMore == /\ pc = "more"
              /\ \E r \in Answers(hint, 1, FALSE, TRUE):
                 /\ Asked(hint, r, FALSE)
                 /\ CASE r = EINTR -> UNCHANGED <<pc, result>>
                      [] r = 0 -> Done("hash", hint)
                      [] OTHER -> Done("fallback", 0)
              /\ UNCHANGED <<path, seek, hint, dst, len, flags, at>>

Next == Append \/ Probe \/ Rest \/ SeqCap \/ Stream \/ Known \/ DirectPiece \/ DirectMore

Spec == Init /\ [][Next]_vars /\ WF_vars(Probe \/ Rest \/ SeqCap \/ Stream \/ Known \/ DirectPiece \/ DirectMore)

\* A hash is of a whole file: of as many bytes as a waiting read, asked at
\* that offset, found the file to have (only a waiting read's 0 ends a file).
EndsAtZero == result.kind = "hash" => result.n \in zeroAt

\* No error is swallowed: after a waiting read fails for real, no hash.
NoSwallow == realErr => result.kind # "hash"

\* No false error: b3sum fails only where a waiting read failed for real
\* (not for a probe the page cache refused, nor for an EINTR).
NoFalseError == result.kind = "err" => realErr

\* A buffer holds at most Cap bytes before the read is promoted to streaming
\* (a file that said it was small, or grows, cannot exhaust memory).
Bounded == pc \in {"probe", "rest", "seqcap"} => at <= Cap

\* Every read ends: a hash, an error, or (direct) the other way.
Ends == <>(pc = "done")
====
