#!/usr/bin/env python3
"""tools/audit.py's verdicts: a failure, a hang and a missing tool each show, and none reads as a pass."""
import io
import os
import tempfile
import time
import unittest

import audit


def verdict(*checks):
    with tempfile.TemporaryDirectory() as logs:
        status = audit.run(list(checks), logs, out=io.StringIO())
        with open(os.path.join(logs, "report.md")) as f:
            return status, f.read()


class Verdicts(unittest.TestCase):
    def test_every_check_passing_exits_0(self):
        status, report = verdict(audit.check("ok", "L", "true"))
        self.assertEqual(status, 0)
        self.assertIn("| `ok` | L | PASS |", report)

    def test_a_failure_exits_1_and_later_checks_still_run(self):
        status, report = verdict(audit.check("bad", "L", "exit 7"), audit.check("ok", "L", "true"))
        self.assertEqual(status, 1)
        self.assertIn("| `bad` | L | FAIL |", report)
        self.assertIn("exit 7", report)
        self.assertIn("| `ok` | L | PASS |", report)

    def test_a_missing_tool_is_skipped_and_exits_3_without_running(self):
        with tempfile.TemporaryDirectory() as d:
            mark = os.path.join(d, "ran")
            status, report = verdict(audit.check("needs", "L", f"touch {mark}", ["cmd:no-such-program-audit"]))
            self.assertFalse(os.path.exists(mark))
        self.assertEqual(status, 3)
        self.assertIn("SKIPPED", report)
        self.assertIn("no `no-such-program-audit` on PATH", report)

    def test_a_failure_outranks_a_skip(self):
        status, _ = verdict(audit.check("needs", "L", "true", ["py:no_such_module_audit"]),
                            audit.check("bad", "L", "false"))
        self.assertEqual(status, 1)

    def test_a_hang_is_stopped_with_what_it_started(self):
        with tempfile.TemporaryDirectory() as d:
            pid = os.path.join(d, "pid")
            status, report = verdict(audit.check("hang", "L", f"(sleep 300 & echo $! > {pid}; wait)", minutes=0.02))
            with open(pid) as f:
                child = int(f.read())
        self.assertEqual(status, 1)
        self.assertIn("TIMEOUT", report)
        for _ in range(50):  # the kill is sent before run() returns; the kernel reaps soon after
            try:
                os.kill(child, 0)
            except ProcessLookupError:
                break
            time.sleep(0.1)
        else:
            self.fail("the hung check's child is still running")

    def test_wrong_cpu_and_small_memory_name_what_is_needed(self):
        self.assertIn("needs a no-such-cpu CPU", audit.missing("arch:no-such-cpu"))
        self.assertIn("needs 1000000 GB", audit.missing("mem:1000000"))
        self.assertIsNone(audit.missing("mem:0"))
        self.assertIn("rustup target add no-such-target", audit.missing("target:no-such-target"))

    def test_every_listed_check_has_a_unique_name_and_known_needs(self):
        names = [c["name"] for c in audit.CHECKS]
        self.assertEqual(len(names), len(set(names)))
        for c in audit.CHECKS:
            for need in c["needs"]:
                audit.missing(need)  # raises on an unknown kind


if __name__ == "__main__":
    unittest.main()
