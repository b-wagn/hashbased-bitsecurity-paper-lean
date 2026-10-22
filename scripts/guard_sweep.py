"""Fail if any public theorem lacks a #guard_msgs-guarded #print axioms entry.

Run from the repository root. Exits 1 and prints the names when coverage has
decayed, 0 and prints the count when it has not.

Two things make this worth running rather than a grep. It tracks `namespace`
and `end` with a stack, so a name is the name the kernel knows; and it skips
block comments, so a docstring line beginning "lemma to ..." is prose rather
than a declaration. A sweep without those reports hundreds of false positives,
which is worse than no sweep at all -- nobody reads the output twice.

What it cannot see is recorded in REVIEW.md section 7: a declaration indented
inside a `section`, and one named by a macro.
"""
import os
import re
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else "."
DIRS = ["SlhDsaSecurity/Proof", "SlhDsaSecurity/Statement"]
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+|nonrec\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)")

axioms = open(os.path.join(ROOT, "SlhDsaSecurity/Proof/Axioms.lean")).read()
covered = set(re.findall(r"#print axioms (\S+)", axioms))

uncovered = []
for directory in DIRS:
    full = os.path.join(ROOT, directory)
    if not os.path.isdir(full):
        continue
    for name in sorted(os.listdir(full)):
        if not name.endswith(".lean") or name == "Axioms.lean":
            continue
        path = os.path.join(directory, name)
        stack = []
        depth = 0           # block-comment nesting
        for line in open(os.path.join(ROOT, path)).read().splitlines():
            opens = line.count("/-")
            closes = line.count("-/")
            was_in_comment = depth > 0
            depth = max(0, depth + opens - closes)
            if was_in_comment or opens:
                continue
            if line.startswith("private"):
                continue
            match = re.match(r"namespace (\S+)\s*$", line)
            if match:
                stack.append(match.group(1))
                continue
            match = re.match(r"end (\S+)\s*$", line)
            if match and stack and stack[-1] == match.group(1):
                stack.pop()
                continue
            match = DECL.match(line)
            if match:
                full_name = ".".join(stack + [match.group(1)])
                if full_name not in covered:
                    uncovered.append((path, full_name))

if uncovered:
    print("GUARD COVERAGE REGRESSED: %d theorem(s) without a #print axioms entry"
          % len(uncovered))
    for path, full_name in uncovered:
        print("  %s  %s" % (path, full_name))
    print("Add them with add_axioms.py, generated from kernel output, never by hand.")
    sys.exit(1)

print("guard sweep: %d guards, 0 uncovered" % len(covered))
