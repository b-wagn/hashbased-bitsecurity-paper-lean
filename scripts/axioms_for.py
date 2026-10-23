"""Append kernel-generated, #guard_msgs-guarded #print axioms entries for the public theorems
of the given Lean files to SlhDsaSecurity/Proof/Axioms.lean, and add the module imports.

Usage (from the repo root, after building the modules):
    python3 scripts/axioms_for.py SlhDsaSecurity/Proof/Foo.lean [...]

The expected text of each guard is what `lake env lean` prints for the `#print axioms` line,
never written by hand.
"""
import os, re, subprocess, sys, tempfile

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:protected\s+|nonrec\s+)?(?:theorem|lemma)\s+([^\s:({\[]+)")
AX = "SlhDsaSecurity/Proof/Axioms.lean"


def names(path):
    out, stack, depth = [], [], 0
    for line in open(path).read().splitlines():
        opens, closes = line.count("/-"), line.count("-/")
        was = depth > 0
        depth = max(0, depth + opens - closes)
        if was or opens:
            continue
        if line.startswith("private"):
            continue
        m = re.match(r"namespace (\S+)\s*$", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"end (\S+)\s*$", line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        m = DECL.match(line)
        if m:
            out.append(".".join(stack + [m.group(1)]))
    return out


def main():
    files = sys.argv[1:]
    mods = [f[:-5].replace("/", ".") for f in files]
    allnames = [n for f in files for n in names(f)]
    ax = open(AX).read()
    covered = set(re.findall(r"#print axioms (\S+)", ax))
    todo = [n for n in allnames if n not in covered]
    if not todo:
        print("nothing to add")
        return
    src = "".join(f"import {m}\n" for m in mods) + "".join(f"#print axioms {n}\n" for n in todo)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=".") as t:
        t.write(src)
        tmp = t.name
    try:
        res = subprocess.run(["lake", "env", "lean", tmp], capture_output=True, text=True)
    finally:
        os.unlink(tmp)
    out = res.stdout + res.stderr
    msgs = {}
    for m in re.finditer(r"(?m)^'(.+?)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)",
                         out):
        msgs[m.group(1)] = m.group(0)
    missing = [n for n in todo if n not in msgs]
    if missing:
        print("no kernel output for:", missing)
        print(out[:3000])
        sys.exit(1)
    for m in mods:
        line = f"import {m}\n"
        if line not in ax:
            idx = max(i for i, l in enumerate(ax.splitlines(True)) if l.startswith("import "))
            lines = ax.splitlines(True)
            lines.insert(idx + 1, line)
            ax = "".join(lines)
    entries = "".join(f"\n/--\ninfo: {msgs[n]}\n-/\n#guard_msgs in\n#print axioms {n}\n" for n in todo)
    ax = ax.rstrip("\n") + "\n" + entries
    open(AX, "w").write(ax)
    print(f"added {len(todo)} entries")


if __name__ == "__main__":
    main()
