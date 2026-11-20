"""Finite two-holder lifecycle model. Public tokens only; this is not a Rust extractor."""
import argparse
from collections import deque
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import tempfile

# Each item refers to the same fixed synthetic generation. The old snapshot
# and blobs for other generations do not contribute material for this target.
EVENTS = ("old_capture", "prepare", "apply", "snapshot", "welcome", "resync",
          "remove_error", "crash", "restart", "retry", "copy_device", "grant")
OLD, BLOB, KEY, READABLE = 1, 2, 4, 8


@dataclass(frozen=True)
class Physical:
    disk: int = 0
    live: int = 0
    peer: int = 0
    view: int = 0
    online: bool = True


def advance(s, op):
    d, v, p, a, up = s.disk, s.live, s.peer, s.view, s.online
    if op == "restart":
        return Physical(d, 0, p, a, True) if not up else s
    if op == "crash":
        return Physical(d, 0, p, a, False)
    if op == "copy_device":
        return Physical(d, v, p, a | p, up)
    if not up:
        return s
    if op == "old_capture":
        a |= OLD
    elif op == "prepare":
        v |= BLOB
    elif op == "apply" or op == "remove_error":
        d |= v
    elif op == "snapshot":
        a |= d
    elif op == "welcome":
        p |= BLOB
    elif op == "grant":
        p |= KEY
    elif op == "resync" or op == "retry":
        if (a & (BLOB | KEY)) == (BLOB | KEY):
            a |= READABLE
    return Physical(d, v, p, a, up)


# A separate provenance interpreter records individual acquisitions and
# edges between holders, not the source's bit-mask operations.
def record(g, op, omit=None):
    disk, live, peer, seen, up = g
    if op == omit:
        return g
    if op == "crash":
        return disk, frozenset(), peer, seen, False
    if op == "restart":
        return disk, live if up else frozenset(), peer, seen, True
    if op == "copy_device":
        return disk, live, peer, seen | peer, up
    if not up:
        return g
    if op == "old_capture":
        seen |= {"old"}
    if op == "prepare":
        live |= {"blob"}
    if op in ("apply", "remove_error"):
        disk |= live
    if op == "snapshot":
        seen |= disk
    if op == "welcome":
        peer |= {"blob"}
    if op == "grant":
        peer |= {"key"}
    if op in ("resync", "retry") and {"blob", "key"} <= seen:
        seen |= {"output"}
    return disk, live, peer, seen, up


NAMES = ((OLD, "old"), (BLOB, "blob"), (KEY, "key"), (READABLE, "output"))
EMPTY = frozenset()
INITIAL = (EMPTY, EMPTY, EMPTY, EMPTY, True)


def expected(s):
    return tuple(frozenset(name for bit, name in NAMES if mask & bit)
                 for mask in (s.disk, s.live, s.peer, s.view)) + (s.online,)


def search(omit=None):
    initial = (Physical(), INITIAL)
    todo = deque([(initial, ())])
    visited = {initial}
    while todo:
        (s, g), path = todo.popleft()
        if expected(s) != g:
            return len(visited), path
        for op in EVENTS:
            nxt = advance(s, op), record(g, op, omit)
            if nxt not in visited:
                visited.add(nxt)
                todo.append((nxt, path + (op,)))
    return len(visited), None


def positive():
    count, mismatch = search()
    if mismatch is not None:
        raise ValueError(mismatch)
    print(f"CC finite paired model: {count} reachable state pairs; no mismatch")
    for op in EVENTS:
        _, path = search(omit=op)
        if path is None:
            raise ValueError(("insensitive to omission", op))
        print("omitted", op, "=>", ",".join(path))
    s = Physical()
    history = ["old_capture", "prepare", "remove_error", "crash", "restart"]
    for op in history:
        s = advance(s, op)
    selected = bool(s.online and s.disk & BLOB and s.view == OLD)
    if not selected:
        raise ValueError("positive selection missing")
    # First adapt to the observed restart, then to the two acquired pieces.
    s = advance(s, "snapshot" if selected else "old_capture")
    if s.view & BLOB:
        s = advance(advance(s, "grant"), "copy_device")
    if advance(s, "retry").view & READABLE == 0:
        raise ValueError("lost joint provenance")
    print("Model prefix admitted after old capture; later joint grant makes this target ineligible.")


def negative(ec_dir):
    file = "F4_CC_Observation_Prefix.ec"
    original = (ec_dir / file).read_text()
    start = original.index("op record (")
    end = original.index("lemma zero_rel", start)
    clauses = original[start:end]
    for arm in re.finditer(r"(?m)^(  with opn=(\w+) => )[^\n]*", clauses):
        op = arm[2]
        replacement = arm[1] + "g" + ("." if op == "Retry" else "")
        mutated = original[:start + arm.start()] + replacement + original[start + arm.end():]
        lemma = "lemma cc_" + op.lower()
        proof_line = mutated[:mutated.index(lemma)].count("\n") + 2
        with tempfile.TemporaryDirectory() as folder:
            target = Path(folder) / file
            target.write_text(mutated)
            proc = subprocess.run(["easycrypt", "llm", "-lastgoals", file], cwd=folder,
                                  capture_output=True, text=True, timeout=75)
        out = proc.stderr + proc.stdout
        if proc.returncode == 0 or f"[critical] [{file}: line {proof_line} " not in out:
            raise ValueError(("unexpected mutation result", op, out[-500:]))
        print(f"REJECTED={op} at {lemma}")
    if len(list(re.finditer(r"(?m)^  with opn=", clauses))) != len(EVENTS):
        raise ValueError("untested ledger arm")
    savepoint = "F4_CC_Savepoint.ec"
    source = (ec_dir / savepoint).read_text()
    old = "db=s.`saved;open_tx=false"
    if source.count(old) != 1:
        raise ValueError("ambiguous rollback arm")
    with tempfile.TemporaryDirectory() as folder:
        (Path(folder) / savepoint).write_text(source.replace(old, "db=s.`saved;ram=false;open_tx=false"))
        proc = subprocess.run(["easycrypt", "llm", "-lastgoals", savepoint], cwd=folder,
                              capture_output=True, text=True, timeout=75)
    proof_line = source[:source.index("  by move: early late;")].count("\n") + 1
    if proc.returncode == 0 or f"[critical] [{savepoint}: line {proof_line} " not in proc.stdout + proc.stderr:
        raise ValueError(("wrong savepoint mutation failure", (proc.stdout + proc.stderr)[-600:]))
    print("REJECTED=rollback-erases-memory at store_only_impossible")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--negative", type=Path)
    args = ap.parse_args()
    if args.negative is None:
        positive()
    else:
        negative(args.negative)
