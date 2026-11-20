"""Check ordered acceptance gates in the ordinary compiled Product snapshot selector."""
import argparse
import hashlib
from pathlib import Path
import re
import subprocess

from verify_remove_gate import reachable

PIN = "817bf698d3e186c132779196de787c7b1a076b14cacd89a16c0fc086293662ac"
# Each gate must be crossed even to arrive at the next gate's source.
CHAIN = [(13, 14), (20, 21), (24, 25), (27, 28), (30, 31)]
SUCCESS = 63
REJECT = 44


def extract(path):
    matches = re.findall(r"^fn offline_product::match_native_snapshot\([^\n]+\{\n.*?^}", path.read_text(), re.M | re.S)
    if len(matches) != 1 or hashlib.sha256(matches[0].encode()).hexdigest() != PIN:
        raise ValueError("different or ambiguous snapshot selector")
    parts = re.findall(r"^    bb(\d+)(?: \(cleanup\))?: \{\n(.*?)^    \}", matches[0], re.M | re.S)
    blocks = {int(i): body.strip() for i, body in parts}
    if len(parts) != len(blocks) or set(blocks) != set(range(max(blocks) + 1)):
        raise ValueError("incomplete block list")
    patterns = {13: "MlsGroup::load::<", 21: "_20 = move _38;", 23: "MlsGroup::is_active",
                24: "[0: bb44, otherwise: bb25]", 25: "MlsGroup::pending_commit",
                26: "::is_some", 27: "[0: bb28, otherwise: bb44]", 28: "MlsGroup::epoch",
                29: "GroupEpoch::as_u64", 30: "Ne(move _46, move _50);",
                44: "product_current_private_member_epoch", 63: "_92 = move _20;"}
    if any(s not in blocks[i] for i, s in patterns.items()):
        raise ValueError("selector changed")
    ok = [i for i, b in blocks.items() if re.search(r"_0 = .*::Ok\(", b)]
    if ok != [SUCCESS]:
        raise ValueError("unexpected Ok construction")
    edges = []
    for i, b in blocks.items():
        term = b.splitlines()[-1].strip()
        dest = list(map(int, re.findall(r"\bbb(\d+)\b", term)))
        if (not dest and term not in {"return;", "resume;", "unreachable;"}) or set(dest) - blocks.keys():
            raise ValueError((i, term))
        edges.extend((i, j) for j in dest)
    return edges


PRELUDE = """
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
abbrev Edge := Nat × Nat
inductive PathAvoid (es : List Edge) (skip : List Edge) (s : Nat) : Nat → Prop
  | start : PathAvoid es skip s s
  | step {a b} : PathAvoid es skip s a → (a,b) ∈ es → (a,b) ∉ skip → PathAvoid es skip s b

theorem cut {es skip : List Edge} {s t : Nat} (inside : List Nat)
    (seed : s ∈ inside) (out : t ∉ inside)
    (closed : ∀ e ∈ es, e.1 ∈ inside → e ∉ skip → e.2 ∈ inside) :
    ¬ PathAvoid es skip s t := by
  intro h
  apply out
  clear out
  induction h with
  | start => exact seed
  | step _ edge avoid ih => exact closed _ edge ih avoid
"""


def program(edges, specs):
    src = PRELUDE + f"\ndef cfg : List Edge := {edges}\n"
    for name, start, end, gate, inside in specs:
        skip = [] if gate is None else [gate]
        src += f"""theorem {name} : ¬ PathAvoid cfg {skip} {start} {end} := by
  apply cut {inside} (by decide) (by decide)
  have certified : cfg.all (fun e => decide (e.1 ∈ {inside} → e ∉ ({skip} : List Edge) → e.2 ∈ {inside})) = true := by decide
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp certified e he)
#print axioms {name}
"""
    return src


def run(mir, out, lean):
    edges = extract(mir)
    if SUCCESS not in reachable(edges, 0) or REJECT not in reachable(edges, 0):
        raise ValueError("vacuous selector graph")
    specs = []
    for i, gate in enumerate(CHAIN):
        end = CHAIN[i + 1][0] if i + 1 < len(CHAIN) else SUCCESS
        specs.append((f"gate_{i}", 0, end, gate, reachable(edges, 0, gate)))
    specs.append(("rejection_cannot_accept", REJECT, SUCCESS, None, reachable(edges, REJECT)))
    path = out / "SnapshotCuts.lean"

    def verify(graph, certificates):
        path.write_text(program(graph, certificates), encoding="utf-8")
        return subprocess.run([lean, str(path)], capture_output=True, text=True)

    good = verify(edges, specs)
    if good.returncode or "sorryAx" in good.stdout:
        raise ValueError(good.stdout + good.stderr)
    print(good.stdout.strip())
    # Give each rejected predicate a route to success in turn, independently of the MIR hash.
    for i in (2, 3, 4):
        name, start, end, gate, inside = specs[i]
        source, _ = gate
        bad = verify(edges + [(source, end)], [specs[i]])
        if bad.returncode == 0 or "decide" not in bad.stdout + bad.stderr:
            raise ValueError(f"mutation at {name} escaped or checker failed unexpectedly")
    path.write_text(program(edges, specs), encoding="utf-8")
    print(f"SNAPSHOT_SELECTOR: {len(edges)} MIR edges, 6 kernel cuts, 3 bypass controls rejected")


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("mir", type=Path)
    p.add_argument("out", type=Path)
    p.add_argument("--lean", default="lean")
    args = p.parse_args()
    run(args.mir, args.out, args.lean)
