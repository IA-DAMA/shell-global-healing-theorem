"""Project every basic-block target of the pinned replacement MIR and check a Lean certificate."""
import argparse
import hashlib
from pathlib import Path
import re
import subprocess

PIN = "a369180f81d358ed4de884ab8a271db8a46729ebd846f4f71ed3272c091afebd"
GATE = (87, 88)
TARGET = 90


def graph(path):
    text = path.read_text(encoding="utf-8")
    matches = re.findall(r"^fn replacement::complete\([^\n]+\{\n.*?^}", text, re.M | re.S)
    if len(matches) != 1 or hashlib.sha256(matches[0].encode()).hexdigest() != PIN:
        raise ValueError("MIR function missing, ambiguous or different from the reviewed input")
    parts = re.findall(r"^    bb(\d+)(?: \(cleanup\))?: \{\n(.*?)^    \}", matches[0], re.M | re.S)
    blocks = {int(i): body.strip().splitlines()[-1] for i, body in parts}
    if len(blocks) != len(parts) or set(blocks) != set(range(max(blocks) + 1)):
        raise ValueError("incomplete basic block list")
    for i, pattern in {85: "transaction::<", 86: "as Try>::branch(move _140)",
                       87: "[0: bb88, 1: bb89, otherwise: bb3]", 90: "offline_product::catch_up::<"}.items():
        if pattern not in blocks[i]:
            raise ValueError(("boundary differs", i))
    edges = [(i, int(k)) for i, term in blocks.items() for k in re.findall(r"\bbb(\d+)\b", term)]
    for i, term in blocks.items():
        if not any(a == i for a, _ in edges) and term not in ("return;", "resume;", "unreachable;"):
            raise ValueError(("unknown terminal", i, term))
    if any(k not in blocks for _, k in edges):
        raise ValueError("bad destination")
    return edges


def reachable(edges, start, forbidden=None):
    reached = {start}
    while True:
        new = {k for a, k in edges if a in reached and (a, k) != forbidden} - reached
        if not new:
            return sorted(reached)
        reached |= new


def literals(edges, cut):
    return ("def edges : List (Nat × Nat) := [" + ",".join(f"({a},{b})" for a, b in edges)
            + "]\ndef cut : List Nat := " + str(cut) + "\n")


PROOF = """
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
inductive Before : Nat → Prop
  | start : Before 0
  | step {a b : Nat} : Before a → (a,b) ∈ edges → (a,b) ≠ (87,88) → Before b
theorem closed_cut :
    edges.all (fun e => decide (e.1 ∉ cut ∨ e = (87,88) ∨ e.2 ∈ cut)) = true := by decide
theorem inductive_cut {n : Nat} (h : Before n) : n ∈ cut := by
  induction h with
  | start => decide
  | @step a b _ edge avoid ih =>
    have h := List.all_eq_true.mp closed_cut (a,b) edge
    simp only [decide_eq_true_eq] at h
    exact (h.resolve_left (fun f => f ih)).resolve_left avoid
theorem join_requires_continue : ¬ Before 90 := by
  intro h
  exact (by decide : 90 ∉ cut) (inductive_cut h)
#print axioms join_requires_continue
"""


def run(mir, out, lean):
    edges = graph(mir)
    cut = reachable(edges, 0, GATE)
    if TARGET not in reachable(edges, 0) or TARGET in cut or 89 not in cut:
        raise ValueError("dead target or ineffective cut")
    path = out / "ReplacementCut.lean"
    path.write_text(literals(edges, cut) + PROOF, encoding="utf-8")
    good = subprocess.run([lean, str(path)], capture_output=True, text=True)
    report = good.stdout + good.stderr
    foundations = ("does not depend on any axioms", "depends on axioms: [propext, Quot.sound]")
    if good.returncode or not any(report.strip().endswith(ok) for ok in foundations):
        raise ValueError(report)
    print(report.strip())
    # Negative: let the error branch enter JOIN, with the same certificate.
    path = out / "WrongEdge.lean"
    path.write_text(literals(edges + [(89, TARGET)], cut) + PROOF, encoding="utf-8")
    bad = subprocess.run([lean, str(path)], capture_output=True, text=True)
    if bad.returncode == 0 or "decide" not in bad.stdout + bad.stderr:
        raise ValueError("mutation did not invalidate the finite kernel certificate")
    print(f"{len(edges)} MIR edges (including cleanup); altered error edge rejected")


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("mir", type=Path)
    p.add_argument("out", type=Path)
    p.add_argument("--lean", default="lean")
    a = p.parse_args()
    run(a.mir, a.out, a.lean)
