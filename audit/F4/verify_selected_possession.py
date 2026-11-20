"""Run the kernel proof and require each mutation to fail in its intended theorem."""
from pathlib import Path
import re
import subprocess
import sys


def main(out):
    original = Path(__file__).with_name("SelectedPossession.lean")
    source = original.read_text(encoding="utf-8")
    report = subprocess.run(["lean", str(original)], capture_output=True, text=True)
    output = report.stdout + report.stderr
    if report.returncode or "sorry" in output or output.count("depends on axioms: [propext]") != 4:
        raise ValueError(output)
    print(output.strip())
    mutations = [
        ("forget-at-rollback", "  | none => held", "  | none => if q = .rollbackProbe then [] else held", "one"),
        ("grant-on-refusal", "  | _ => none", "  | .atPeer k false => some ⟨peer,k⟩\n  | _ => none", "one"),
        ("require-same-device", "∧ s.groupId = r.groupId", "∧ s.groupId = r.groupId ∧ s.device = r.device", "cross_device_witness"),
    ]
    for label, old, new, theorem in mutations:
        if source.count(old) != 1:
            raise ValueError(label)
        variant = source.replace(old, new)
        path = out / f"{label}.lean"
        path.write_text(variant, encoding="utf-8")
        ran = subprocess.run(["lean", str(path)], capture_output=True, text=True)
        errors = [int(x) for x in re.findall(r":(\d+):\d+: error:", ran.stdout + ran.stderr)]
        decl = variant.index("theorem " + theorem)
        start = variant[:decl].count("\n") + 1
        stop = variant.index("\n\n", decl)
        end = variant[:stop].count("\n") + 1
        if not ran.returncode or not errors or not start <= errors[0] <= end:
            raise ValueError((label, ran.stdout + ran.stderr))
        print(f"REJECTED={label} at {theorem}")


if __name__ == "__main__":
    main(Path(sys.argv[1]))
