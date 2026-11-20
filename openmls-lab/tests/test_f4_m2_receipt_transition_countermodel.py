"""F4 M2 negative refinement witness: receipt identity is not transition identity.
Finite executable specification only, NOT a claim about native OpenMLS.
"""
import unittest
from dataclasses import dataclass

@dataclass(frozen=True)
class Receipt:
    group: str
    parent: str
    head: str
    epoch: int
    operation: str
    signature_valid: bool

def accept(state, receipt):
    """Fail-closed state transition; signature alone never implies freshness."""
    if not receipt.signature_valid or receipt.group != state["group"]:
        return False
    if receipt.parent != state["head"] or receipt.epoch != state["epoch"] + 1:
        return False
    if receipt.head in state["seen"] or receipt.head == receipt.parent:
        return False
    state["head"], state["epoch"] = receipt.head, receipt.epoch
    state["seen"].add(receipt.head)
    return True

class ReceiptTransitionCountermodel(unittest.TestCase):
    def setUp(self):
        self.state = {"group": "g1", "head": "h0", "epoch": 0, "seen": {"h0"}}

    def test_signed_replay_cannot_advance_twice(self):
        r = Receipt("g1", "h0", "h1", 1, "OWN_UPDATE", True)
        self.assertTrue(accept(self.state, r))
        self.assertFalse(accept(self.state, r))
        self.assertEqual(self.state["epoch"], 1)

    def test_valid_signature_wrong_group_does_not_refine(self):
        r = Receipt("g2", "h0", "h1", 1, "OWN_UPDATE", True)
        self.assertFalse(accept(self.state, r))

    def test_signed_fork_and_rollback_rejected(self):
        self.assertTrue(accept(self.state, Receipt("g1", "h0", "h1", 1, "OWN_UPDATE", True)))
        self.assertFalse(accept(self.state, Receipt("g1", "h0", "fork", 2, "OWN_UPDATE", True)))
        self.assertFalse(accept(self.state, Receipt("g1", "h1", "h0", 2, "OWN_UPDATE", True)))

    def test_unsigned_successor_rejected(self):
        self.assertFalse(accept(self.state, Receipt("g1", "h0", "h1", 1, "OWN_UPDATE", False)))

if __name__ == "__main__":
    unittest.main()
