"""Finite countermodel: signed successor metadata cannot attest native acceptance.
NOT a Product/OpenMLS refinement proof.
"""
from dataclasses import dataclass
import unittest

@dataclass(frozen=True)
class Event:
    signed: bool
    parent: str
    head: str
    epoch: int
    native_applied: bool
    stored: bool
    operation: str

def metadata_only(s, e):
    return e.signed and e.parent == s[0] and e.epoch == s[1] + 1 and e.head != e.parent

def strict_step(s, e):
    if not metadata_only(s, e) or not e.native_applied or not e.stored:
        return s
    return (e.head, e.epoch)

class NativeAcceptanceGap(unittest.TestCase):
    def test_signed_but_native_rejected_is_not_successor(self):
        s = ('h0', 0)
        e = Event(True, 'h0', 'h1', 1, False, True, 'OWN_UPDATE')
        self.assertTrue(metadata_only(s, e))
        self.assertEqual(strict_step(s, e), s)

    def test_signed_but_not_persisted_is_not_successor(self):
        s = ('h0', 0)
        e = Event(True, 'h0', 'h1', 1, True, False, 'OWN_UPDATE')
        self.assertTrue(metadata_only(s, e))
        self.assertEqual(strict_step(s, e), s)

    def test_native_accepted_and_persisted_advances(self):
        s = ('h0', 0)
        e = Event(True, 'h0', 'h1', 1, True, True, 'OWN_UPDATE')
        self.assertEqual(strict_step(s, e), ('h1', 1))

    def test_external_commit_not_automatically_healing(self):
        s = ('h0', 0)
        e = Event(True, 'h0', 'h1', 1, True, True, 'EXTERNAL_COMMIT')
        self.assertEqual(strict_step(s, e), ('h1', 1))
        independent_healing_secret_proven = False
        self.assertFalse(independent_healing_secret_proven)

if __name__ == '__main__':
    unittest.main()
