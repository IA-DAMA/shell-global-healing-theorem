"""Finite negative model: REMOVE durable before JOIN is not a healed epoch.

This is a logical regression for the non-atomic replacement shape, NOT a Rust
implementation test or a proof of OpenMLS storage semantics.
"""
from dataclasses import dataclass, replace
import unittest

@dataclass(frozen=True)
class State:
    epoch: int
    removed: bool
    joined: bool
    adversary_knows_old: bool
    authenticated_parent: bool

def durable_remove(s: State) -> State:
    assert s.epoch == 0 and not s.removed
    return replace(s, epoch=1, removed=True, joined=False, authenticated_parent=True)

def external_join(s: State) -> State:
    assert s.epoch == 1 and s.removed and s.authenticated_parent
    return replace(s, epoch=2, joined=True)

def restart(s: State) -> State:
    return s  # durable checkpoint survives crash; no fabricated JOIN

def naive_fresh(s: State) -> bool:
    return s.epoch > 0  # intentionally unsound healing rule

def conservative_fresh(s: State) -> bool:
    # Only a necessary gate, not sufficient for PCS or independent path entropy.
    return s.joined and not s.adversary_knows_old

class ReplacementCrashCountermodel(unittest.TestCase):
    def test_crash_after_remove_is_not_healing(self):
        s = State(0, False, False, True, True)
        intermediate = restart(durable_remove(s))
        self.assertEqual(intermediate.epoch, 1)
        self.assertTrue(naive_fresh(intermediate))
        self.assertFalse(conservative_fresh(intermediate))
        self.assertFalse(intermediate.joined)

    def test_join_does_not_erase_exposure_automatically(self):
        s = State(0, False, False, True, True)
        final = external_join(durable_remove(s))
        self.assertEqual(final.epoch, 2)
        self.assertTrue(final.adversary_knows_old)
        self.assertFalse(conservative_fresh(final))

    def test_uncompromised_join_is_only_eligible_not_proven(self):
        s = State(0, False, False, False, True)
        final = external_join(durable_remove(s))
        self.assertTrue(conservative_fresh(final))

    def test_join_without_durable_remove_rejected(self):
        with self.assertRaises(AssertionError):
            external_join(State(0, False, False, True, True))

if __name__ == "__main__":
    unittest.main()
