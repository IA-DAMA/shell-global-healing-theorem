"""F4-M1: rollback of retained private state defeats an erasure-only FreshQ test.
Finite negative model, not a claim about Product or OpenMLS implementation.
"""
import unittest
from dataclasses import dataclass

@dataclass(frozen=True)
class State:
    epoch: int
    live: frozenset
    snapshots: tuple
    adversary: frozenset

def snapshot(s):
    return State(s.epoch, s.live, s.snapshots + (s.live,), s.adversary)

def erase(s, secret):
    return State(s.epoch + 1, s.live - {secret}, s.snapshots, s.adversary)

def restore_and_corrupt(s, index):
    recovered = s.snapshots[index]
    return State(s.epoch, recovered, s.snapshots, s.adversary | recovered)

def naive_fresh(s, target):
    return target not in s.live

def knowledge_fresh(s, target):
    return target not in s.adversary

class RetainedSnapshotCountermodel(unittest.TestCase):
    def test_erasure_does_not_revoke_snapshot(self):
        s = snapshot(State(4, frozenset({"hpke_epoch4"}), (), frozenset()))
        s = erase(s, "hpke_epoch4")
        self.assertTrue(naive_fresh(s, "hpke_epoch4"))
        s = restore_and_corrupt(s, 0)
        self.assertFalse(knowledge_fresh(s, "hpke_epoch4"))

    def test_no_snapshot_means_restore_not_possible(self):
        s = erase(State(4, frozenset({"hpke_epoch4"}), (), frozenset()), "hpke_epoch4")
        with self.assertRaises(IndexError):
            restore_and_corrupt(s, 0)

    def test_snapshot_corruption_survives_subsequent_erasure(self):
        s = snapshot(State(4, frozenset({"hpke_epoch4"}), (), frozenset()))
        s = restore_and_corrupt(s, 0)
        s = erase(s, "hpke_epoch4")
        self.assertTrue(naive_fresh(s, "hpke_epoch4"))
        self.assertFalse(knowledge_fresh(s, "hpke_epoch4"))

if __name__ == "__main__":
    unittest.main()
