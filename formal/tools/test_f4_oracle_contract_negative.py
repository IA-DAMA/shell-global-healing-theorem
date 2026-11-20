"""Negative F4 oracle contract tests. No PCS, QPT or native refinement claim.

Run: python3 -m unittest discover -s formal/tools -p 'test_f4_oracle_contract_negative.py'
"""
import unittest
from f4_adaptive_challenger_ledger import Query, State, replay, step

class F4OracleContractNegative(unittest.TestCase):
    def test_send_does_not_advance_epoch(self):
        q = Query("send", accepted=True, native_verified=True,
                  current_verified=True, parent_matches=True)
        self.assertEqual(step(State(epoch=9), q).epoch, 9)

    def test_challenge_after_corrupt_is_only_recorded_not_adjudicated(self):
        s = replay((Query("corrupt"), Query("challenge")))
        self.assertEqual(s.challenges, ((1, 0, "exporter"),))
        self.assertIn((0, "exporter"), s.compromised)
        self.assertFalse(hasattr(s, "bad_challenge_t1"))
        self.assertFalse(hasattr(s, "challenge_response"))

    def test_challenge_after_reveal_is_only_recorded(self):
        s = replay((Query("reveal"), Query("challenge")))
        self.assertIn((0, "exporter"), s.revealed)
        self.assertEqual(s.challenges, ((1, 0, "exporter"),))
        self.assertFalse(hasattr(s, "freshq"))

    def test_welcome_is_not_separate_oracle_event(self):
        with self.assertRaises(ValueError):
            step(State(epoch=7), Query("welcome_install_verified"))

    def test_two_members_same_target_cannot_be_distinguished(self):
        s = replay((Query("corrupt", target="exporter"),
                    Query("corrupt", target="exporter")))
        self.assertEqual(len(s.compromised), 1)
        self.assertEqual(len(s.ledger), 2)

if __name__ == "__main__":
    unittest.main()
