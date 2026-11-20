"""F4 M1: finite countermodel for adaptive retained-state exposure.
Not an OpenMLS proof; no private source or production inputs.
"""
import unittest

def reachable(seed, rules):
    known = set(seed)
    while True:
        new = {out for required, out in rules if set(required) <= known} - known
        if not new:
            return known
        known |= new

def exposed_at(snapshot, time, disclosures):
    return {secret for t, secret in disclosures if t <= time and secret in snapshot.get(t, set())}

class TemporalErasureCountermodel(unittest.TestCase):
    def test_erasure_before_corruption_prevents_direct_reveal(self):
        state = {1: {'retained_hpke_sk'}, 2: set()}
        self.assertEqual(exposed_at(state, 2, [(2, 'retained_hpke_sk')]), set())

    def test_old_snapshot_defeats_later_erasure(self):
        state = {1: {'retained_hpke_sk'}, 2: set()}
        disclosed = exposed_at(state, 1, [(1, 'retained_hpke_sk')])
        rules = [(('retained_hpke_sk', 'public_ciphertext'), 'path_secret'),
                 (('path_secret', 'init_secret'), 'epoch_secret')]
        self.assertIn('epoch_secret', reachable(disclosed | {'public_ciphertext', 'init_secret'}, rules))

    def test_absent_retention_evidence_must_not_certify_fresh(self):
        public_trace = ('commit_applied', 'epoch_advanced')
        erased = {2: set()}
        retained = {2: {'retained_hpke_sk'}}
        self.assertEqual(public_trace, public_trace)
        self.assertNotEqual(exposed_at(erased, 2, [(2, 'retained_hpke_sk')]),
                            exposed_at(retained, 2, [(2, 'retained_hpke_sk')]))

if __name__ == '__main__':
    unittest.main()
