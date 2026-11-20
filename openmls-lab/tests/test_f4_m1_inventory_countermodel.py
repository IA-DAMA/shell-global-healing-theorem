"""F4 M1 executable negative witness: incomplete causal inventory is unsound.

This is a finite graph countermodel, NOT an OpenMLS source-refinement proof.
No cryptographic keys, network requests, or production data are accessed.
Run: python3 -m unittest discover -s openmls-lab/tests -p 'test_f4_m1_inventory_countermodel.py'
"""
from collections import deque
import unittest


def closure(exposed, edges):
    """Least fixed point of publicly computable single-input derivations."""
    known = set(exposed)
    queue = deque(exposed)
    adjacency = {}
    for source, destination in edges:
        adjacency.setdefault(source, set()).add(destination)
    while queue:
        for destination in adjacency.get(queue.popleft(), ()):
            if destination not in known:
                known.add(destination)
                queue.append(destination)
    return known


def challenge_is_fresh(challenge, exposed, certified_edges):
    return challenge not in closure(exposed, certified_edges)


class CausalInventoryCountermodel(unittest.TestCase):
    def test_missing_cross_class_edge_produces_false_fresh(self):
        exposed = {"retained_hpke_private"}
        challenge = "epoch_exporter_secret"
        # A deliberately incomplete observer sees no derivation route.
        observed_edges = []
        # Countermodel: the adversary can decapsulate a retained ciphertext,
        # then follow publicly specified key schedule transformations.
        actual_edges = [
            ("retained_hpke_private", "opened_path_secret"),
            ("opened_path_secret", "commit_secret"),
            ("commit_secret", "epoch_secret"),
            ("epoch_secret", "epoch_exporter_secret"),
        ]
        self.assertTrue(challenge_is_fresh(challenge, exposed, observed_edges))
        self.assertFalse(challenge_is_fresh(challenge, exposed, actual_edges))

    def test_complete_inventory_rejects_exposed_route(self):
        edges = [("path", "commit"), ("commit", "epoch")]
        self.assertFalse(challenge_is_fresh("epoch", {"path"}, edges))

    def test_no_route_remains_unresolved_not_proven_secure(self):
        self.assertTrue(challenge_is_fresh("epoch", {"unrelated"}, []))
        # The result is only graph nonreachability, not computational PCS.


if __name__ == "__main__":
    unittest.main()
