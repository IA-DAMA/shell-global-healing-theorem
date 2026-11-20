"""F4 M1: conjunctive derivation countermodel, research-only finite graph.

A derivation requiring TWO secrets must not be represented by two unary edges.
This is a negative model, not a claim of OpenMLS implementation equivalence.
Run: python3 -m unittest discover -s openmls-lab/tests -p 'test_f4_m1_hyperedge_countermodel.py'
"""
import unittest


def derive(exposed, rules):
    known = set(exposed)
    while True:
        added = {out for inputs, out in rules if set(inputs) <= known} - known
        if not added:
            return known
        known.update(added)


class MultiInputCausalRoutes(unittest.TestCase):
    def test_hkdf_like_conjunction_not_unary_or(self):
        rules = [(("init_secret", "commit_secret"), "epoch_secret"),
                 (("epoch_secret",), "exporter_secret")]
        self.assertNotIn("exporter_secret", derive({"init_secret"}, rules))
        self.assertNotIn("exporter_secret", derive({"commit_secret"}, rules))
        self.assertIn("exporter_secret", derive({"init_secret", "commit_secret"}, rules))

    def test_omitted_input_creates_false_fresh(self):
        actual = [(("init_secret", "commit_secret"), "epoch_secret"),
                  (("epoch_secret",), "exporter_secret")]
        incomplete = [(("init_secret", "unlisted_commit_secret"), "epoch_secret")]
        exposed = {"init_secret", "commit_secret"}
        self.assertIn("exporter_secret", derive(exposed, actual))
        self.assertNotIn("exporter_secret", derive(exposed, incomplete))

    def test_public_value_is_explicit_input(self):
        rules = [(("private_key", "ciphertext"), "decapsulated_secret")]
        self.assertNotIn("decapsulated_secret", derive({"private_key"}, rules))
        self.assertIn("decapsulated_secret", derive({"private_key", "ciphertext"}, rules))


if __name__ == "__main__":
    unittest.main()
