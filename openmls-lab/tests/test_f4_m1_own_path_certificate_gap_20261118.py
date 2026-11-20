"""F4 M1 negative specification: an accepted exporter witness is not a PCS healing certificate.

Source anchors (private research): offline_product_f4_probe.rs and
offline_product_update.rs, inspected 2026-11-18. This is NOT a Rust proof.
"""
import unittest
from dataclasses import dataclass

@dataclass(frozen=True)
class Witness:
    operation: str
    accepted_native: bool
    own_path_verified: bool
    retained_outbox: bool
    entropy_independent: bool

def exporter_witness_possible(w):
    return w.accepted_native

def candidate_healing_anchor(w):
    return (w.operation == "OWN_UPDATE" and w.accepted_native
            and w.own_path_verified and w.retained_outbox)

def demonstrated_healing(w):
    # No source-derived proof currently establishes this last conjunct.
    return candidate_healing_anchor(w) and w.entropy_independent

class OwnPathCertificateGap(unittest.TestCase):
    def test_catchup_peer_has_exporter_but_not_own_path(self):
        w = Witness("OWN_UPDATE", True, False, False, False)
        self.assertTrue(exporter_witness_possible(w))
        self.assertFalse(candidate_healing_anchor(w))

    def test_external_commit_not_healing_by_operation_name(self):
        w = Witness("JOIN", True, False, False, False)
        self.assertFalse(candidate_healing_anchor(w))

    def test_public_path_proof_does_not_prove_entropy(self):
        w = Witness("OWN_UPDATE", True, True, True, False)
        self.assertTrue(candidate_healing_anchor(w))
        self.assertFalse(demonstrated_healing(w))

    def test_unaccepted_update_not_anchor(self):
        w = Witness("OWN_UPDATE", False, True, True, True)
        self.assertFalse(candidate_healing_anchor(w))

if __name__ == "__main__":
    unittest.main()
