"""Executable negative-specification tests, NOT a PCS/QPT proof.

The adversarial ledger is challenger-owned; no assumption that Product detects corruption.
"""
from dataclasses import dataclass, field

@dataclass
class Challenger:
    epoch: int = 0
    compromised: bool = False
    revealed: set = field(default_factory=set)
    pending: bool = False
    signature_compromised: bool = False
    external_untrusted: bool = False
    accepted: list = field(default_factory=list)
    checkpoint: str = 'genesis'
    challenges: list = field(default_factory=list)
    events: list = field(default_factory=list)

    def query(self, kind, **kw):
        self.events.append((kind, dict(kw)))
        if kind == 'corrupt':
            self.compromised = True
        elif kind == 'corrupt_signing':
            self.signature_compromised = True
        elif kind in ('proposal', 'join_pending', 'commit_rejected'):
            self.pending = True
        elif kind in ('commit_accepted', 'resync_external'):
            # Test flags are not verified signatures or proof of PCS healing.
            valid = (kw.get('mls_accepted') is True
                     and kw.get('current_verified') is True
                     and kw.get('parent_checkpoint') == self.checkpoint)
            if not valid:
                return False
            if kind == 'resync_external':
                self.external_untrusted |= self.signature_compromised
            self.epoch += 1
            self.checkpoint = kw['next_checkpoint']
            self.pending = False
            self.accepted.append((self.epoch, self.checkpoint))
            # No caller-supplied honest_fresh can clear compromise.
            return True
        elif kind == 'reveal':
            self.revealed.add((kw.get('epoch', self.epoch), kw.get('target', 'exporter')))
        elif kind == 'challenge':
            target = kw.get('target', 'exporter')
            fresh = (not self.compromised and (self.epoch, target) not in self.revealed
                     and not self.external_untrusted)
            self.challenges.append((len(self.challenges), self.epoch, target, fresh))
            return fresh
        else:
            raise ValueError(kind)

def accepted(s, next_checkpoint):
    return dict(mls_accepted=True, current_verified=True,
                parent_checkpoint=s.checkpoint, next_checkpoint=next_checkpoint)

def test_negative_sequences():
    s = Challenger()
    s.query('corrupt'); s.query('proposal')
    assert s.epoch == 0 and s.query('challenge') is False
    s = Challenger()
    s.query('corrupt'); s.query('commit_accepted', **accepted(s, 'c1'))
    s.query('reveal', epoch=1)
    assert s.epoch == 1 and s.query('challenge') is False
    s = Challenger()
    s.query('corrupt_signing'); s.query('resync_external', **accepted(s, 'c1'))
    assert s.query('challenge') is False
    s = Challenger()
    s.query('join_pending'); s.query('commit_rejected')
    assert s.epoch == 0
    assert s.query('commit_accepted', honest_fresh=True) is False
    assert s.epoch == 0
    assert s.query('commit_accepted', **accepted(s, 'c1')) is True
    assert s.epoch == 1 and s.query('challenge') is True

def test_rejected_and_no_fake_healing():
    for kind in ('commit_accepted', 'resync_external'):
        for missing in ('mls_accepted', 'current_verified', 'parent_checkpoint'):
            s = Challenger()
            kw = accepted(s, 'c1')
            kw[missing] = False if missing != 'parent_checkpoint' else 'wrong'
            assert s.query(kind, **kw) is False
            assert (s.epoch, s.checkpoint, s.accepted) == (0, 'genesis', [])
    s = Challenger()
    s.query('corrupt')
    assert s.query('commit_accepted', **accepted(s, 'c1')) is True
    assert s.query('challenge') is False
    assert s.challenges == [(0, 1, 'exporter', False)]
    s = Challenger()
    s.query('reveal', target='exporter')
    assert s.query('challenge') is False
    assert s.query('challenge', target='other') is True

if __name__ == '__main__':
    test_negative_sequences()
    test_rejected_and_no_fake_healing()
    print('F4_NEGATIVE_SPEC_PASS: four sequences and fail-closed guards (model only)')
