"""Adversarial ledger completeness counterexamples, not OpenMLS or QPT proof.

The canonical ledger belongs to the challenger. Two matching observer logs do
not imply that either observer saw all adaptive corruption/reveal queries.
"""
from dataclasses import dataclass
from itertools import product

@dataclass(frozen=True)
class Event:
    index: int
    kind: str
    epoch: int
    target: str


def audit(canonical, shell, provider):
    """Fail closed on missing, duplicated, reordered or fabricated events."""
    if shell != provider:
        return False, 'observer_divergence'
    if shell != canonical:
        return False, 'incomplete_or_fabricated_ledger'
    if [e.index for e in canonical] != list(range(len(canonical))):
        return False, 'invalid_challenger_indices'
    return True, 'complete'


def run():
    kinds = ('corrupt', 'reveal', 'send', 'join', 'resync', 'challenge')
    checked = 0
    for n in range(1, 4):
        for sequence in product(kinds, repeat=n):
            truth = tuple(Event(i, k, i // 2, 'exporter') for i, k in enumerate(sequence))
            assert audit(truth, truth, truth) == (True, 'complete')
            for omitted in range(n):
                partial = truth[:omitted] + truth[omitted + 1:]
                assert partial == partial
                assert audit(truth, partial, partial) == (False, 'incomplete_or_fabricated_ledger')
                checked += 1
            if n > 1:
                reordered = tuple(reversed(truth))
                assert audit(truth, reordered, reordered)[0] is False
                checked += 1
    truth = (Event(0, 'corrupt', 0, 'exporter'),)
    assert audit(truth, (), ()) == (False, 'incomplete_or_fabricated_ledger')
    assert audit(truth, truth, ()) == (False, 'observer_divergence')
    assert audit((Event(9, 'challenge', 0, 'exporter'),),
                 (Event(9, 'challenge', 0, 'exporter'),),
                 (Event(9, 'challenge', 0, 'exporter'),)) == (False, 'invalid_challenger_indices')
    print(f'F4_LEDGER_NEGATIVE_SPEC_PASS cases={checked} (Python model only)')

if __name__ == '__main__':
    run()
