"""F4 adaptive challenger ledger, executable *specification only*.

Corruption is recorded by the challenger even if invisible to both observers.
This is not a refinement of OpenMLS, a proof of FreshQ, or a QPT reduction.
"""
from dataclasses import dataclass, replace
from itertools import product

KINDS = ("corrupt", "reveal", "send", "commit", "join", "resync", "challenge")
@dataclass(frozen=True)
class Query:
    kind: str
    target: str = "exporter"
    accepted: bool = False
    native_verified: bool = False
    current_verified: bool = False
    parent_matches: bool = False

@dataclass(frozen=True)
class Entry:
    index: int
    kind: str
    epoch_before: int
    epoch_after: int
    target: str
    accepted: bool

@dataclass(frozen=True)
class State:
    epoch: int = 0
    ledger: tuple = ()
    compromised: frozenset = frozenset()
    revealed: frozenset = frozenset()
    challenges: tuple = ()

def step(state, query):
    if query.kind not in KINDS:
        raise ValueError("unknown oracle query")
    # Strictly reject forged truthy values such as "verified". This is still
    # a specification guard, not native signature verification.
    if any(type(flag) is not bool for flag in (query.accepted, query.native_verified,
                                              query.current_verified, query.parent_matches)):
        raise TypeError("acceptance evidence flags must be booleans")
    gate = (query.accepted and query.native_verified and
            query.current_verified and query.parent_matches)
    advance = query.kind in ("commit", "join", "resync") and gate
    next_epoch = state.epoch + int(advance)
    entry = Entry(len(state.ledger), query.kind, state.epoch, next_epoch,
                  query.target, bool(advance))
    compromised = state.compromised
    revealed = state.revealed
    if query.kind == "corrupt":
        compromised = compromised | {(state.epoch, query.target)}
    if query.kind == "reveal":
        revealed = revealed | {(state.epoch, query.target)}
    # Deliberately never infer healing from an accepted commit.
    challenges = state.challenges
    if query.kind == "challenge":
        challenges += ((entry.index, state.epoch, query.target),)
    return State(next_epoch, state.ledger + (entry,), compromised,
                 revealed, challenges)

def replay(queries):
    state = State()
    for query in queries:
        state = step(state, query)
    return state

def audit_challenger(actual_queries, claimed_ledger):
    canonical = replay(actual_queries).ledger
    return canonical == tuple(claimed_ledger)

def run():
    n = 0
    for length in range(4):
        for kinds in product(KINDS, repeat=length):
            queries = tuple(Query(k) for k in kinds)
            result = replay(queries)
            assert len(result.ledger) == length
            assert [e.index for e in result.ledger] == list(range(length))
            assert result.epoch == 0  # No accepted native evidence supplied
            assert audit_challenger(queries, result.ledger)
            if length:
                assert not audit_challenger(queries, result.ledger[:-1])
            n += 1
    for kind in ("send", "commit", "join", "resync"):
        for mask in range(16):
            flags = [(mask >> i) & 1 == 1 for i in range(4)]
            query = Query(kind, accepted=flags[0], native_verified=flags[1],
                          current_verified=flags[2], parent_matches=flags[3])
            state = step(State(), query)
            assert state.epoch == int(all(flags) and kind != "send")
            assert state.ledger[0].accepted == (all(flags) and kind != "send")
            n += 1
    assert step(State(epoch=7), Query("send", accepted=True, native_verified=True, current_verified=True, parent_matches=True)).epoch == 7
    assert step(State(epoch=7), Query("commit", accepted=True, native_verified=True, current_verified=True, parent_matches=True)).epoch == 8
    for field in ("accepted", "native_verified", "current_verified", "parent_matches"):
        try:
            step(State(), replace(Query("commit"), **{field: "verified"}))
        except TypeError:
            pass
        else:
            raise AssertionError(f"truthy nonboolean bypass: {field}")
        n += 1
    hidden = (Query("corrupt"), Query("challenge"))
    truth = replay(hidden)
    assert not audit_challenger(hidden, ())
    assert truth.compromised == frozenset({(0, "exporter")})
    assert truth.challenges == ((1, 0, "exporter"),)
    assert replay((Query("corrupt"), Query("send", accepted=True,
                native_verified=True, current_verified=True,
                parent_matches=True))).compromised == frozenset({(0, "exporter")})
    print(f"F4_ADAPTIVE_LEDGER_SPEC_PASS cases={n} (Python specification only)")

if __name__ == "__main__":
    run()
