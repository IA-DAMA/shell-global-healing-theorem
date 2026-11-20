"""Fail-closed typed oracle contract model, NOT OpenMLS or a PCS proof.
Authentication is an input assertion, not native signature verification.
"""
from dataclasses import dataclass
from typing import Callable, Optional
from secrets import token_bytes

EVENTS = frozenset({'corrupt','reveal','send_application','commit_accepted',
                    'welcome_install_verified','external_commit_accepted','resync_install_verified','challenge'})

@dataclass(frozen=True)
class Exposure:
    index: int
    member: str
    device: str
    epoch: Optional[int]
    secret_kind: str
    event: str

@dataclass(frozen=True)
class Query:
    kind: str
    member: str
    device: str
    secret_kind: str = 'epoch_secret'
    installed_epoch: Optional[int] = None
    authenticated: bool = False
    challenge_id: Optional[str] = None
    # A return from the exposure oracle, separate from authentication of requests.
    disclosure_returned: bool = True
    context: bytes = b""

@dataclass(frozen=True)
class ChallengeWorld:
    """The experiment supplies a fixed world and its selected exporter backend."""
    real: bool
    read_exporter: Callable[[Query, int], Optional[bytes]]
    sample_ideal: Callable[[int], bytes] = token_bytes

    def __post_init__(self):
        if type(self.real) is not bool:
            raise TypeError('real must be bool')


@dataclass(frozen=True)
class Record:
    index: int
    kind: str
    global_before: int
    global_after: int
    member: str
    device: str
    request_authorized: bool
    epoch_advanced: bool
    challenge_id: Optional[str]

@dataclass(frozen=True)
class State:
    global_epoch: int = 0
    local_epochs: tuple = ()
    ledger: tuple = ()
    exposures: tuple = ()
    challenge_attempts: tuple = ()

    challenge_response: Optional[bytes] = None
    bad_challenge_t1: bool = False
    freshq: bool = False


def transition(state: State, query: Query, *, world: Optional[ChallengeWorld] = None) -> State:
    if query.kind not in EVENTS:
        raise ValueError('unknown query')
    if not query.member or not query.device or not query.secret_kind:
        raise ValueError('typed identity required')
    if type(query.disclosure_returned) is not bool or type(query.context) is not bytes:
        raise TypeError('invalid disclosure status or exporter context')
    if type(query.authenticated) is not bool:
        raise TypeError('authenticated must be bool')
    if query.kind == 'challenge' and not query.challenge_id:
        raise ValueError('challenge id required')
    if query.kind != 'challenge' and query.challenge_id is not None:
        raise ValueError('challenge id on nonchallenge')
    if query.kind in {'welcome_install_verified', 'resync_install_verified'}:
        if type(query.installed_epoch) is not int or not 0 <= query.installed_epoch <= state.global_epoch:
            raise ValueError('Welcome epoch must be an existing global epoch')
    elif query.installed_epoch is not None:
        raise ValueError('installed_epoch only valid for Welcome')
    idx = len(state.ledger)
    advance = query.authenticated and query.kind in {'commit_accepted','external_commit_accepted'}
    epoch = state.global_epoch + int(advance)
    local = dict(state.local_epochs)
    if advance:
        local[(query.member, query.device)] = epoch
    elif query.kind in {'welcome_install_verified', 'resync_install_verified'} and query.authenticated:
        local[(query.member, query.device)] = query.installed_epoch
    exposures = state.exposures
    bad = state.bad_challenge_t1 or query.kind in {'welcome_install_verified','resync_install_verified'}
    fresh = state.freshq
    response = state.challenge_response
    if query.kind in {'corrupt','reveal'} and query.disclosure_returned:
        if state.challenge_attempts:
            bad = True
        # Corruption targets a device's installed secret, not the latest
        # global epoch. An uninstalled device has no justified epoch witness.
        exposures += (Exposure(idx,query.member,query.device,
                               local.get((query.member,query.device)),
                               query.secret_kind,query.kind),)
    challenges = state.challenge_attempts
    if query.kind == 'challenge':
        # Conservative projection proved by gate_fresh_exact. Available records
        # supply no witness of healing after any successful disclosure.
        fresh = (not bad and not challenges and not exposures
                 and local.get((query.member, query.device)) == epoch)
        if fresh and world is not None:
            # Read once under the identical access/failure policy in both worlds.
            selected = world.read_exporter(query, epoch)
            if selected is not None and (type(selected) is not bytes or len(selected) != 32):
                raise ValueError("malformed exporter result")
            if selected is not None:
                response = selected if world.real else world.sample_ideal(32)
                if type(response) is not bytes or len(response) != 32:
                    raise ValueError("malformed ideal response")
            else:
                bad = True
        else:
            bad = True
        challenges += ((idx,query.challenge_id,query.member,query.device,state.global_epoch),)
    rec = Record(idx,query.kind,state.global_epoch,epoch,query.member,query.device,
                 query.authenticated,advance,query.challenge_id)
    return State(epoch,tuple(sorted(local.items())),state.ledger+(rec,),exposures,challenges,
                 response,bad,fresh)

def replay(queries, *, world=None):
    state = State()
    for query in queries:
        state = transition(state,query,world=world)
    return state

def test_contract():
    q = [Query('corrupt','alice','phone'),Query('corrupt','alice','phone'),
         Query('commit_accepted','bob','tablet',authenticated=True),
         Query('welcome_install_verified','carol','laptop',installed_epoch=1,authenticated=True),
         Query('send_application','carol','laptop',authenticated=True),
         Query('challenge','carol','laptop',challenge_id='c0')]
    s = replay(q)
    assert s.global_epoch == 1
    assert dict(s.local_epochs)[('carol','laptop')] == 1
    assert len(s.exposures) == 2 and s.exposures[0].index != s.exposures[1].index
    assert s.exposures[0].epoch is None and s.exposures[1].epoch is None
    local_exposure = replay([Query('commit_accepted','alice','phone',authenticated=True),
        Query('corrupt','alice','phone')])
    assert local_exposure.exposures[0].epoch == 1
    assert s.challenge_attempts == ((5,'c0','carol','laptop',1),)
    assert [x.epoch_advanced for x in s.ledger] == [False,False,True,False,False,False]
    assert s.ledger[4].request_authorized and not s.ledger[4].epoch_advanced
    assert transition(State(global_epoch=7),Query('welcome_install_verified','a','d',installed_epoch=7,authenticated=True)).global_epoch == 7
    for bad in [Query('challenge','a','d'),Query('welcome_install_verified','a','d',installed_epoch=3),
                Query('commit_accepted','a','d',authenticated='yes')]:
        try:
            transition(State(),bad)
        except (ValueError,TypeError):
            pass
        else:
            raise AssertionError('bad event accepted')
    print('F4_TYPED_CONTRACT_SPEC_PASS; NOT a native refinement or PCS/QPT proof')

if __name__ == '__main__':
    test_contract()
