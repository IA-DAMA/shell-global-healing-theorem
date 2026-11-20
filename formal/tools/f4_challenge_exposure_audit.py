"""Fail-closed adversarial challenge audit over the typed F4 specification.

This is NOT FreshQ_T1: the native secret-dependency graph and QPT game are
not yet available. No post-commit healing is inferred.
"""
from f4_typed_oracle_contract import Query, replay

def audit(queries):
    state = replay(queries)
    outcomes = []
    for rec in state.ledger:
        if rec.kind != 'challenge':
            continue
        prior = tuple(e for e in state.exposures if e.index < rec.index)
        # Global epoch is NOT necessarily the installed epoch of the target.
        # Without an epoch witness, this comparison cannot establish FreshQ.
        # Snapshot at challenge index, never the final state after later queries.
        at_challenge = replay(queries[:rec.index + 1])
        installed = dict(at_challenge.local_epochs).get((rec.member, rec.device))
        epoch_ambiguous = installed is None or installed != rec.global_before
        # Exposure is recorded against the global epoch by the current
        # specification. This is not evidence of the installed local secret.
        # Only classify same-epoch exposure if the epoch witness is aligned.
        direct = tuple(e for e in prior if
            not epoch_ambiguous and
            e.member == rec.member and e.device == rec.device and
            e.epoch == rec.global_before)
        # Historical compromise is deliberately retained; whether an
        # accepted commit heals it is an UNDISCHARGED semantic obligation.
        historical = tuple(e for e in prior if
            e.member == rec.member and e.device == rec.device)
        outcomes.append(dict(index=rec.index, challenge_id=rec.challenge_id,
            direct_exposure=bool(direct), historical_exposure=bool(historical),
            epoch_ambiguous=epoch_ambiguous,
            eligible_t1=None, bad_challenge_t1=None))
    return outcomes

def test_adversarial_cases():
    cases = [
        ([Query('challenge','a','phone',challenge_id='c')],False,False),
        ([Query('corrupt','a','phone'),Query('challenge','a','phone',challenge_id='c')],False,True),
        ([Query('reveal','a','phone'),Query('challenge','a','phone',challenge_id='c')],False,True),
        ([Query('corrupt','a','phone'),Query('commit_accepted','b','phone',authenticated=True),
          Query('challenge','a','phone',challenge_id='c')],False,True),
        ([Query('corrupt','a','phone'),Query('challenge','b','phone',challenge_id='c')],False,False),
    ]
    for queries,direct,historical in cases:
        result=audit(queries)
        assert len(result)==1
        assert result[0]['direct_exposure']==direct
        assert result[0]['historical_exposure']==historical
        assert result[0]['eligible_t1'] is None
        assert result[0]['bad_challenge_t1'] is None
    # A target can have a local epoch different from the global epoch.
    # A Welcome installation must not silently prove the challenge epoch.
    divergent = audit([Query('commit_accepted','b','tablet',authenticated=True),
        Query('welcome_install_verified','a','phone',installed_epoch=0,authenticated=True),
        Query('challenge','a','phone',challenge_id='old')])
    assert divergent[0]['epoch_ambiguous']
    assert divergent[0]['eligible_t1'] is None
    # Even a synchronized local epoch is not proof of the PCS secret lineage.
    aligned = audit([Query('commit_accepted','a','phone',authenticated=True),
        Query('challenge','a','phone',challenge_id='new')])
    assert not aligned[0]['epoch_ambiguous']
    assert aligned[0]['eligible_t1'] is None
    # Explicitly test aligned local epoch: a later exposure must be counted.
    aligned_exposed = audit([Query('commit_accepted','a','phone',authenticated=True),
        Query('corrupt','a','phone'), Query('challenge','a','phone',challenge_id='x')])
    assert aligned_exposed[0]['direct_exposure']
    assert aligned_exposed[0]['historical_exposure']
    assert not aligned_exposed[0]['epoch_ambiguous']
    print('F4_CHALLENGE_AUDIT_SPEC_PASS cases=8; T1 freshness UNPROVED')

if __name__=='__main__':
    test_adversarial_cases()
