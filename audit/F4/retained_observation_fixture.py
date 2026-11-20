"""Test-only hooks for a scheduled, authorized observation on a second synthetic store."""

HOOK = """
#[cfg(test)]
#[derive(Clone, Copy)]
pub(super) enum ObservationCut { BeforeMerge, AfterRollback }
#[cfg(test)]
thread_local! {
    pub(super) static OBSERVE_AT: std::cell::RefCell<Option<Box<dyn FnMut(
        ObservationCut, &rusqlite::Connection
    )>>> = std::cell::RefCell::new(None);
}
#[cfg(test)]
fn observe_cut(cut: ObservationCut, connection: &rusqlite::Connection) {
    OBSERVE_AT.with(|hook| {
        if let Some(observe) = hook.borrow_mut().as_mut() { observe(cut, connection); }
    });
}
"""

SETUP = r"""
    let prior = std::rc::Rc::new(observe_selected().expect("admitted before prepare"));
    let retained = std::rc::Rc::new(std::cell::RefCell::new(None));
    let worker_prior = prior.clone();
    let worker_retained = retained.clone();
    let peer_path = lab.group[2].clone();
    let peer_context = lab.contexts[2].clone();
    let peer_wire = lab.context_wire(2, &inspected, lab.current(2, &third_receipt,
        third.request.successor_group_info.clone(), third.request.successor_context.clone(),
        third_facts.successor_roster.clone()));
    let service_pin: [u8; 32] = lab.service.public().try_into().unwrap();
    lifecycle::OBSERVE_AT.with(|slot| {
        assert!(slot.borrow().is_none());
        *slot.borrow_mut() = Some(Box::new(move |cut, connection| {
            match cut {
                lifecycle::ObservationCut::BeforeMerge => {
                    // The caller's transaction stays paused until the independent store returns.
                    // Only the fixture SERVICE public pin is installed on this fresh test thread.
                    let pair = std::thread::scope(|scope| {
                        scope.spawn(|| {
                            FIXTURE_SERVICE_PIN.with(|p| {
                                assert!(p.borrow().is_none());
                                *p.borrow_mut() = Some(service_pin);
                            });
                            let _pin = FixturePin;
                            crate::offline_activation::with_product_fixture_clock(&clock(1000), || {
                                crate::android_storage::with_custody(&peer_path, &MATERIAL, || {
                                    let db = store::open(&peer_path)?;
                                    let req = ProductRequest::ExportGroupInfo {};
                                    let state = f4_exposure::capture_verified_full_state(&db, &peer_wire,
                                        &peer_context, &clock(1000), &req, 2)?;
                                    let reveal = f4_exposure::reveal_verified_exporter(&db, &peer_wire,
                                        &peer_context, &clock(1000), &req, 3)?;
                                    Ok((state, reveal))
                                })
                            }).expect("peer capture and reveal require valid signed CURRENT and custody")
                        }).join().unwrap()
                    });
                    assert_ne!(worker_prior.event().member_device, pair.0.event().member_device);
                    assert_eq!(worker_prior.event().epoch, pair.1.event().epoch);
                    assert!(pair.1.same_challenge_on_group(&worker_prior, connection).unwrap());
                    assert!(pair.1.same_challenge_on_group(&pair.0, connection).unwrap());
                    assert!(worker_retained.borrow_mut().replace(pair).is_none());
                    println!("F4_CC_ACQUIRE=peer_old_state,peer_old_reveal;comparison=true,true");
                }
                lifecycle::ObservationCut::AfterRollback => {
                    let held = worker_retained.borrow();
                    let (peer, revealed) = held.as_ref().expect("earlier observation was retained");
                    assert!(revealed.same_challenge_on_group(&worker_prior, connection).unwrap());
                    assert!(revealed.same_challenge_on_group(peer, connection).unwrap());
                    println!("F4_CC_RETAIN=across_rollback;comparison=true,true");
                }
            }
        }));
    });
"""

FINAL = r"""
            let held = retained.borrow();
            let (peer, old_reveal) = held.as_ref().unwrap();
            assert!(old_reveal.same_challenge_on_group(&prior, &connection)?);
            assert!(old_reveal.same_challenge_on_group(peer, &connection)?);
            assert!(!challenge.same_challenge_on_group(&prior, &connection)?);
            assert!(!challenge.same_challenge_on_group(peer, &connection)?);
            println!("F4_CC_RETAIN=after_retry;old=true,true;final=false,false");
"""

MARKERS = (
    "F4_CC_ACQUIRE=peer_old_state,peer_old_reveal;comparison=true,true",
    "F4_CC_RETAIN=across_rollback;comparison=true,true",
    "F4_CC_RETAIN=after_retry;old=true,true;final=false,false",
)


def once(text, old, new):
    if text.count(old) != 1:
        raise ValueError("unexpected or ambiguous native fixture")
    return text.replace(old, new)


def extend_native(source, fixture):
    source = once(source, "use rusqlite::OptionalExtension;", "use rusqlite::OptionalExtension;" + HOOK)
    source = once(source, "            Some(restored.epoch().as_u64())",
                  "            observe_cut(ObservationCut::BeforeMerge, c);\n            Some(restored.epoch().as_u64())")
    source = once(source, '            println!("F4_CC_PUBLIC_EPOCHS',
                  '            observe_cut(ObservationCut::AfterRollback, c);\n            println!("F4_CC_PUBLIC_EPOCHS')
    fixture = once(fixture, "&inspected, 1).map(|_| ())", "&inspected, 1)")
    fixture = once(fixture, '    observe_selected().expect("admitted before prepare");', SETUP)
    fixture = once(fixture, '    assert!(matches!(observe_selected()',
                   '    lifecycle::OBSERVE_AT.with(|slot| assert!(slot.borrow_mut().take().is_some()));\n    assert!(matches!(observe_selected()')
    anchor = "            let comparisons = [challenge.same_challenge_on_group"
    return source, once(fixture, anchor, FINAL + anchor)
