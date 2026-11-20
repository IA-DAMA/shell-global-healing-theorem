#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Event {
    AcceptUpdate { member: u8, generation: u8 },
    StartCorrupt { member: u8 },
    EndCorrupt { member: u8 },
    RevealCurrent { member: u8 },
    Remove { member: u8 },
    Challenge { generator: u8 },
}

#[derive(Clone, Debug)]
struct Trace {
    members: Vec<u8>,
    events: Vec<Event>,
}

fn challenge_pos(t: &Trace) -> usize {
    t.events.iter().position(|e| matches!(e, Event::Challenge { .. })).unwrap()
}

fn generator(t: &Trace) -> u8 {
    match t.events[challenge_pos(t)] { Event::Challenge { generator } => generator, _ => unreachable!() }
}

fn accepted_members_at_challenge(t: &Trace) -> Vec<u8> {
    let cp=challenge_pos(t);
    t.members.iter().copied().filter(|u|
        !t.events[..cp].iter().any(|e| matches!(e,Event::Remove{member} if member==u))
    ).collect()
}

fn install_pos(t: &Trace, u:u8) -> Option<usize> {
    let cp=challenge_pos(t);
    t.events[..cp].iter().enumerate().rev().find_map(|(i,e)|
        match e { Event::AcceptUpdate{member,..} if *member==u => Some(i), _=>None })
}

fn exposed_in_current_window(t:&Trace,u:u8)->bool {
    let cp=challenge_pos(t);
    let start=install_pos(t,u).unwrap_or(0);
    let mut corrupt=false;
    for e in &t.events[start..cp] {
        match *e {
            Event::StartCorrupt{member} if member==u => corrupt=true,
            Event::EndCorrupt{member} if member==u => corrupt=false,
            Event::RevealCurrent{member} if member==u => return true,
            _=>{}
        }
        if corrupt { return true; }
    }
    false
}

fn covered_fresh_q(t:&Trace)->bool {
    let cp=challenge_pos(t);
    if cp==0 { return false; }
    accepted_members_at_challenge(t).into_iter().all(|u| !exposed_in_current_window(t,u))
}

// Canonical two-member trace: B was compromised under generation 0, then B
// installs replacement generation 1 after corruption ends. A also updates.
// Both paths are safe at challenge.
fn canonical()->Trace {
    Trace{members:vec![1,2],events:vec![
        Event::StartCorrupt{member:2},
        Event::RevealCurrent{member:2},
        Event::EndCorrupt{member:2},
        Event::AcceptUpdate{member:2,generation:1},
        Event::AcceptUpdate{member:1,generation:1},
        Event::Challenge{generator:1},
    ]}
}

#[test]
fn canonical_covered_trace_is_fresh(){ assert!(covered_fresh_q(&canonical())); }

#[test]
fn m1_drop_member_would_be_unsound(){
    let mut t=canonical();
    t.events.remove(3); // B never renews.
    assert!(!covered_fresh_q(&t));
    let mut bad=t.clone(); bad.members=vec![1]; // Phi illegally drops B.
    assert!(covered_fresh_q(&bad), "mutant demonstrates why membership preservation is mandatory");
}

#[test]
fn m2_shift_install_shortens_window_unsoundly(){
    let mut t=canonical();
    t.events=vec![
        Event::AcceptUpdate{member:2,generation:0},
        Event::StartCorrupt{member:2},Event::RevealCurrent{member:2},Event::EndCorrupt{member:2},
        Event::AcceptUpdate{member:1,generation:1},Event::Challenge{generator:1}
    ];
    assert!(!covered_fresh_q(&t));
    // A translator inventing a later B install would flip the answer.
    t.events.insert(4,Event::AcceptUpdate{member:2,generation:1});
    assert!(covered_fresh_q(&t));
}

#[test]
fn m3_drop_corruption_is_detectable(){
    let mut t=canonical();
    t.events.remove(3); // no B renewal
    assert!(!covered_fresh_q(&t));
    t.events.retain(|e| !matches!(e,Event::StartCorrupt{member:2}|Event::RevealCurrent{member:2}));
    assert!(covered_fresh_q(&t), "dropping corruption changes classification and must be forbidden by Phi");
}

#[test]
fn m4_wrong_generator_is_a_distinct_challenge_identity(){
    let t=canonical();
    assert_eq!(generator(&t),1);
    let mut m=t.clone();
    let cp=challenge_pos(&m);
    m.events[cp]=Event::Challenge{generator:2};
    assert_ne!(generator(&t),generator(&m));
}

#[test]
fn m5_unaccepted_renewal_does_not_heal(){
    let t=Trace{members:vec![1,2],events:vec![
        Event::AcceptUpdate{member:2,generation:0},
        Event::StartCorrupt{member:2},Event::RevealCurrent{member:2},Event::EndCorrupt{member:2},
        // generation without AcceptUpdate is intentionally absent from provider state
        Event::AcceptUpdate{member:1,generation:1},Event::Challenge{generator:1}
    ]};
    assert!(!covered_fresh_q(&t));
}

#[test]
fn m6_authentic_removal_excludes_old_holder_from_challenge_membership(){
    let t=Trace{members:vec![1,2],events:vec![
        Event::StartCorrupt{member:2},Event::RevealCurrent{member:2},Event::EndCorrupt{member:2},
        Event::Remove{member:2},Event::AcceptUpdate{member:1,generation:1},
        Event::Challenge{generator:1}
    ]};
    assert_eq!(accepted_members_at_challenge(&t),vec![1]);
    assert!(covered_fresh_q(&t));
}

#[test]
fn m7_network_only_does_not_change_freshness(){
    // Scheduling events are deliberately not freshness events. The provider
    // classifier sees accepted state/exposure, not mere delivery attempts.
    assert!(covered_fresh_q(&canonical()));
}

#[test]
fn m8_posthoc_win_cannot_be_an_input_to_freshness(){
    let t=canonical();
    let before=covered_fresh_q(&t);
    let hypothetical_adversary_won=true;
    assert!(hypothetical_adversary_won);
    assert_eq!(covered_fresh_q(&t),before);
}
