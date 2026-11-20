#[derive(Clone, Debug, PartialEq, Eq)]
struct ChallengeBinding {
    domain: &'static str,
    provider: &'static str,
    version: &'static str,
    suite: &'static str,
    group: [u8;4],
    head: [u8;4],
    parent: [u8;4],
    epoch: u64,
    membership: [u8;4],
    generator: [u8;4],
    state_auth: [u8;4],
    exporter_label: &'static str,
    exporter_context: &'static [u8],
    purpose: &'static str,
    output_len: usize,
    accepted: bool,
}
fn same_challenge(a:&ChallengeBinding,b:&ChallengeBinding)->bool { a==b }
fn canonical()->ChallengeBinding {
    ChallengeBinding{
        domain:"shell.challenge/1",provider:"openmls",version:"0.9.0",suite:"q-leg",
        group:*b"GRP1",head:*b"H001",parent:*b"P000",epoch:7,membership:*b"M001",
        generator:*b"D001",state_auth:*b"A001",exporter_label:"shell.q/1",
        exporter_context:b"history/H001/epoch/7",purpose:"t1-q",output_len:32,accepted:true
    }
}
macro_rules! reject_mutant {($name:ident,$mutate:expr)=>{#[test] fn $name(){let a=canonical();let mut b=a.clone();$mutate(&mut b);assert!(!same_challenge(&a,&b));}}}
reject_mutant!(c1_epoch_shift,|b:&mut ChallengeBinding|b.epoch+=1);
reject_mutant!(c2_view_shift,|b:&mut ChallengeBinding|b.membership=*b"M002");
reject_mutant!(c3_generator_shift,|b:&mut ChallengeBinding|b.generator=*b"D002");
reject_mutant!(c4_group_shift,|b:&mut ChallengeBinding|b.group=*b"GRP2");
reject_mutant!(c5_provider_shift,|b:&mut ChallengeBinding|b.version="future");
reject_mutant!(c6_exporter_label_shift,|b:&mut ChallengeBinding|b.exporter_label="other");
reject_mutant!(c7_exporter_context_shift,|b:&mut ChallengeBinding|b.exporter_context=b"other");
reject_mutant!(c8_head_shift,|b:&mut ChallengeBinding|b.head=*b"H002");
reject_mutant!(c9_length_purpose_shift,|b:&mut ChallengeBinding|b.output_len=64);
reject_mutant!(c10_unaccepted_state,|b:&mut ChallengeBinding|b.accepted=false);
#[test] fn exact_binding_is_same_challenge(){let a=canonical();assert!(same_challenge(&a,&a.clone()));}
