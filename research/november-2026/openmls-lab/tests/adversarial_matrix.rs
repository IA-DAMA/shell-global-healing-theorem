use shell_classical_pq_composition::combine_exported_secrets;

const C0: [u8;32] = [0x11;32];
const C1: [u8;32] = [0x12;32];
const Q0: [u8;32] = [0x21;32];
const Q1: [u8;32] = [0x22;32];
const CTX0: &[u8] = b"shell-security-game/epoch-z";
const CTX1: &[u8] = b"shell-security-game/epoch-z+1";

#[test]
fn compromise_only_classical_is_insufficient_for_target_kz() {
    let target=combine_exported_secrets(&C1,&Q1,CTX0);
    let stale_q=combine_exported_secrets(&C1,&Q0,CTX0);
    assert_ne!(target,stale_q);
}
#[test]
fn compromise_only_pq_is_insufficient_for_target_kz() {
    let target=combine_exported_secrets(&C1,&Q1,CTX0);
    let stale_c=combine_exported_secrets(&C0,&Q1,CTX0);
    assert_ne!(target,stale_c);
}
#[test]
fn compromise_both_current_inputs_recovers_target_kz() {
    let target=combine_exported_secrets(&C1,&Q1,CTX0);
    assert_eq!(target,combine_exported_secrets(&C1,&Q1,CTX0));
}
#[test]
fn rollback_epoch_context_does_not_reproduce_target_kz() {
    let target=combine_exported_secrets(&C1,&Q1,CTX1);
    assert_ne!(target,combine_exported_secrets(&C1,&Q1,CTX0));
}
#[test]
fn replay_old_inputs_under_new_context_does_not_reproduce_target_kz() {
    let target=combine_exported_secrets(&C1,&Q1,CTX1);
    assert_ne!(target,combine_exported_secrets(&C0,&Q0,CTX1));
}
#[test]
fn cross_leg_mix_from_different_generations_does_not_reproduce_target() {
    let target=combine_exported_secrets(&C1,&Q1,CTX1);
    assert_ne!(target,combine_exported_secrets(&C1,&Q0,CTX1));
    assert_ne!(target,combine_exported_secrets(&C0,&Q1,CTX1));
}
