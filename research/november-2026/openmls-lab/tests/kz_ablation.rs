use shell_classical_pq_composition::combine_exported_secrets;

#[test]
fn pq_only_ablation_changes_kz() {
    let classical=[0x11u8;32]; let pq0=[0x22u8;32]; let mut pq1=pq0; pq1[0]^=1;
    let ctx=b"same-shell-transition";
    assert_ne!(combine_exported_secrets(&classical,&pq0,ctx), combine_exported_secrets(&classical,&pq1,ctx));
}
#[test]
fn classical_only_ablation_changes_kz() {
    let c0=[0x11u8;32]; let mut c1=c0; c1[0]^=1; let pq=[0x22u8;32]; let ctx=b"same-shell-transition";
    assert_ne!(combine_exported_secrets(&c0,&pq,ctx), combine_exported_secrets(&c1,&pq,ctx));
}
#[test]
fn identical_inputs_are_deterministic() {
    let c=[0x11u8;32]; let pq=[0x22u8;32]; let ctx=b"same-shell-transition";
    assert_eq!(combine_exported_secrets(&c,&pq,ctx), combine_exported_secrets(&c,&pq,ctx));
}
#[test]
fn context_is_bound() {
    let c=[0x11u8;32]; let pq=[0x22u8;32];
    assert_ne!(combine_exported_secrets(&c,&pq,b"A"), combine_exported_secrets(&c,&pq,b"B"));
}
