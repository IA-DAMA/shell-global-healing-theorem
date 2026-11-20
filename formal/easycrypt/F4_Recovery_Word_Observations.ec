require import AllCore List F4_Recovery_Word_Experiment.
op observed : (copy_phase * command list * report list) list =
[(Early, [ApplyReceipt; ApplyReceipt], [(Missing, 0, true, None);
 (Missing, 0, true, None)]);
 (Early, [ApplyReceipt; CatchUp], [(Missing, 0, true, None);
 (JournalRejected, 1, true, None)]);
 (Early, [CatchUp; ApplyReceipt], [(JournalRejected, 1, true, None);
 (Missing, 0, true, None)]);
 (Early, [CatchUp; CatchUp], [(JournalRejected, 1, true, None);
 (JournalRejected, 1, true, None)]);
 (Prepared, [ApplyReceipt; ApplyReceipt], [(Advanced, 0, false, Some true);
 (Repeated, 0, false, Some true)]);
 (Prepared, [ApplyReceipt; CatchUp], [(Advanced, 0, false, Some true);
 (Current, 0, false, Some true)]);
 (Prepared, [CatchUp; ApplyReceipt], [(PendingPosition, 0, false, None);
 (Advanced, 0, false, Some true)]);
 (Prepared, [CatchUp; CatchUp], [(PendingPosition, 0, false, None);
 (PendingPosition, 0, false, None)]);
 (Applied, [ApplyReceipt; ApplyReceipt], [(Repeated, 0, false, Some true);
 (Repeated, 0, false, Some true)]);
 (Applied, [ApplyReceipt; CatchUp], [(Repeated, 0, false, Some true);
 (Current, 0, false, Some true)]);
 (Applied, [CatchUp; ApplyReceipt], [(Current, 0, false, Some true);
 (Repeated, 0, false, Some true)]);
 (Applied, [CatchUp; CatchUp], [(Current, 0, false, Some true);
 (Current, 0, false, Some true)])].

lemma native_observations_agree : observed = expected_rows.
proof. by rewrite /observed /expected_rows /phase_rows /command_pairs /report_word /report_after /step /=. qed.
