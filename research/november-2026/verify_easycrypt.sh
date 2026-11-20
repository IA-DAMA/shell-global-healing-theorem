#!/usr/bin/env bash
set -euo pipefail
cd "${F4_EC_DIR:-/app/formal/easycrypt}"
verified=0
for f in \
  ShellTypes.ec QPCS.ec ProviderPCS_Adapter.ec Exporter.ec SplitPRF.ec \
  ShellPCS_Games.ec QPCS_Hop.ec Exporter_Hop.ec SplitPRF_Hop.ec \
  ShellPCS_T1.ec ShellPCS_MSS26.ec Phi_Refinement.ec Phi_Trace_Model.ec \
  Phi_Critical_Window.ec Phi_Canonical_Events.ec Phi_Window_Fold.ec \
  Phi_Safe_TTKEM.ec Phi_Membership_Fold.ec ShellPCS_T1_Conditional.ec \
  ShellContinuity_T2.ec F4_Typed_Challenge_Model.ec \
  F4_Signed_Authority_Refinement_Conditional.ec \
  F4_Oracle_Call_Projection.ec \
  F4_Provider_Oracle_Games_Conditional.ec \
  F4_OpenMLS_Exporter_Algorithm.ec \
  F4_OpenMLS_Exporter_MIR.ec \
  F4_OpenMLS_Exporter_Program.ec \
  F4_Epoch_Schedule_Cut.ec F4_Epoch_Continuation_Hop.ec F4_Epoch_Fixture.ec \
  F4_Installation_Fixture.ec F4_Retained_Copy_Cut.ec F4_Recovery_Prediction_Bound.ec \
  F4_Leaf_Cut_Fixture.ec F4_Singleton_Path_Cut.ec F4_Removal_Route_Closure.ec F4_Late_Opening_and_Hybrids.ec F4_Provider_Stream_Cut.ec F4_Adaptive_Provider_Cut.ec F4_Linear_Temporal_Certificate.ec \
  F4_Recovery_Word_Experiment.ec F4_Recovery_Word_Observations.ec \
  F4_Independent_Events_Bad_Challenge.ec \
  F4_Adaptive_Challenger_Ledger.ec \
  F4_Direct_Exposure_Challenge.ec \
  F4_Adaptive_History_Induction.ec \
  F4_Adversarial_Query_Ledger.ec F4_Interactive_PCS_Game.ec \
  F4_Challenge_Chronology_Obstruction.ec \
  F4_External_FreshQ_Criterion.ec \
  F4_Concrete_PCS_Budget.ec \
  F4_Interactive_PCS_Proof.ec \
  F4_XWing_Quantum_Primitive_Hops.ec \
  F4_XWing_Draft06_Seed_PRG_Bridge.ec \
  F4_Successful_Exposure_FreshQ_Bridge.ec \
  F4_Groupwide_Taint_Recovery_Criterion.ec \
  F4_Cross_Class_Causal_Cut.ec \
  F4_Native_Accepted_Trace_Refinement.ec \
  F4_Native_Interactive_Game_Refinement.ec \
  F4_Native_Full_State_Exposure_Projection.ec \
  F4_Native_Reveal_Installation_Chronology.ec \
  F4_Native_Source_Semantic_Coverage.ec F4_Post_Installation_Challenge.ec F4_Online_Recovery_Cut.ec F4_Direct_Transcript.ec F4_Counter_Block_Adapter.ec F4_QSF_Oracle_Embedding.ec \
  F4_M5_Exporter_Reopening.ec F4_M5_Exposure_Admission.ec F4_M5_Instrument_Cut.ec \
  F4_M5_Epoch_Exporter_Hops.ec F4_M5_Singleton_Schedule.ec \
  F4_M5_Selected_Removal.ec F4_M5_Removal_Random_Tape.ec \
  F4_CC_Observation_Prefix.ec F4_CC_Savepoint.ec F4_CC_Selected_Snapshot.ec \
  F4_L1_Process_Window.ec F4_L2_Product_CC.ec F4_L3_Joint_Copy_Closure.ec \
  F4_L4_Product_Game_Refinement.ec F4_L5_QPT_Blackbox_Bridge.ec \
  F4_L6_Global_Conditional_Bound.ec; do
  printf 'VERIFYING=%s\n' "$f"
  easycrypt "$f"
  verified=$((verified + 1))
  printf 'VERIFIED=%s\n' "$f"
done
printf 'EASYCRYPT_ALL_%s_ACCEPTED=true\n' "$verified"
