/- Capability accounting for the selected interfaces at the two measured cuts.
   A writer is pending. A peer may still have a validated predecessor.
   These are test interface outcomes, not a model of physical memory access. -/
structure Origin where
  groupId : Nat
  device : Nat
  epoch : Nat
  head : Nat
deriving DecidableEq, Repr

inductive Kind | state | exporter
deriving DecidableEq, Repr
structure Handle where
  origin : Origin
  kind : Kind
deriving DecidableEq, Repr

inductive Query
  | atWriter (k : Kind)
  | atPeer (k : Kind) (checksPass : Bool)
  | rollbackProbe
deriving DecidableEq

def delivered (peer : Origin) : Query → Option Handle
  | .atPeer k true => some ⟨peer,k⟩
  | _ => none

def accrue (peer : Origin) (held : List Handle) (q : Query) : List Handle :=
  match delivered peer q with
  | none => held
  | some h => h :: held

def justified (peer : Origin) (before : List Handle) (qs : List Query) (h : Handle) : Prop :=
  h ∈ before ∨ (h.origin = peer ∧ Query.atPeer h.kind true ∈ qs)

theorem one (p : Origin) (hs : List Handle) (q : Query) (h : Handle) :
    h ∈ accrue p hs q ↔ justified p hs [q] h := by
  obtain ⟨o, k⟩ := h
  cases q with
  | atWriter a => simp [accrue, delivered, justified]
  | rollbackProbe => simp [accrue, delivered, justified]
  | atPeer a pass => cases pass <;> simp [accrue, delivered, justified, or_comm]

theorem every_history (p : Origin) (hs : List Handle) (qs : List Query) (h : Handle) :
    h ∈ qs.foldl (accrue p) hs ↔ justified p hs qs h := by
  induction qs generalizing hs with
  | nil => simp [justified]
  | cons a tail ih =>
    rw [List.foldl_cons, ih]
    simp only [justified, List.mem_cons, one, List.not_mem_nil, or_false]
    constructor
    · rintro ((old | ⟨eq, here⟩) | ⟨eq, later⟩)
      · exact Or.inl old
      · exact Or.inr ⟨eq, Or.inl here⟩
      · exact Or.inr ⟨eq, Or.inr later⟩
    · rintro (old | ⟨eq, here | later⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr ⟨eq, here⟩)
      · exact Or.inr ⟨eq, later⟩

/-- Invocability, without claiming that comparison succeeds or returns true. -/
def mayCompare (has : Handle → Prop) (s r : Origin) : Prop :=
  has ⟨s, .state⟩ ∧ has ⟨r, .exporter⟩ ∧ s.groupId = r.groupId

theorem joint_history (p : Origin) (hs : List Handle) (qs : List Query) (s r : Origin) :
    mayCompare (fun h => h ∈ qs.foldl (accrue p) hs) s r ↔
    mayCompare (justified p hs qs) s r := by
  simp only [mayCompare, every_history]

theorem other_origin (p : Origin) (hs : List Handle) (qs : List Query) (h : Handle)
    (other : h.origin ≠ p) : h ∈ qs.foldl (accrue p) hs ↔ h ∈ hs := by
  simp [every_history, justified, other]

private def writer : Origin := ⟨1,0,2,3⟩
private def peer : Origin := ⟨1,2,2,3⟩
private def trace := [Query.atWriter .state, .atPeer .state true, .atPeer .exporter true,
                       .rollbackProbe, .atWriter .exporter]

theorem cross_device_witness :
    mayCompare (fun h => h ∈ trace.foldl (accrue peer) [⟨writer,.state⟩]) writer peer ∧
    ¬ mayCompare (fun h => h ∈ trace.foldl (accrue peer) []) writer peer := by
  unfold mayCompare
  decide

#print axioms every_history
#print axioms joint_history
#print axioms other_origin
#print axioms cross_device_witness
