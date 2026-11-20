require import AllCore List.

(* Fixed synthetic target generation and two distinct holders. No bytes, oracle
   for knowledge, or native completeness flag. The operational state is four
   capability bits per holder; the independent ledger uses lists of origins. *)
type item = [ Old | Blob | Key | Output ].
type cmd = [ OldCapture | Prepare | Apply | Snapshot | Welcome | Resync
           | RemoveError | Crash | Restart | Retry | CopyDevice | Grant ].
type cell = bool * bool * bool * bool.
type native = { disk:cell; live:cell; peer:cell; view:cell; up:bool }.
type ghost = { durable:item list; staged:item list; remote:item list; acquired:item list; online:bool }.
op empty : cell = (false,false,false,false).
op has_item (c:cell) i = with i=Old => c.`1 with i=Blob => c.`2
  with i=Key => c.`3 with i=Output => c.`4.
op additem i (c:cell) =
  (c.`1 \/ i=Old, c.`2 \/ i=Blob, c.`3 \/ i=Key, c.`4 \/ i=Output).
op merge (a b:cell) = (a.`1 \/ b.`1,a.`2 \/ b.`2,a.`3 \/ b.`3,a.`4 \/ b.`4).
op readout (a:cell) = if a.`2 /\ a.`3 then additem Output a else a.
op derive (xs:item list) = if mem xs Blob /\ mem xs Key then Output::xs else xs.
op matches (c:cell) (xs:item list) = forall i, has_item c i <=> mem xs i.
op covered (s:native) (g:ghost) = s.`up=g.`online /\ matches s.`disk g.`durable /\
  matches s.`live g.`staged /\ matches s.`peer g.`remote /\ matches s.`view g.`acquired.
op physical (s:native) opn =
  with opn=Crash => {| s with live=empty; up=false |}
  with opn=Restart => if s.`up then s else {|s with live=empty; up=true|}
  with opn=CopyDevice => {|s with view=merge s.`view s.`peer|}
  with opn=OldCapture => if s.`up then {|s with view=additem Old s.`view|} else s
  with opn=Prepare => if s.`up then {|s with live=additem Blob s.`live|} else s
  with opn=Apply => if s.`up then {|s with disk=merge s.`disk s.`live|} else s
  with opn=RemoveError => if s.`up then {|s with disk=merge s.`disk s.`live|} else s
  with opn=Snapshot => if s.`up then {|s with view=merge s.`view s.`disk|} else s
  with opn=Welcome => if s.`up then {|s with peer=additem Blob s.`peer|} else s
  with opn=Grant => if s.`up then {|s with peer=additem Key s.`peer|} else s
  with opn=Resync => if s.`up then {|s with view=readout s.`view|} else s
  with opn=Retry => if s.`up then {|s with view=readout s.`view|} else s.
op record (g:ghost) opn =
  with opn=Crash => {|g with staged=[]; online=false|}
  with opn=Restart => if g.`online then g else {|g with staged=[]; online=true|}
  with opn=CopyDevice => {|g with acquired=g.`acquired ++ g.`remote|}
  with opn=OldCapture => if g.`online then {|g with acquired=Old::g.`acquired|} else g
  with opn=Prepare => if g.`online then {|g with staged=Blob::g.`staged|} else g
  with opn=Apply => if g.`online then {|g with durable=g.`durable ++ g.`staged|} else g
  with opn=RemoveError => if g.`online then {|g with durable=g.`durable ++ g.`staged|} else g
  with opn=Snapshot => if g.`online then {|g with acquired=g.`acquired ++ g.`durable|} else g
  with opn=Welcome => if g.`online then {|g with remote=Blob::g.`remote|} else g
  with opn=Grant => if g.`online then {|g with remote=Key::g.`remote|} else g
  with opn=Resync => if g.`online then {|g with acquired=derive g.`acquired|} else g
  with opn=Retry => if g.`online then {|g with acquired=derive g.`acquired|} else g.

lemma zero_rel : matches empty [].
proof. rewrite /matches; by case. qed.
lemma add_rel c xs k : matches c xs => matches (additem k c) (k::xs).
proof. rewrite /matches => h i; have := h i; by case: i; case: k; rewrite /additem /=; smt(). qed.
lemma merge_rel a b xs ys : matches a xs => matches b ys => matches (merge a b) (xs++ys).
proof. rewrite /matches => ha hb i; have := ha i; have := hb i; by case: i; rewrite /merge mem_cat /=; smt(). qed.
lemma derive_rel c xs : matches c xs => matches (readout c) (derive xs).
proof. move=> h; have b := h Blob; have k := h Key; rewrite /readout /derive; case (c.`2 /\ c.`3);
  smt(add_rel). qed.

lemma cc_oldcapture s g : covered s g => covered (physical s OldCapture) (record g OldCapture).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_prepare s g : covered s g => covered (physical s Prepare) (record g Prepare).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_apply s g : covered s g => covered (physical s Apply) (record g Apply).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_snapshot s g : covered s g => covered (physical s Snapshot) (record g Snapshot).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_welcome s g : covered s g => covered (physical s Welcome) (record g Welcome).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_resync s g : covered s g => covered (physical s Resync) (record g Resync).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_removeerror s g : covered s g => covered (physical s RemoveError) (record g RemoveError).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_crash s g : covered s g => covered (physical s Crash) (record g Crash).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_restart s g : covered s g => covered (physical s Restart) (record g Restart).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_retry s g : covered s g => covered (physical s Retry) (record g Retry).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_copydevice s g : covered s g => covered (physical s CopyDevice) (record g CopyDevice).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma cc_grant s g : covered s g => covered (physical s Grant) (record g Grant).
proof. rewrite /covered /physical /record /=; case s.`up; case g.`online; simplify; smt(zero_rel merge_rel add_rel derive_rel). qed.

lemma every_step s g opn : covered s g => covered (physical s opn) (record g opn).
proof. case: opn; smt(cc_oldcapture cc_prepare cc_apply cc_snapshot cc_welcome cc_resync cc_removeerror cc_crash cc_restart cc_retry cc_copydevice cc_grant). qed.
lemma every_prefix ops s g : covered s g =>
  covered (foldl physical s ops) (foldl record g ops).
proof. elim: ops s g => [|c cs ih] s g h //=; by apply ih; apply every_step. qed.

op start = {| disk=empty;live=empty;peer=empty;view=empty;up=true |}.
op startg = {|durable=[];staged=[];remote=[];acquired=[];online=true|}.
op admissible (s:native) = s.`up /\ s.`disk.`2 /\ s.`view.`1 /\
  !(s.`view.`4 \/ (s.`view.`2 /\ s.`view.`3)).
op prefix = [OldCapture;Prepare;RemoveError;Crash;Restart].
op adapt (s:native) = if admissible s then [Snapshot;Grant;CopyDevice;Retry] else [].
op finish_without_grant (s:native) = if s.`up then [Snapshot;Retry] else [Restart].
lemma adaptive_local_positive :
  admissible (foldl physical (foldl physical start prefix) (finish_without_grant (foldl physical start prefix))).
proof. by rewrite /finish_without_grant /admissible /prefix /start /= /additem /empty /merge /readout. qed.

lemma witnessed : covered start startg /\ admissible (foldl physical start prefix) /\
  (foldl physical (foldl physical start prefix) (adapt (foldl physical start prefix))).`view.`4.
proof. split.
  + by rewrite /covered /start /startg /= zero_rel.
  by rewrite /adapt /admissible /prefix /start /= /additem /empty /merge /readout.
qed.
