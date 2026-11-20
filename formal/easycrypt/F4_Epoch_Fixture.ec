(* Data emitted by the synthetic two-member Product test. *)
require import AllCore List.
type f4_fixture_kind = [Capture | Reveal | Own | Install].
op f4_epoch_fixture : (f4_fixture_kind * int * int * bool) list =
  [(Reveal, 1, 1, true);
   (Capture, 2, 1, true);
   (Capture, 3, 1, false);
   (Install, 4, 1, false);
   (Own, 5, 2, true);
   (Install, 6, 2, false);
   (Capture, 7, 2, false)].
