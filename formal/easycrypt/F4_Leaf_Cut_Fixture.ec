(* Generated from isolated native Product commits by leaf_cut_fixture.py. *)
require import AllCore List.
op removal_cut : int * int * int * int * bool * int list * bool * bool * bool =
  (1, 2, 2, 1, true, [], false, false, true).
op removal_copy_equal : bool list = [false; true; true].
op same_receipt_cut : bool list * bool list = ([false; false], [false; true]).
op alternating_cut : int * int * int * int list * int list * bool * bool * bool * bool list =
  (1, 2, 3, [1], [1], true, false, true, [false; false; false; true]).
