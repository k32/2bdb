From LibTx Require Import
     SLOT.Hoare.

Require Import List.
Import ListNotations.

Ltac unfold_trace f :=
  match type of f with
  | LongStep ?s1 [] ?s2 => inversion_clear f
  | LongStep ?s1 (?h :: ?t) ?s2 =>
    let s1 := fresh "s" in
    let s2 := fresh "s" in
    let s3 := fresh "s" in
    let te := fresh "te" in
    let tail := fresh "tail" in
    let Hcr := fresh "Hcr" in
    let Htl := fresh "Htl" in
    inversion_clear f as [|s1 s2 s3 te tail Hcr Htl];
    unfold_trace Htl
  end.

Section tests.
  Generalizable Variables ST TE.

  Goal forall `{StateSpace ST TE} s s' (te : TE), LongStep s [te; te; te] s' -> True.
    intros.
    unfold_trace H0.
  Abort.
End tests.
