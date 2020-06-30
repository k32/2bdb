Ltac symm_not :=
  let H := fresh
  in unfold not;
     intros H;
     symmetry in H;
     generalize dependent H.
