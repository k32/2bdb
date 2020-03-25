Class EqDec T : Type :=
  { eq_dec : forall (a b : T), {a = b} + {a <> b};
  }.
