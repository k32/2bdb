Definition eq_decP T := forall (a b : T), {a = b} + {a <> b}.

(** Type of values with decidable comparison operator *)
Record Keq_dec : Type :=
  { KT : Type;
    eq_dec : eq_decP KT;
  }.
