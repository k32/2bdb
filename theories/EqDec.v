Class EqDec T : Type :=
  { eq_dec : forall (a b : T), {a = b} + {a <> b};
  }.

Lemma eq_dec_same : forall A B `{EqDec A} (a : A) (b c : B),
    (if eq_dec a a then b else c) = b.
Proof with firstorder.
  intros. destruct (eq_dec a a)...
Qed.

Hint Rewrite eq_dec_same : eq_dec.
Hint Extern 3 ((if eq_dec ?X ?Y then _ else _) = _) => destruct (eq_dec ?X ?Y); subst; firstorder : eq_dec.
Hint Extern 3 (_ = (if eq_dec ?X ?Y then _ else _)) => destruct (eq_dec ?X ?Y); subst; firstorder : eq_dec.
