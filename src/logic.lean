
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro pb,
  have b : false := pb p,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
<<<<<<< HEAD
  intro p,
  by_contradiction hboom,
  by_cases h : P,
  have b : false := p hboom,
  exact b,
  have b : false := p hboom,
  exact b,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
<<<<<<< HEAD
  split,
  intro p,
  by_contradiction hboom,
  by_cases h : P,
  have b : false := p hboom,
  exact b,
  have b : false := p hboom,
  exact b,
  intro p,
  intro pb,
  have b : false := pb p,
  contradiction,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
<<<<<<< HEAD
  intro pq,
  cases pq with p q,
  right,
  exact p,
  left,
  exact q,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
<<<<<<< HEAD
  intro pq,
  cases pq,
  split,
  exact pq_right,
  exact pq_left,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
<<<<<<< HEAD
  intro pq,
  intro p,
  cases pq with np q,
  by_contradiction hboom,
  have h : false := np p,
  contradiction,
  exact q,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
<<<<<<< HEAD
  intro pq,
  intro np,
  cases pq with p q,
  by_contradiction hboom,
  have b : false := np p,
  contradiction,
  exact q,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
<<<<<<< HEAD
  intro pq,
  intro nq,
  intro np,
  have q : Q := pq np,
  have b : false := nq q,
  exact b,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
<<<<<<< HEAD
  intro nqnp,
  intro p,
  by_contradiction hboom,
  apply nqnp,
  exact hboom,
  exact p,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
<<<<<<< HEAD
  split,
  intro pq,
  intro nq,
  intro np,
  have q : Q := pq np,
  have b : false := nq q,
  exact b,
  intro nqnp,
  intro p,
  by_contradiction hboom,
  apply nqnp,
  exact hboom,
  exact p,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
<<<<<<< HEAD
  by_cases h : P,
  intro pp,
  apply pp,
  left,
  exact h,
  intro pp,
  apply pp,
  right,
  exact h,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
<<<<<<< HEAD
  intro pqp,
  intro np,
  apply np,
  apply pqp,
  intro p,
  have b : false := np p,
  exfalso,
  exact b,
=======
  sorry,
>>>>>>> 6a5cb529a223be050b3888aeeeb68128cf26973a
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  sorry,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  sorry,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  sorry,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  sorry,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  sorry,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  sorry,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  sorry,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  sorry,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  sorry,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  sorry,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  sorry,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  sorry,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  sorry,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  sorry,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  sorry,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  sorry,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  sorry,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  sorry,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  sorry,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  sorry,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro h,
  intro a,
  intro pa,
  apply h,
  existsi a,
  exact pa,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro a,
  intro h,
  cases h with b hb,
  apply a,
  exact hb,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro p,
  by_contradiction,
  apply p,
  intro a,
  by_contradiction j,
  apply h,
  existsi a,
  exact j,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro h,
  intro a,
  cases h with b hb,
  have j := a(b),
  apply hb,
  exact j,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  intro q,
  by_contradiction,
  apply q,
  intro b,
  by_contradiction p,
  apply h,
  existsi b,
  exact p,
  intro h,
  intro a,
  cases h with b hb,
  have j := a(b),
  apply hb,
  exact j,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  intro h,
  intro a,
  intro p,
  apply h,
  existsi a,
  exact p,
  intro a,
  intro h,
  cases h with b hb,
  have k := a(b),
  apply k,
  exact hb,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro q,
  intro a,
  cases q with b qb,
  have p := a(b),
  apply p,
  exact qb,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro a,
  intro h,
  cases h with b hb,
  have p := a(b),
  apply hb,
  exact p,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro h,
  intro a,
  by_contradiction j,
  apply h,
  existsi a,
  exact j,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro a,
  by_contradiction j,
  apply a,
  intro p,
  intro h,
  apply j,
  existsi p,
  exact h,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  intro a,
  intro h,
  cases h with b hb,
  have p := a(b),
  apply hb,
  exact p,
  intro h,
  intro a,
  by_contradiction j,
  apply h,
  existsi a,
  exact j,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  intro h,
  intro a,
  cases h with b hb,
  have p := a(b),
  apply p,
  exact hb,
  intro a,
  by_contradiction j,
  apply a,
  intro h,
  intro p,
  apply j,
  existsi h,
  exact p,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro h,
  split,
  cases h,
  existsi h_w,
  cases h_h,
  exact h_h_left,
  cases h,
  existsi h_w,
  cases h_h,
  exact h_h_right,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro h,
  cases h with b hb,
  cases hb with p q,
  left,
  existsi b,
  exact p,
  right,
  existsi b,
  exact q,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro a,
  cases a with p q,
  cases p with b hb,
  existsi b,
  left,
  exact hb,
  cases q with a ah,
  existsi a,
  right,
  exact ah,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro a,
  split,
  intro h,
  have p := a(h),
  cases p,
  exact p_left,
  intro h,
  have p := a(h),
  cases p,
  exact p_right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro aa,
  cases aa,
  intro a,
  split,
  have p := aa_left(a),
  exact p,
  have q := aa_right(a),
  exact q,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro aa,
  cases aa,
  intro a,
  left,
  have p := aa(a),
  exact p,
  intro a,
  right,
  have q := aa(a),
  exact q,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
