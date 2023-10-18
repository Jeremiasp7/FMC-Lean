
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
  intro p,
  by_contradiction hboom,
  by_cases h : P,
  have b : false := p hboom,
  exact b,
  have b : false := p hboom,
  exact b,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
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
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro pq,
  cases pq with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro pq,
  cases pq,
  split,
  exact pq_right,
  exact pq_left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro pq,
  intro p,
  cases pq with np q,
  by_contradiction hboom,
  have h : false := np p,
  contradiction,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro pq,
  intro np,
  cases pq with p q,
  by_contradiction hboom,
  have b : false := np p,
  contradiction,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro pq,
  intro nq,
  intro np,
  have q : Q := pq np,
  have b : false := nq q,
  exact b,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro nqnp,
  intro p,
  by_contradiction hboom,
  apply nqnp,
  exact hboom,
  exact p,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
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
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  by_cases h : P,
  intro pp,
  apply pp,
  left,
  exact h,
  intro pp,
  apply pp,
  right,
  exact h,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro pqp,
  intro np,
  apply np,
  apply pqp,
  intro p,
  have b : false := np p,
  exfalso,
  exact b,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro pq,
  intro npnq,
  cases pq with p q,
  cases npnq,
  apply npnq_left,
  exact p,
  cases npnq,
  apply npnq_right,
  exact q,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro pq,
  intro npnq,
  cases pq,
  cases npnq with np nq,
  apply np,
  exact pq_left,
  apply nq,
  apply pq_right,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro pq,
  split,
  intro p,
  apply pq,
  left,
  exact p,
  intro q,
  apply pq,
  right,
  exact q,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npnq,
  intro pq,
  cases npnq,
  cases pq with p q,
  apply npnq_left,
  exact p,
  apply npnq_right,
  exact q,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro pq,
  by_contradiction,
  apply pq,
  split,
  by_contradiction p,
  apply h,
  right,
  exact p,
  by_contradiction q,
  apply h,
  left,
  exact q,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqnp,
  intro pq,
  cases pq,
  cases nqnp with nq np,
  apply nq,
  exact pq_right,
  apply np,
  exact pq_left,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro pq,
  by_contradiction,
  apply pq,
  split,
  by_contradiction p,
  apply h,
  right,
  exact p,
  by_contradiction q,
  apply h,
  left,
  exact q,
  intro nqnp,
  intro pq,
  cases pq,
  cases nqnp with nq np,
  apply nq,
  exact pq_right,
  apply np,
  exact pq_left,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro pq,
  split,
  intro p,
  apply pq,
  left,
  exact p,
  intro q,
  apply pq,
  right,
  exact q,
  intro npnq,
  intro pq,
  cases npnq,
  cases pq with p q,
  apply npnq_left,
  exact p,
  apply npnq_right,
  exact q,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pqr,
  cases pqr,
  cases pqr_right with q r,
  left,
  split,
  exact pqr_left,
  exact q,
  right,
  split,
  exact pqr_left,
  exact r,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro h,
  split,
  cases h with pq pr,
  cases pq,
  exact pq_left,
  cases pr,
  exact pr_left,
  cases h with pq pr,
  cases pq,
  left,
  exact pq_right,
  cases pr,
  right,
  exact pr_right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pqr,
  split,
  cases pqr,
  left,
  exact pqr,
  cases pqr with q r,
  right,
  exact q,
  cases pqr,
  left,
  exact pqr,
  cases pqr,
  right,
  exact pqr_right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pqpr,
  cases pqpr,
  cases pqpr_left,
  left,
  exact pqpr_left,
  cases pqpr_right,
  left,
  exact pqpr_right,
  right,
  split,
  exact pqpr_left,
  exact pqpr_right,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pqr,
  intro p,
  intro q,
  apply pqr,
  split,
  exact p,
  exact q,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro pqr,
  intro pq,
  cases pq,
  apply pqr,
  exact pq_left,
  exact pq_right,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq,
  exact pq_left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq,
  exact pq_right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro p,
  cases p,
  exact p_left,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pp,
  cases pp with p p,
  exact p,
  exact p,
  intro p,
  left,
  exact p,
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
