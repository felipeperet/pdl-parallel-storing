import Mathlib.Logic.Relation

import PdlParallelStoring.Syntax

open Program

----------------------------------------------------------------------------------------------------
-- PDL Semantics
----------------------------------------------------------------------------------------------------

/-- A frame is a pair F = (W, {Rπ : π is a program}) where:
      - W is a non-empty set,
      - Rπ ⊆ W × W, for each program π.
-/
structure Frame where
  W : Type
  [nonempty : Nonempty W]
  R : Program → W → W → Prop

/-- A model is a pair M = (F, V) where:
      - F is a frame,
      - V : Φ → 2^W is a valuation function mapping atomic formulae into subsets of W.
-/
structure Model where
  F : Frame
  V : Literal → F.W → Prop

/-- Satisfaction relation.
    (M, w) ⊨ φ holds when formula φ is true at world w in model M.

    (M, w) ⊨ φ is inductively defined as follows:
      - ⊥ is never satisfied,
      - an atom p is satisfied iff w ∈ V(p),
      - ¬ φ is satisfied iff φ is not satisfied,
      - φ₁ ∧ φ₂ is satisfied iff both φ₁ and φ₂ are satisfied,
      - ⟨α⟩ φ is satisfied iff there exists w' with R(α)(w, w') and (M, w') ⊨ φ.
-/
def satisfies (M : Model) (w : M.F.W) : Formula → Prop
  | Formula.false => False
  | Formula.atom ψ => M.V ψ w
  | Formula.neg φ => ¬ satisfies M w φ
  | Formula.conj φ₁ φ₂ => satisfies M w φ₁ ∧ satisfies M w φ₂
  | Formula.diamond α φ => ∃ w', M.F.R α w w' ∧ satisfies M w' φ

notation:40 "(" κ ", " s ") " " ⊨ " φ => satisfies κ s φ

/-- A model is standard₀ when composition and choice have their standard PDL semantics:
      - R(α ; β) = R(α) ∘ R(β)  (relational composition),
      - R(α ∪ β)(w₁, w₂) iff R(α)(w₁, w₂) ∨ R(β)(w₁, w₂).
-/
class Standard₀ (M : Model) where
  comp : ∀ {α β}, M.F.R (α ; β) = Relation.Comp (M.F.R α) (M.F.R β)
  choice : ∀ {α β}, M.F.R (α ∪ β) = λ w₁ w₂ => M.F.R α w₁ w₂ ∨ M.F.R β w₁ w₂

/-- A model is standard when it extends Standard₀ with iteration and test:
      - R(α *) = R(α) * (reflexive-transitive closure),
      - R(φ ?)(w₁, w₂) iff w₁ = w₂ ∧ (M, w₁) ⊨ φ.
-/
class Standard (M : Model) extends Standard₀ M where
  iter : ∀ {α}, M.F.R (α *) = Relation.ReflTransGen (M.F.R α)
  test : ∀ {φ}, M.F.R (φ ?) = λ w₁ w₂ => (w₁ = w₂) ∧ (satisfies M w₁ φ)

----------------------------------------------------------------------------------------------------
-- PRSPDL Semantics
----------------------------------------------------------------------------------------------------

/-- A set of structured states is a triple (S, E, ⋆) where:
      - S is a non-empty set,
      - E is an equivalence relation on S,
      - ⋆ : S × S → S is injective (s₁ ⋆ s₂ = t₁ ⋆ t₂ ↔ s₁ = t₁ ∧ s₂ = t₂).
-/
class State (S : Type) where
  [nonempty : Nonempty S]
  E : S → S → Prop
  [equiv : Equivalence E]
  star : S → S → S
  [inject : ∀ {s₁ t₁ s₂ t₂}, (star s₁ t₁ = star s₂ t₂) ↔ (s₁ = s₂) ∧ t₁ = t₂]

infix:50 " ≈ " => State.E
infixr:85 " ⋆ " => State.star

/-- A structured frame is a pair F = ((S, E, ⋆), {Rπ : π is a program}) where:
      - (S, E, ⋆) is a set of structured states,
      - Rπ ⊆ E for each program π (every transition relates equivalent states),
      - (S, {Rπ}) forms a frame.
-/
class Structured (F : Frame) where
  [S : State F.W]
  respects_equiv : ∀ {π s t}, F.R π s t → s ≈ t

instance {F : Frame} [SF : Structured F] : State F.W := SF.S

/-- A proper frame is a structured frame where the store/retrieve programs have their
    intended semantics:
      - R(s₁)(s', t') iff ∃ s t, s' = s ∧ t' = s ⋆ t  (store into first coordinate),
      - R(s₂)(s', t') iff ∃ s t, s' = t ∧ t' = s ⋆ t  (store into second coordinate),
      - R(r₁)(s', t') iff ∃ s t, s' = s ⋆ t ∧ t' = s  (retrieve first coordinate),
      - R(r₂)(s', t') iff ∃ s t, s' = s ⋆ t ∧ t' = t  (retrieve second coordinate).
-/
class Proper (F : Frame) extends Structured F where
  s₁ : ∀ {s' t'}, F.R s₁ s' t' ↔ ∃ s t, (s' = s) ∧ t' = s ⋆ t
  s₂ : ∀ {s' t'}, F.R s₂ s' t' ↔ ∃ s t, (s' = t) ∧ t' = s ⋆ t
  r₁ : ∀ {s' t'}, F.R r₁ s' t' ↔ ∃ s t, (s' = s ⋆ t) ∧ t' = s
  r₂ : ∀ {s' t'}, F.R r₂ s' t' ↔ ∃ s t, (s' = s ⋆ t) ∧ t' = t

/-- A proper frame with parallel composition. Extends a proper frame with:
      - R(π₁ ‖ π₂)(s', t') iff
        ∃ s₁ t₁ s₂ t₂, s' = s₁ ⋆ t₁ ∧ t' = s₂ ⋆ t₂ ∧ R(π₁)(s₁, s₂) ∧ R(π₂)(t₁, t₂).
-/
class ProperParallel (F : Frame) extends Proper F where
  parallel : ∀ {π₁ π₂ s' t'}, F.R (π₁ ‖ π₂) s' t' ↔
    ∃ s₁ t₁ s₂ t₂, (s' = s₁ ⋆ t₁) ∧ (t' = s₂ ⋆ t₂) ∧
    F.R π₁ s₁ s₂ ∧ F.R π₂ t₁ t₂

/-- A proper standard₀ model: a proper frame equipped with a valuation, where composition
    and choice have their standard PDL semantics. This is the semantic class for RSPDL₀.
-/
class ProperStandard₀ (M : Model) extends Standard₀ M, Proper M.F

/-- A proper parallel standard model: a proper frame with parallel composition, equipped with
    a valuation, where all program constructors (composition, choice, iteration, test, and
    parallel composition) have their standard semantics. This is the semantic class for PRSPDL.
-/
class ProperParallelStandard (M : Model) extends Standard M, ProperParallel M.F

/-- Global satisfaction: φ is globally satisfied in M when (M, w) ⊨ φ for every world w.
-/
def globallySatisfies (M : Model) [ProperStandard₀ M] (φ : Formula) :=
  ∀ {w : M.F.W}, (M, w) ⊨ φ

notation:40 M " ⊨ " φ => globallySatisfies M φ

/-- Validity in a proper frame: φ is valid in F when it is globally satisfied in every
    proper standard₀ model whose underlying frame is F.
-/
def validInProperFrame (F : Frame) [Proper F] (φ : Formula) : Prop :=
  ∀ {M : Model} [ProperStandard₀ M], (M.F = F) → M ⊨ φ

notation:40 F " ⊨ " φ => validInProperFrame F φ

/-- Global validity: φ is valid when it is valid in every proper frame.
-/
def valid (φ : Formula) : Prop :=
  ∀ {F : Frame} [Proper F], F ⊨ φ

notation:40 "⊨ " φ => valid φ

/-- Semantic equivalence: φ₁ ≡ φ₂ when φ₁ ↔ φ₂ is valid.
-/
def semEquiv (φ₁ φ₂ : Formula) : Prop :=
  ⊨ (φ₁ ↔ φ₂)

infixl:50 " ≡ " => semEquiv

----------------------------------------------------------------------------------------------------
-- Properties of Proper Frames
----------------------------------------------------------------------------------------------------

/-- Property I) R(s₁) ; R(r₁) = Id.

    Storing into the first coordinate and then retrieving the first coordinate yields the
    identity. -/
@[simp]
lemma s₁_comp_r₁ (F : Frame) [P : Proper F] : ∀ {s u : F.W},
    Relation.Comp (F.R s₁) (F.R r₁) s u ↔ s = u := by
  intros s u
  constructor
  . intro hcomp
    obtain ⟨t, hs₁, hr₁⟩ := hcomp
    rewrite [P.s₁] at hs₁
    rewrite [P.r₁] at hr₁
    obtain ⟨s₁, t₁, hs_eq, ht_eq⟩ := hs₁
    obtain ⟨s₂, t₂, ht_eq₂, hu_eq⟩ := hr₁
    have h_eq : s₁ ⋆ t₁ = s₂ ⋆ t₂ := by rw [← ht_eq, ht_eq₂]
    have s₁_eq_s₂ : s₁ = s₂ := (State.inject.mp h_eq).1
    rewrite [hs_eq, hu_eq]
    exact s₁_eq_s₂
  . intro h_eq
    use s ⋆ s
    simp [P.s₁, P.r₁]
    use u
    rw [h_eq]

/-- Property II) R(s₂) ; R(r₂) = Id.

    Storing into the second coordinate and then retrieving the second coordinate yields the
    identity. -/
@[simp]
lemma s₂_comp_r₂ (F : Frame) [P : Proper F] : ∀ {s u : F.W},
    Relation.Comp (F.R s₂) (F.R r₂) s u ↔ s = u := by
  intros s u
  constructor
  . intro hcomp
    obtain ⟨t, hs₂, hr₂⟩ := hcomp
    rewrite [P.s₂] at hs₂
    rewrite [P.r₂] at hr₂
    obtain ⟨s₁, t₁, hs_eq, ht_eq⟩ := hs₂
    obtain ⟨s₂, t₂, ht_eq₂, hu_eq⟩ := hr₂
    have h_eq : s₁ ⋆ t₁ = s₂ ⋆ t₂ := by rw [← ht_eq, ht_eq₂]
    have t₁_eq_t₂ : t₁ = t₂ := (State.inject.mp h_eq).2
    rewrite [hs_eq, hu_eq]
    exact t₁_eq_t₂
  . intro h_eq
    use s ⋆ s
    simp [P.s₂, P.r₂]
    constructor <;> use u <;> rw [h_eq]

/-- Property III) R(s₁) ; R(r₂) = E.

    Storing into the first coordinate and then retrieving the second coordinate relates exactly
    the E-equivalent states. -/
@[simp]
lemma s₁_comp_r₂ (F : Frame) [P : Proper F] : ∀ {s t : F.W},
    Relation.Comp (F.R s₁) (F.R r₂) s t ↔ s ≈ t := by
  intros s t
  constructor
  . intro hcomp
    obtain ⟨_, hs₁, hr₂⟩ := hcomp
    rewrite [P.s₁, P.r₂] at *
    obtain ⟨s₁, t₁, hs_eq, hu_eq⟩ := hs₁
    obtain ⟨s₂, t₂, hu_eq₂, ht_eq⟩ := hr₂
    have h_eq : s₁ ⋆ t₁ = s₂ ⋆ t₂ := by rw [← hu_eq, hu_eq₂]
    have ⟨_, t₁_eq_t₂⟩ := State.inject.mp h_eq
    rewrite [hs_eq, ht_eq, ← t₁_eq_t₂]
    have h₁ : s₁ ≈ (s₁ ⋆ t₁) := by
      apply Structured.respects_equiv
      rewrite [P.s₁]
      use s₁, t₁
    have h₂ : t₁ ≈ (s₁ ⋆ t₁) := by
      apply Structured.respects_equiv
      rewrite [P.s₂]
      use s₁, t₁
    have h₃ : (s₁ ⋆ t₁) ≈ t₁ := State.equiv.symm h₂
    exact State.equiv.trans h₁ h₃
  . intro _
    use s ⋆ t
    rewrite [P.s₁, P.r₂] at *
    constructor
    . use s, t
    . use s, t

/-- Property IV) (R(r₁) ; R(s₁)) ∩ (R(r₂) ; R(s₂)) ⊆ Id.

    If two states are related by both retrieve-then-store compositions, they must be equal. -/
@[simp]
lemma r₁_s₁_inter_r₂_s₂ (F : Frame) [P : Proper F] : ∀ {s t : F.W},
    (Relation.Comp (F.R r₁) (F.R s₁) s t ∧ Relation.Comp (F.R r₂) (F.R s₂) s t) →
    s = t := by
  intros s t hcomp
  obtain ⟨hcomp₁, hcomp₂⟩ := hcomp
  obtain ⟨i₁, hr₁, hs₁⟩ := hcomp₁
  obtain ⟨i₂, hr₂, hs₂⟩ := hcomp₂
  rewrite [P.s₁, P.s₂, P.r₁, P.r₂] at *
  obtain ⟨s₁, t₁, hs_eq₁, hi₁_eq₁⟩ := hr₁
  obtain ⟨s₂, t₂, hi₁_eq₂, ht_eq₁⟩ := hs₁
  obtain ⟨s₃, t₃, hs_eq₂, hi₂_eq₁⟩ := hr₂
  obtain ⟨s₄, t₄, hi₂_eq₂, ht_eq₂⟩ := hs₂
  conv at ht_eq₂ =>
    rhs
    arg 2
    rewrite [← hi₂_eq₂, hi₂_eq₁]
  conv at ht_eq₁ =>
    rhs
    arg 1
    rewrite [← hi₁_eq₂, hi₁_eq₁]
  have h₁ : s₁ ⋆ t₁ = s₃ ⋆ t₃ := by rw [← hs_eq₁, hs_eq₂]
  have ⟨_, t₁_eq_t₃⟩ := State.inject.mp h₁
  have h₂ : s₁ ⋆ t₂ = s₄ ⋆ t₃ := by rw [← ht_eq₁, ht_eq₂]
  have ⟨_, t₂_eq_t₃⟩ := State.inject.mp h₂
  have t₁_eq_t₂ : t₁ = t₂ := by rw [t₁_eq_t₃, ← t₂_eq_t₃]
  rw [hs_eq₁, ht_eq₁, ← t₁_eq_t₂]

/-- Property V) R(r₁) ; E = R(r₂) ; E.

    Retrieving either coordinate and then stepping by equivalence yields the same relation. -/
@[simp]
lemma r₁_E_eq_r₂_E (F : Frame) [P : Proper F] : ∀ {s t : F.W},
    Relation.Comp (F.R r₁) State.E s t ↔ Relation.Comp (F.R r₂) State.E s t := by
  intros s t
  constructor
  . intros comp
    obtain ⟨i, hr₁, equiv⟩ := comp
    rewrite [P.r₁] at hr₁
    obtain ⟨s₁, t₁, s_eq, i_eq⟩ := hr₁
    use t₁
    constructor
    . rewrite [P.r₂, s_eq]
      use s₁, t₁
    . rewrite [← s₁_comp_r₂]
      use t₁ ⋆ t
      constructor
      . rewrite [P.s₁]
        use t₁, t
      . rewrite [P.r₂]
        use t₁, t
  . intros comp
    obtain ⟨i, hr₂, equiv⟩ := comp
    rewrite [P.r₂] at hr₂
    obtain ⟨s₁, t₁, s_eq, i_eq⟩ := hr₂
    use s₁
    constructor
    . rewrite [s_eq, P.r₁]
      use s₁, t₁
    . rewrite [← s₁_comp_r₂]
      use s₁ ⋆ t
      constructor
      . rewrite [P.s₁]
        use s₁, t
      . rewrite [P.r₂]
        use s₁, t
