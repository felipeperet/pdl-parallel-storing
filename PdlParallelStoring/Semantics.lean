import Mathlib.Logic.Relation

import PdlParallelStoring.Syntax

open Program

----------------------------------------------------------------------------------------------------
-- PDL Semantics
----------------------------------------------------------------------------------------------------
-- Def) A frame is a pair F = (W, {Rπ : π is a program})
--      where:
--        - W is a non-empty set,
--        - Rπ ⊆ W × W , for each program π.
structure Frame where
  W : Type
  [nonempty : Nonempty W]
  R : Program → W → W → Prop

-- Def) A model is a pair M = (F, V)
--      where:
--        - F is a frame,
--        - V : Φ → 2^W is a valuation function mapping atomic formulae into subsets of W.
structure Model where
  F : Frame
  V : Literal → F.W → Prop

-- Def) Satisfaction relation.
def satisfies (M : Model) (w : M.F.W) : Formula → Prop
  | Formula.false => False
  | Formula.atom ψ => M.V ψ w
  | Formula.neg φ => ¬ satisfies M w φ
  | Formula.conj φ₁ φ₂ => satisfies M w φ₁ ∧ satisfies M w φ₂
  | Formula.diamond α φ => ∃ w', M.F.R α w w' ∧ satisfies M w' φ

notation:40 "(" κ ", " s ") " " ⊨ " φ => satisfies κ s φ

-- Def) A model is standard when it satisfies the following conditions:
class Standard (M : Model) where
  comp : ∀ {α β}, M.F.R (α ; β) = Relation.Comp (M.F.R α) (M.F.R β)
  choice : ∀ {α β}, M.F.R (α ∪ β) = λ w₁ w₂ => M.F.R α w₁ w₂ ∨ M.F.R β w₁ w₂
  iter : ∀ {α}, M.F.R (α ★) = Relation.ReflTransGen (M.F.R α)
  test : ∀ {φ}, M.F.R (φ ?) = λ w₁ w₂ => (w₁ = w₂) ∧ (satisfies M w₁ φ)

----------------------------------------------------------------------------------------------------
-- PRSPDL Semantics
----------------------------------------------------------------------------------------------------
-- Def) A set of structured states is a triple (S, E, ⋆)
--      where:
--        - S is a non-empty set,
--        - E is an equivalence relation on S,
--        - ⋆ : S² → S is injective (s₁ ⋆ s₂ = t₁ ⋆ t₂ ↔ s₁ = t₁ ∧ s₂ = t₂).
class State (S : Type) where
  [nonempty : Nonempty S]
  E : S → S → Prop
  [equiv : Equivalence E]
  star : S → S → S
  [inject : ∀ {s₁ t₁ s₂ t₂}, (star s₁ t₁ = star s₂ t₂) ↔ (s₁ = s₂) ∧ t₁ = t₂]

infix:50 " ≈ " => State.E
infixr:85 " ⋆ " => State.star

-- Def) A structured frame is a pair F = ((S, E ⋆), {Rπ : π is a program})
--      where:
--        - (S, E, ⋆) is a set of structured states,
--        - Rπ ⊆ E, for each program π,
--        - (S, {Rπ : π is a program}) is a frame.
class Structured (F : Frame) where
  [S : State F.W]
  respects_equiv : ∀ {π s t}, F.R π s t → s ≈ t

instance {F : Frame} [SF : Structured F] : State F.W := SF.S

-- Def) A structured frame F is proper when it satisfies the following conditions:
class Proper (F : Frame) extends Structured F where
  s₁ : ∀ {s' t'}, F.R s₁ s' t' ↔ ∃ s t, (s' = s) ∧ t' = s ⋆ t
  s₂ : ∀ {s' t'}, F.R s₂ s' t' ↔ ∃ s t, (s' = t) ∧ t' = s ⋆ t
  r₁ : ∀ {s' t'}, F.R r₁ s' t' ↔ ∃ s t, (s' = s ⋆ t) ∧ t' = s
  r₂ : ∀ {s' t'}, F.R r₂ s' t' ↔ ∃ s t, (s' = s ⋆ t) ∧ t' = t
  parallel : ∀ {π₁ π₂ s' t'}, F.R (π₁ ‖ π₂) s' t' ↔
    ∃ s₁ t₁ s₂ t₂, (s' = s₁ ⋆ t₁) ∧ (t' = s₂ ⋆ t₂) ∧
    F.R π₁ s₁ s₂ ∧ F.R π₂ t₁ t₂

-- Def) An PRSPDL model is a proper standard model.
class ProperStandard (M : Model) extends Standard M, Proper M.F

-- Def) Global satisfaction.
--      That is, the formula is satisfied in every possible state of a proper standard model.
def globallySatisfies (M : Model) [ProperStandard M] (φ : Formula) :=
  ∀ {w : M.F.W}, (M, w) ⊨ φ

notation:40 M " ⊨ " φ => globallySatisfies M φ

-- Def) Validity in a proper frame.
--      That is, a formula is satisfied in every possible model of a proper frame.
def validInProperFrame (F : Frame) [Proper F] (φ : Formula) : Prop :=
  ∀ {M : Model} [ProperStandard M], (M.F = F) → M ⊨ φ

notation:40 F " ⊨ " φ => validInProperFrame F φ

-- Def) Global validity.
--      That is, a formula is valid in every possible proper frame.
def valid (φ : Formula) : Prop :=
  ∀ {F : Frame} [Proper F], F ⊨ φ

notation:40 "⊨ " φ => valid φ

-- Def) Semantic equivalence.
def semEquiv (φ₁ φ₂ : Formula) : Prop :=
  ⊨ (φ₁ ↔ φ₂)

infixl:50 " ≡ " => semEquiv

----------------------------------------------------------------------------------------------------
-- Properties of Proper Structured Frames
----------------------------------------------------------------------------------------------------
-- Property I) Rs₁ ; Rr₁ = Id
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

-- Property II) Rs₂ ; Rr₂ = Id
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

-- Property III) Rs₁ ; Rr₂ = E
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

-- Property IV) (Rr₁ ; Rs₁) ∩ (Rr₂ ; Rs₂) ⊆ Id
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

-- Property V) Rr₁ ; E = Rr₂ ; E
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
