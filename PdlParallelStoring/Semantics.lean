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
      - φ ∧ ψ is satisfied iff both φ and ψ are satisfied,
      - ⟨α⟩ φ is satisfied iff there exists w' with R(α)(w, w') and (M, w') ⊨ φ.
-/
def satisfies (M : Model) (w : M.F.W) : Formula → Prop
  | Formula.false => False
  | Formula.atom p => M.V p w
  | Formula.neg φ => ¬ satisfies M w φ
  | Formula.conj φ ψ => satisfies M w φ ∧ satisfies M w ψ
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
      - ⋆ : S × S → 𝒫(S) associates each pair of states with a set of possible combinations,
      - ⋆ is separated: if t ∈ w ⋆ s and t ∈ w' ⋆ s', then w = w' and s = s'
                        (each state has at most one decomposition),
      - ⋆ is serial: for all w s, there exists t ∈ w ⋆ s
                     (every pair of states can be combined).
-/
class State (S : Type) where
  [nonempty : Nonempty S]
  E : S → S → Prop
  [equiv : Equivalence E]
  star : S → S → Set S
  [separated : ∀ {t w s w' s'}, (t ∈ star w s) → (t ∈ star w' s') → (w = w') ∧ s = s']
  [serial : ∀ (w s : S), ∃ t, t ∈ star w s]

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
      - R(s₁)(s', t') iff ∃ s t, s' = s ∧ t' ∈ s ⋆ t  (store into first coordinate),
      - R(s₂)(s', t') iff ∃ s t, s' = t ∧ t' ∈ s ⋆ t  (store into second coordinate),
      - R(r₁)(s', t') iff ∃ s t, s' ∈ s ⋆ t ∧ t' = s  (retrieve first coordinate),
      - R(r₂)(s', t') iff ∃ s t, s' ∈ s ⋆ t ∧ t' = t  (retrieve second coordinate).

    Note: with set-valued ⋆, the store programs are non-deterministic (there may be
    multiple ways to combine two states), while the retrieve programs are deterministic
    (each combined state has at most one decomposition, by the separated condition).
-/
class Proper (F : Frame) extends Structured F where
  s₁ : ∀ {s' t'}, F.R s₁ s' t' ↔ ∃ s t, (s' = s) ∧ t' ∈ s ⋆ t
  s₂ : ∀ {s' t'}, F.R s₂ s' t' ↔ ∃ s t, (s' = t) ∧ t' ∈ s ⋆ t
  r₁ : ∀ {s' t'}, F.R r₁ s' t' ↔ ∃ s t, (s' ∈ s ⋆ t) ∧ t' = s
  r₂ : ∀ {s' t'}, F.R r₂ s' t' ↔ ∃ s t, (s' ∈ s ⋆ t) ∧ t' = t

/-- A proper frame with parallel composition. Extends a proper frame with:
      - R(π₁ ‖ π₂)(s', t') iff
        ∃ s₁ t₁ s₂ t₂, s' ∈ s₁ ⋆ t₁ ∧ t' ∈ s₂ ⋆ t₂ ∧ R(π₁)(s₁, s₂) ∧ R(π₂)(t₁, t₂).
-/
class ProperParallel (F : Frame) extends Proper F where
  parallel : ∀ {π₁ π₂ s' t'}, F.R (π₁ ‖ π₂) s' t' ↔
    ∃ s₁ t₁ s₂ t₂, (s' ∈ s₁ ⋆ t₁) ∧ (t' ∈ s₂ ⋆ t₂) ∧ F.R π₁ s₁ s₂ ∧ F.R π₂ t₁ t₂

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
    obtain ⟨s₁, t₁, rfl, ht_mem⟩ := hs₁
    obtain ⟨s₂, t₂, ht_mem₂, rfl⟩ := hr₁
    exact (State.separated ht_mem ht_mem₂).1
  . intro h_eq
    subst h_eq
    obtain ⟨z, hz⟩ := State.serial s s
    exact ⟨z, P.s₁.mpr ⟨s, s, rfl, hz⟩, P.r₁.mpr ⟨s, s, hz, rfl⟩⟩

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
    obtain ⟨s₁, t₁, rfl, ht_mem⟩ := hs₂
    obtain ⟨s₂, t₂, ht_mem₂, rfl⟩ := hr₂
    exact (State.separated ht_mem ht_mem₂).2
  . intro h_eq
    subst h_eq
    obtain ⟨z, hz⟩ := State.serial s s
    exact ⟨z, P.s₂.mpr ⟨s, s, rfl, hz⟩, P.r₂.mpr ⟨s, s, hz, rfl⟩⟩

/-- Property III) R(s₁) ; R(r₂) = E.

    Storing into the first coordinate and then retrieving the second coordinate relates
    exactly the E-equivalent states. -/
@[simp]
lemma s₁_comp_r₂ (F : Frame) [P : Proper F] : ∀ {s t : F.W},
    Relation.Comp (F.R s₁) (F.R r₂) s t ↔ s ≈ t := by
  intros s t
  constructor
  . intro hcomp
    obtain ⟨z, hs₁, hr₂⟩ := hcomp
    rewrite [P.s₁] at hs₁
    rewrite [P.r₂] at hr₂
    obtain ⟨a, b, rfl, hz_mem⟩ := hs₁
    obtain ⟨c, d, hz_mem₂, rfl⟩ := hr₂
    have ⟨_, h_eq⟩ := State.separated hz_mem hz_mem₂
    subst h_eq
    have h₁ : s ≈ z := Structured.respects_equiv (P.s₁.mpr ⟨s, b, rfl, hz_mem⟩)
    have h₂ : b ≈ z := Structured.respects_equiv (P.s₂.mpr ⟨s, b, rfl, hz_mem⟩)
    exact State.equiv.trans h₁ (State.equiv.symm h₂)
  . intro _
    obtain ⟨z, hz⟩ := State.serial s t
    exact ⟨z, P.s₁.mpr ⟨s, t, rfl, hz⟩, P.r₂.mpr ⟨s, t, hz, rfl⟩⟩
