import Mathlib.Logic.Relation

import PdlParallelStoring.Syntax

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
  R : π → W → W → Prop

-- Def) A model is a pair M = (F, V)
--      where:
--        - F is a frame,
--        - V : Φ → 2^W is a valuation function mapping atomic formulae into subsets of W.
structure Model where
  F : Frame
  V : Ψ → F.W → Prop

-- Def) Satisfaction relation.
def satisfies (M : Model) (w : M.F.W) : Φ → Prop
  | Φ.false => False
  | Φ.atomic ψ => M.V ψ w
  | Φ.neg φ => ¬ satisfies M w φ
  | Φ.conj φ₁ φ₂ => satisfies M w φ₁ ∧ satisfies M w φ₂
  | Φ.diamond α φ => ∃ w', M.F.R α w w' ∧ satisfies M w' φ

notation:40 "(" κ "," s ") " " ⊨ " φ => satisfies κ s φ

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
infixr:85 "⋆" => State.star

-- Def) A structured frame is a pair F = ((S, E ⋆), {Rπ : π is a program})
--      where:
--        - (S, E, ⋆) is a set of structured states,
--        - Rπ ⊆ E, for each program π,
--        - (S, {Rπ : π is a program}) is a frame.
class Structured (F : Frame) where
  [S : State F.W]
  respects_equiv : ∀ {π s₁ s₂}, F.R π s₁ s₂ → s₁ ≈ s₂

instance {F : Frame} [SF : Structured F] : State F.W := SF.S

-- Def) A structured frame F is proper when it satisfies the following conditions:
class Proper (F : Frame) extends Structured F where
  s₁ : ∀ {s' t'}, F.R π.s₁ s' t' ↔ ∃ s t, (s' = s) ∧ t' = s ⋆ t
  s₂ : ∀ {s' t'}, F.R π.s₂ s' t' ↔ ∃ s t, (s' = t) ∧ t' = s ⋆ t
  r₁ : ∀ {s' t'}, F.R π.r₁ s' t' ↔ ∃ s t, (s' = s ⋆ t) ∧ t' = s
  r₂ : ∀ {s' t'}, F.R π.r₂ s' t' ↔ ∃ s t, (s' = s ⋆ t) ∧ t' = t
  parallel : ∀ {π₁ π₂ s' t'}, F.R (π₁ ‖ π₂) s' t' ↔
    ∃ s₁ t₁ s₂ t₂, (s' = s₁ ⋆ t₁) ∧ (t' = s₂ ⋆ t₂) ∧
    F.R π₁ s₁ s₂ ∧ F.R π₂ t₁ t₂

-- Def) An PRSPDL model is a proper standard model.
class ProperStandard (M : Model) extends Standard M, Structured M.F, Proper M.F

-- Def) Global satisfaction.
--      That is, the formula is satisfied in every possible state of a proper standard model.
def globallySatisfies (M : Model) [ProperStandard M] (φ : Φ) :=
  ∀ {w : M.F.W}, (M, w) ⊨ φ

notation:40 M " ⊨ " φ => globallySatisfies M φ

-- Def) Validity in a proper frame.
--      That is, a formula is satisfied in every possible model of a proper frame.
def validInProperFrame (F : Frame) [Proper F] (φ : Φ) : Prop :=
  ∀ {M : Model} [ProperStandard M], (M.F = F) → M ⊨ φ

notation:40 F " ⊨ " φ => validInProperFrame F φ

-- Def) Global validity.
--      That is, a formula is valid in every possible proper frame.
def valid (φ : Φ) : Prop := ∀ {F : Frame} [Proper F], F ⊨ φ

notation:40 "⊨ " φ => valid φ

-- Def) Semantic equivalence.
def semEquiv (φ₁ φ₂ : Φ) : Prop := ⊨ (φ₁ ↔ φ₂)

infixl:50 " ≡ " => semEquiv
