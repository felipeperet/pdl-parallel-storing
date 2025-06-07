import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Relation
import PdlParallelStoring.Syntax

----------------------------------------------------------------------------------------------------
-- PDL Semantics
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
-- Basic Semantic Structures
----------------------------------------------------------------------------------------------------

 -- Def) A frame is a pair F = (W, {Rπ : π is a program})
 --      where:
 --        - W is a non-empty set,
 --        - Rπ ⊆ W × W , for each program π.
 structure Frame where
   W : Type
   nonempty : Nonempty W
   R : π → W → W → Prop

-- Def) A model is a pair M = (F, V)
--      where:
--        - F is a frame,
--        - V : Φ → 2W is a valuation function mapping proposition symbols into subsets of W.
structure Model where
  frame : Frame
  V : (Ψ → frame.W → Prop)

-- Def) Satisfaction relation.
def satisfies (M : Model) (w : M.frame.W) : Φ → Prop
  | Φ.false => False
  | Φ.atomic φ => M.V φ w
  | Φ.neg φ => ¬ (satisfies M w φ)
  | Φ.conj φ₁ φ₂ => (satisfies M w φ₁) ∧ (satisfies M w φ₂)
  | Φ.diamond α φ => ∃ w', M.frame.R α w w' ∧ satisfies M w' φ

-- Sugar syntax for satisfaction.
notation:20 M "," w "⊨" φ => satisfies M w φ

----------------------------------------------------------------------------------------------------
-- Standard Model
----------------------------------------------------------------------------------------------------
-- Helper Relations for Standard Model Conditions in PDL:

-- Def) Relational composition: R₁ ; R₂
def relComp {W : Type} (R₁ R₂ : W → W → Prop) : W → W → Prop :=
  λ w₁ w₃ => ∃ w₂, R₁ w₁ w₂ ∧ R₂ w₂ w₃

-- Def) Relational union: R₁ ∪ R₂
def relUnion {W : Type} (R₁ R₂ : W → W → Prop) : W → W → Prop :=
  λ w₁ w₂ => R₁ w₁ w₂ ∨ R₂ w₁ w₂

-- Def) Reflexive transitive closure: R*
def relStar {W : Type} (R : W → W → Prop) : W → W → Prop :=
  λ (w₁ w₂) => Relation.ReflTransGen R w₁ w₂

-- Def) Test relation: {(w,w) ∈ W² : M, w ⊨ φ}
def relTest (M : Model) (φ : Φ) : M.frame.W → M.frame.W → Prop :=
  λ w₁ w₂ => (w₁ = w₂) ∧ (M, w₁ ⊨ φ)

-- A model is standard when it satisfies the following conditions:
def isStandardModel (M : Model) : Prop :=
  (∀ α β, M.frame.R (α ; β) = relComp (M.frame.R α) (M.frame.R β)) ∧
  (∀ α β, M.frame.R (α ∪ β) = relUnion (M.frame.R α) (M.frame.R β)) ∧
  (∀ α, M.frame.R (α *) = relStar (M.frame.R α)) ∧
  (∀ φ, M.frame.R (? (φ)) = relTest M φ)

----------------------------------------------------------------------------------------------------
-- PRSPDL Semantics
----------------------------------------------------------------------------------------------------
-- Def) A set of structured states is a triple (S, E, ⋆)
--      where:
--        - S is a non-empty set,
--        - E is an equivalence relation on S,
--        - ⋆ : S² → S is injective (s₁ ⋆ s₂ = t₁ ⋆ t₂ ↔ s₁ = t₁ ∧ s₂ = t₂).
structure StructuredState where
  S : Type
  nonempty : Nonempty S
  E : S → S → Prop
  equiv : Equivalence E
  star : S → S → S
  inject : Function.Injective (λ (p : S × S) => star p.1 p.2)

-- Def) A structured frame is a pair F = ((S, E ⋆), {Rπ : π is a program})
--      where:
--        - (S, E, ⋆) is a set of structured states,
--        - Rπ ⊆ E, for each program π,
--        - (S, {Rπ : π is a program}) is a frame.
structure StructuredFrame where
  structStates : StructuredState
  R : π → structStates.S → structStates.S → Prop
  respects_equiv : ∀ π s₁ s₂, R π s₁ s₂ → structStates.E s₁ s₂

-- Def) A structured frame F is proper when it satisfies the following conditions:
def isProperStructuredFrame (F : StructuredFrame) : Prop :=
  let R := F.R
  let star := F.structStates.star
  (∀ s' t', R π.s₁ s' t' ↔ ∃ s t, (s' = s) ∧ (t' = star s t)) ∧
  (∀ s' t', R π.s₂ s' t' ↔ ∃ s t, (s' = t) ∧ (t' = star s t)) ∧
  (∀ s' t', R π.r₁ s' t' ↔ ∃ s t, (s' = star s t) ∧ (t' = s)) ∧
  (∀ s' t', R π.r₂ s' t' ↔ ∃ s t, (s' = star s t) ∧ (t' = t)) ∧
  (∀ π₁ π₂ s' t', R (π₁ ‖ π₂) s' t' ↔ ∃ s₁ t₁ s₂ t₂, (s' = star s₁ t₁) ∧ (t' = star s₂ t₂) ∧
    R π₁ s₁ s₂ ∧
    R π₂ t₁ t₂)
