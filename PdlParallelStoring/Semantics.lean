import PdlParallelStoring.Syntax

----------------------------------------------------------------------------------------------------
-- PRSPDL Semantics
----------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------
-- Basic Semantic Structures
----------------------------------------------------------------------------------------------------

 -- Def) A frame is a pair F = (W, {Rπ : π is a program})
 --      Where:
 --        - W is a non-empty set,
 --        - Rπ ⊆ W × W , for each program π.
 structure Frame where
   W : Type
   nonempty : Nonempty W
   R : π → W → W → Prop

-- Def) A model is a pair M = (F, V)
--      Where:
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

-- Helper Relations for Standard Model Conditions:

-- Def) Relational composition: R₁ ; R₂
def relComp {W : Type} (R₁ R₂ : W → W → Prop) : W → W → Prop :=
  λ w₁ w₃ => ∃ w₂, R₁ w₁ w₂ ∧ R₂ w₂ w₃

-- Def) Relational union: R₁ ∪ R₂
def relUnion {W : Type} (R₁ R₂ : W → W → Prop) : W → W → Prop :=
  λ w₁ w₂ => R₁ w₁ w₂ ∨ R₂ w₁ w₂

-- Def) Reflexive transitive closure: R*
def relStar {W : Type} (R : W → W → Prop) : W → W → Prop :=
  λ (w₁ w₂) => (w₁ = w₂) ∨ Relation.TransGen R w₁ w₂

-- Def) Test relation: {(w,w) ∈ W² : M, w ⊨ φ}
def relTest (M : Model) (φ : Φ) : M.frame.W → M.frame.W → Prop :=
  λ w₁ w₂ => (w₁ = w₂) ∧ (M, w₁ ⊨ φ)

-- A model is standard when it satisfies the following conditions:
def isStandardModel (M : Model) : Prop :=
  (∀ α β, M.frame.R (α ; β) = relComp (M.frame.R α) (M.frame.R β)) ∧
  (∀ α β, M.frame.R (α ∪ β) = relUnion (M.frame.R α) (M.frame.R β)) ∧
  (∀ α, M.frame.R (α ⋆) = relStar (M.frame.R α)) ∧
  (∀ φ, M.frame.R (? (φ)) = relTest M φ)
