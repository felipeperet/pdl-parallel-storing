import Mathlib.Data.Finset.Basic

import PdlParallelStoring.AxiomaticSystem
import PdlParallelStoring.Properties

-- Predicates for formulae and programs in the RSPDL₀ fragment.
-- In this fragment, we do not allow the use of the operators of:
--   - test (?)
--   - iteration (★)
--   - parallel composition (‖).

inductive RSPDL0Program : π → Prop where
  | atomic α : RSPDL0Program (π.atomic α)
  | comp α β : RSPDL0Program α → RSPDL0Program β → RSPDL0Program (α ; β)
  | choice α β : RSPDL0Program α → RSPDL0Program β → RSPDL0Program (α ∪ β)
  | s₁ : RSPDL0Program π.s₁
  | s₂ : RSPDL0Program π.s₂
  | r₁ : RSPDL0Program π.r₁
  | r₂ : RSPDL0Program π.r₂

inductive RSPDL0Formula : Φ → Prop where
  | false : RSPDL0Formula ⊥'
  | atomic φ : RSPDL0Formula (Φ.atomic φ)
  | neg φ : RSPDL0Formula φ → RSPDL0Formula (¬ φ)
  | conj φ₁ φ₂ : RSPDL0Formula φ₁ → RSPDL0Formula φ₂ → RSPDL0Formula (φ₁ ∧ φ₂)
  | diamond π φ : RSPDL0Program π → RSPDL0Formula φ → RSPDL0Formula (⟨π⟩ φ)

def listToConjunction : List Φ → Φ
  | [] => ⊤'
  | [φ] => φ
  | φ :: φs => φ ∧ listToConjunction φs

noncomputable def finsetToConjunction (φs : Finset Φ) : Φ :=
  listToConjunction φs.toList

def IsConsistent (s : Set Φ) : Prop :=
  (∀ φ ∈ s, RSPDL0Formula φ) ∧
  ¬ ∃ (φs : Finset Φ), (∀ φ ∈ φs, φ ∈ s) ∧ (⊢ (finsetToConjunction φs → ⊥'))

def IsMaximal (s : Set Φ) : Prop :=
  IsConsistent s ∧
  ∀ {φ : Φ}, RSPDL0Formula φ → (φ ∉ s) → ¬ IsConsistent (s ∪ {φ})

def MaximalConsistentSet : Type :=
  {s : Set Φ // IsMaximal s}

def canonicalRelation (α : π) (Γ Δ : MaximalConsistentSet) : Prop :=
  ∀ φ, (([α] φ) ∈ Γ.val) → φ ∈ Δ.val

def canonicalFrame : Frame where
  W := MaximalConsistentSet
  R := canonicalRelation
  nonempty := sorry

def canonicalValuation (ψ : Ψ) (Γ : MaximalConsistentSet) : Prop :=
  Φ.atomic ψ ∈ Γ.val

def canonicalModel : Model where
  F := canonicalFrame
  V := canonicalValuation

instance canonicalProper : Proper canonicalFrame := by
  sorry

instance canonicalStandard : Standard canonicalModel := by
  sorry

instance : ProperStandard canonicalModel where
  toStandard := canonicalStandard
  toProper := canonicalProper

theorem completeness :
    ∀ {φ : Φ}, RSPDL0Formula φ → (¬ ⊢ φ) →
    ∃ (M : Model) (_ : ProperStandard M), ¬ (M ⊨ φ) := by
  sorry
