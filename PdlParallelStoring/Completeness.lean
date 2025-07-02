import Mathlib.Logic.Basic
import Mathlib.Data.Set.Insert

import PdlParallelStoring.AxiomaticSystem
import PdlParallelStoring.Properties

def IsConsistent (s : Set Φ) : Prop :=
  ¬ ∃ (φs : List Φ), (∀ φ ∈ φs, φ ∈ s) ∧ (⊢ ((φs.foldr (· ∧ ·) ⊤') → ⊥'))

def IsMaximal (s : Set Φ) : Prop :=
  IsConsistent s ∧ ∀ {φ : Φ}, (φ ∉ s) → ¬ IsConsistent (s ∪ {φ})

def MaximalConsistentSet : Type :=
  {s : Set Φ // IsMaximal s}

def CanonicalFrame : Frame where
  W := MaximalConsistentSet
  R := sorry
  nonempty := sorry

def CanonicalModel : Model where
  F := CanonicalFrame
  V := sorry

instance canonical_proper : Proper CanonicalFrame := by
  sorry

instance canonical_standard : Standard CanonicalModel := by
  sorry

instance : ProperStandard CanonicalModel where
  toStandard := canonical_standard
  toProper := canonical_proper

theorem completeness : ∀ {φ : Φ}, (¬ ⊢ φ) → ∃ (M : Model) (_ : ProperStandard M), ¬ (M ⊨ φ) := by
  sorry
