import Mathlib.Data.Set.Lattice

import PdlParallelStoring.AxiomaticSystem
import PdlParallelStoring.Semantics

open Classical

-- Predicates for formulae and programs in the RSPDL₀ fragment.
-- In this fragment, we do not allow the use of the operators of:
--   - test (?)
--   - iteration (★)
--   - parallel composition (‖).

def IsConsistent (Γ : Set Φ) : Prop :=
  ¬ (Γ ⊢ ⊥')

def IsMaximalConsistent (Γ : Set Φ) : Prop :=
  IsConsistent Γ ∧
  ∀ {φ}, (φ ∉ Γ) → ¬ IsConsistent (Γ ∪ {φ})

lemma consistent_empty : IsConsistent ∅ := by
  sorry

lemma deduction_consistency (φ : Φ) : ((⊢ φ) ↔ ¬ IsConsistent {¬ φ}) := by
  sorry

lemma unprovable_consistent (φ : Φ) : (¬ ⊢ φ) → IsConsistent {¬ φ} := by
  intros hNotProv
  rewrite [deduction_consistency φ] at hNotProv
  exact Decidable.not_not.mp hNotProv

def MaximalConsistentSet : Type :=
  {Γ : Set Φ // IsMaximalConsistent Γ}

lemma mcs_complete (Γ : MaximalConsistentSet) (φ : Φ) : (φ ∈ Γ.val) ∨ (¬ φ) ∈ Γ.val := by
  sorry

lemma mcs_no_contradiction (Γ : MaximalConsistentSet) (φ : Φ) : (φ ∈ Γ.val) → (¬ φ) ∉ Γ.val := by
  sorry

namespace Lindenbaum

def insert : Option Φ → Set Φ → Set Φ
  | none, Γ => Γ
  | some φ, Γ =>
      if IsConsistent (Γ ∪ {φ})
      then Γ ∪ {φ}
      else Γ ∪ {¬ φ}

def delta (Γ : Set Φ) : Nat → Set Φ
  | 0 => Γ
  | n + 1 => insert (decode n) (delta Γ n)

def max (Γ : Set Φ) : Set Φ :=
  ⋃ n, delta Γ n

lemma cut_aux : ∀ {Δ ψ}, (Δ ⊢ ψ) → ∀ {Γ φ}, (Δ = (Γ ∪ {φ})) → (Γ ⊢ φ) → Γ ⊢ ψ := by
  intros _ _ h
  induction h with
  | premise _ φ h_in =>
      intros Δ _ h_eq h_deriv
      rewrite [h_eq] at h_in
      cases h_in with
      | inl h_in_D => exact Deduction.premise Δ φ h_in_D
      | inr h_in_singleton =>
          rewrite [Set.mem_singleton_iff] at h_in_singleton
          rewrite [h_in_singleton]
          exact h_deriv
  | axiom' _ φ h_ax =>
      intros Δ _ _ _
      exact Deduction.axiom' Δ φ h_ax
  | modusPonens Γ φ ψ h_ant h_cond ih₁ ih₂ =>
      intros Δ χ h_eq h_deriv
      sorry
  | necessitation =>
      sorry

theorem cut : ∀ {φ ψ : Φ}, (Γ ⊢ φ) → (Γ ∪ {φ} ⊢ ψ) → Γ ⊢ ψ := by
  intros φ ψ h₁ h₂
  exact cut_aux h₂ rfl h₁

lemma consistency_either (Γ : Set Φ) (φ : Φ) :
    IsConsistent Γ →
    IsConsistent (Γ ∪ {φ}) ∨ IsConsistent (Γ ∪ {¬ φ}) := by
  sorry

lemma insert_preserves_consistency (opt_φ : Option Φ) (Γ : Set Φ) :
    IsConsistent Γ → IsConsistent (insert opt_φ Γ) := by
  intros hConsistent
  cases opt_φ with
  | none => exact hConsistent
  | some φ =>
      rewrite [insert]
      split_ifs with h
      . exact h
      . have hEither := consistency_either Γ φ hConsistent
        cases hEither with
        | inl _ => contradiction
        | inr hRight => exact hRight

lemma delta_preserves_consistency (Γ : Set Φ) (n : Nat) :
    IsConsistent Γ → IsConsistent (delta Γ n) := by
  intros hConsistent
  induction n with
  | zero => exact hConsistent
  | succ n ih =>
      apply insert_preserves_consistency
      exact ih

lemma lindenbaum (Γ : Set Φ) : IsConsistent Γ → ∃ (Δ : MaximalConsistentSet), Γ ⊆ Δ.val := by
  /- intros hConsistent -/
  /- exists (max Γ) -/
  sorry

end Lindenbaum

def canonicalRelation (α : π) (Γ Δ : MaximalConsistentSet) : Prop :=
  ∀ {φ}, (([α] φ) ∈ Γ.val) → φ ∈ Δ.val

def canonicalFrame : Frame where
  W := MaximalConsistentSet
  R := canonicalRelation
  nonempty := sorry

def canonicalValuation (lit : Literal) (Γ : MaximalConsistentSet) : Prop :=
  (Φ.atomic lit) ∈ Γ.val

def canonicalModel : Model where
  F := canonicalFrame
  V := canonicalValuation

lemma truth_lemma (φ : Φ) (Γ : canonicalModel.F.W) : ((canonicalModel, Γ) ⊨ φ) ↔ φ ∈ Γ.val := by
  sorry

instance canonicalProper : Proper canonicalFrame := by
  sorry

instance canonicalStandard : Standard canonicalModel := by
  sorry

instance : ProperStandard canonicalModel where
  toStandard := canonicalStandard
  toProper := canonicalProper

lemma contrapositive_completeness :
    ∀ {φ : Φ}, (¬ ⊢ φ) →
    ∃ (M : Model) (_ : ProperStandard M), ¬ (M ⊨ φ) := by
  intros φ hNotProv
  have h₁ : IsConsistent {¬ φ} := unprovable_consistent φ hNotProv
  obtain ⟨Γ, h₂⟩ := Lindenbaum.lindenbaum {¬ φ} h₁
  have h₃ : (¬ φ) ∈ Γ.val := h₂ (Set.mem_singleton (¬ φ))
  have h₄ : φ ∉ Γ.val := by
    by_contra hIn
    have hNotIn : (¬ φ) ∉ Γ.val := mcs_no_contradiction Γ φ hIn
    exact hNotIn h₃
  have h₅ : ¬ ((canonicalModel, Γ) ⊨ φ) := by
    rewrite [truth_lemma φ Γ]
    exact h₄
  use canonicalModel, inferInstance
  intro hGlobalSat
  have hSat : (canonicalModel, Γ) ⊨ φ := hGlobalSat
  exact h₅ hSat

theorem completeness : ∀ {φ : Φ}, (⊨ φ) → (⊢ φ) := by
  intros φ hValid
  by_contra hNotProv
  obtain ⟨M, _, hNotGlobalSat⟩ := contrapositive_completeness hNotProv
  have hGlobalSat : M ⊨ φ := hValid rfl
  exact hNotGlobalSat hGlobalSat
