import Mathlib.Data.Set.Lattice

import PdlParallelStoring.AxiomaticSystem
import PdlParallelStoring.Semantics

open Classical

-- Predicates for formulae and programs in the RSPDL₀ fragment.
-- In this fragment, we do not allow the use of the operators of:
--   - test (?)
--   - iteration (★)
--   - parallel composition (‖).

def IsConsistent (Γ : Set Formula) : Prop :=
  ¬ (Γ ⊢ ⊥')

def IsMaximalConsistent (Γ : Set Formula) : Prop :=
  IsConsistent Γ ∧
  ∀ {φ}, (φ ∉ Γ) → ¬ IsConsistent (Γ ∪ {φ})

lemma consistent_empty : IsConsistent ∅ := by
  sorry

lemma weakening : ∀ {Γ Δ : Set Formula} {φ : Formula}, (Γ ⊆ Δ) → (Γ ⊢ φ) → Δ ⊢ φ := by
  intros _ _ _ h_sub h_deriv
  induction h_deriv with
  | premise _ _ h_mem =>
      apply Deduction.premise
      exact h_sub h_mem
  | axiom' _ _ h_ax =>
      apply Deduction.axiom'
      exact h_ax
  | modusPonens _ _ _ _ _ ih_phi ih_imp =>
      apply Deduction.modusPonens
      · exact ih_phi h_sub
      · exact ih_imp h_sub
  | necessitation _ _ _ h_empty _ =>
      apply Deduction.necessitation
      exact h_empty

lemma monotonicity : ∀ {Γ Δ : Set Formula} {φ : Formula}, (Γ ⊢ φ) → (Γ ∪ Δ) ⊢ φ := by
  intros _ _ _ h_deriv
  apply weakening
  · intro _ hx
    left
    exact hx
  · exact h_deriv

lemma deduction_theorem : ∀ {Γ : Set Formula} {φ ψ : Formula},
    (Γ ∪ {φ} ⊢ ψ) → (Γ ⊢ (φ → ψ)) := by
  intros Γ φ ψ h_union_deriv
  sorry

lemma deduction_consistency_aux : ∀ {Γ : Set Formula} {φ : Formula},
    (Γ ⊢ φ) ↔ ¬ IsConsistent (Γ ∪ {¬ φ}) := by
  intros Γ φ
  constructor
  . intros h_deriv h_consist
    apply h_consist
    have h₁ : Γ ∪ {¬ φ} ⊢ φ := monotonicity h_deriv
    have h₂ : Γ ∪ {¬ φ} ⊢ ¬ φ := by
      apply Deduction.premise
      simp only [Set.union_singleton, Set.mem_insert_iff, true_or]
    have h₃ : Γ ∪ {¬ φ} ⊢ φ ∧ ¬ φ := by
      have h_ax : (Γ ∪ {¬ φ}) ⊢ (φ → ((¬ φ) → (φ ∧ (¬ φ)))) := by
        apply Deduction.axiom'
        apply Axiom.conjIntro
      have h_step : (Γ ∪ {¬ φ}) ⊢ ((¬ φ) → (φ ∧ (¬ φ))) := by
        exact Deduction.modusPonens (Γ ∪ {¬ φ}) φ ((¬ φ) → (φ ∧ (¬ φ))) h₁ h_ax
      exact Deduction.modusPonens (Γ ∪ {¬ φ}) (¬ φ) (φ ∧ (¬ φ)) h₂ h_step
    have h₄ : Γ ∪ {¬ φ} ⊢ ((φ ∧ (¬ φ)) → ⊥') := by
      apply Deduction.axiom'
      apply Axiom.contradiction
    exact Deduction.modusPonens (Γ ∪ {¬ φ}) (φ ∧ (¬ φ)) ⊥' h₃ h₄
  . intros h_inconsistent
    simp only [IsConsistent, Decidable.not_not] at h_inconsistent
    have h_imp : Γ ⊢ ((¬ φ) → ⊥') := deduction_theorem h_inconsistent
    apply Deduction.modusPonens Γ ((¬ φ) → ⊥') φ h_imp
    apply Deduction.axiom'
    apply Axiom.reductio

lemma deduction_consistency : ∀ {φ : Formula}, ((⊢ φ) ↔ ¬ IsConsistent {¬ φ}) := by
  intros φ
  constructor
  . sorry
  . sorry

lemma unprovable_consistent : ∀ {φ : Formula}, (¬ ⊢ φ) → IsConsistent {¬ φ} := by
  intros _ h_not_prov
  rewrite [deduction_consistency] at h_not_prov
  exact Decidable.not_not.mp h_not_prov

def MaximalConsistentSet : Type :=
  {Γ : Set Formula // IsMaximalConsistent Γ}

lemma mcs_complete (Γ : MaximalConsistentSet) (φ : Formula) : (φ ∈ Γ.val) ∨ (¬ φ) ∈ Γ.val := by
  sorry

lemma mcs_no_contradiction (Γ : MaximalConsistentSet) (φ : Formula) :
    (φ ∈ Γ.val) →
    (¬ φ) ∉ Γ.val := by
  sorry

namespace Lindenbaum

def insert : Option Formula → Set Formula → Set Formula
  | none, Γ => Γ
  | some φ, Γ =>
      if IsConsistent (Γ ∪ {φ})
      then Γ ∪ {φ}
      else Γ ∪ {¬ φ}

def delta (Γ : Set Formula) : Nat → Set Formula
  | 0 => Γ
  | n + 1 => insert (decode n) (delta Γ n)

def max (Γ : Set Formula) : Set Formula :=
  ⋃ n, delta Γ n

lemma cut_aux :
    ∀ {Δ : Set Formula} {ψ : Formula}, (Δ ⊢ ψ) →
    ∀ {Γ: Set Formula} {φ: Formula}, (Δ = (Γ ∪ {φ})) →
    (Γ ⊢ φ) →
    Γ ⊢ ψ := by
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
  | modusPonens _ φ ψ _ _ ih₁ ih₂ =>
      intros Δ _ h_eq h_deriv
      have h_ant : Δ ⊢ φ := ih₁ h_eq h_deriv
      have h_cond : Δ ⊢ (φ → ψ) := ih₂ h_eq h_deriv
      exact Deduction.modusPonens Δ φ ψ h_ant h_cond
  | necessitation _ α φ h_empty_deriv _ =>
      intros Δ _ _ _
      exact Deduction.necessitation Δ α φ h_empty_deriv

lemma cut : ∀ {Γ : Set Formula} {φ ψ : Formula}, (Γ ⊢ φ) → (Γ ∪ {φ} ⊢ ψ) → Γ ⊢ ψ := by
  intros _ _ _ h₁ h₂
  exact cut_aux h₂ rfl h₁

lemma consistency_either (Γ : Set Formula) (φ : Formula) :
    IsConsistent Γ →
    IsConsistent (Γ ∪ {φ}) ∨ IsConsistent (Γ ∪ {¬ φ}) := by
  intros h_consistent
  by_contra h
  have h₁ : (¬ IsConsistent (Γ ∪ {φ})) ∧ ¬ IsConsistent (Γ ∪ {¬ φ}) := by
    constructor
    . intros h_union_consistent
      apply h
      left
      exact h_union_consistent
    . intros h_union_consistent
      apply h
      right
      exact h_union_consistent
  obtain ⟨h₁₁, h₁₂⟩ := h₁
  rewrite [← deduction_consistency_aux] at h₁₂
  apply h₁₁
  intros h₂
  apply h_consistent
  exact cut h₁₂ h₂

lemma insert_preserves_consistency (opt_φ : Option Formula) (Γ : Set Formula) :
    IsConsistent Γ →
    IsConsistent (insert opt_φ Γ) := by
  intros h_consistent
  cases opt_φ with
  | none => exact h_consistent
  | some φ =>
      rewrite [insert]
      split_ifs with h
      . exact h
      . have h_either := consistency_either Γ φ h_consistent
        cases h_either with
        | inl _ => contradiction
        | inr hRight => exact hRight

lemma delta_preserves_consistency (Γ : Set Formula) (n : Nat) :
    IsConsistent Γ →
    IsConsistent (delta Γ n) := by
  intros h_consistent
  induction n with
  | zero => exact h_consistent
  | succ n ih =>
      apply insert_preserves_consistency
      exact ih

lemma lindenbaum (Γ : Set Formula) : IsConsistent Γ → ∃ (Δ : MaximalConsistentSet), Γ ⊆ Δ.val := by
  sorry

end Lindenbaum

def canonicalRelation (α : Program) (Γ Δ : MaximalConsistentSet) : Prop :=
  ∀ {φ}, (([α] φ) ∈ Γ.val) → φ ∈ Δ.val

def canonicalFrame : Frame where
  W := MaximalConsistentSet
  R := canonicalRelation
  nonempty := sorry

def canonicalValuation (lit : Literal) (Γ : MaximalConsistentSet) : Prop :=
  (Formula.atomic lit) ∈ Γ.val

def canonicalModel : Model where
  F := canonicalFrame
  V := canonicalValuation

lemma truth_lemma (φ : Formula) (Γ : canonicalModel.F.W) :
    ((canonicalModel, Γ) ⊨ φ) ↔ φ ∈ Γ.val := by
  sorry

instance canonicalProper : Proper canonicalFrame := by
  sorry

instance canonicalStandard : Standard canonicalModel := by
  sorry

instance : ProperStandard canonicalModel where
  toStandard := canonicalStandard
  toProper := canonicalProper

lemma contrapositive_completeness :
    ∀ {φ : Formula}, (¬ ⊢ φ) →
    ∃ (M : Model) (_ : ProperStandard M), ¬ (M ⊨ φ) := by
  intros φ h_not_prov
  have h₁ : IsConsistent {¬ φ} := unprovable_consistent h_not_prov
  obtain ⟨Γ, h₂⟩ := Lindenbaum.lindenbaum {¬ φ} h₁
  have h₃ : (¬ φ) ∈ Γ.val := h₂ (Set.mem_singleton (¬ φ))
  have h₄ : φ ∉ Γ.val := by
    by_contra h_in
    have h_not_in : (¬ φ) ∉ Γ.val := mcs_no_contradiction Γ φ h_in
    exact h_not_in h₃
  have h₅ : ¬ ((canonicalModel, Γ) ⊨ φ) := by
    rewrite [truth_lemma φ Γ]
    exact h₄
  use canonicalModel, inferInstance
  intro h_global_sat
  have h_sat : (canonicalModel, Γ) ⊨ φ := h_global_sat
  exact h₅ h_sat

theorem completeness : ∀ {φ : Formula}, (⊨ φ) → (⊢ φ) := by
  intros φ h_valid
  by_contra h_not_prov
  obtain ⟨M, _, h_not_global_sat⟩ := contrapositive_completeness h_not_prov
  have h_global_sat : M ⊨ φ := h_valid rfl
  exact h_not_global_sat h_global_sat
