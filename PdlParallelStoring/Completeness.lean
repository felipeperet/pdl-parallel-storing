import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

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

lemma weakening : ∀ {Γ Δ : Set Formula} {φ : Formula},
    (Γ ⊆ Δ) →
    (Γ ⊢ φ) →
    Δ ⊢ φ := by
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

lemma monotonicity : ∀ {Γ Δ : Set Formula} {φ : Formula},
    (Γ ⊢ φ) →
    (Γ ∪ Δ) ⊢ φ := by
  intros _ _ _ h_deriv
  apply weakening
  · intro _ hx
    left
    exact hx
  · exact h_deriv

lemma deduction_theorem_general :
    ∀ {Δ : Set Formula} {ψ : Formula}, (Δ ⊢ ψ) →
    ∀ {Γ : Set Formula} {φ : Formula}, (Δ = Γ ∪ {φ}) →
    (Γ ⊢ (φ → ψ)) := by
  intros _ _ h Γ φ h_eq
  induction h with
  | premise _ χ h_in =>
      rewrite [h_eq] at h_in
      cases h_in with
      | inl h_in₁ =>
          have h_deriv : Γ ⊢ χ := Deduction.premise Γ χ h_in₁
          have h_weak : Γ ⊢ (χ → (φ → χ)) := by
            apply Deduction.axiom'
            apply Axiom.axiomK
          exact Deduction.modusPonens Γ χ (φ → χ) h_deriv h_weak
      | inr h_in₂ =>
          simp only [Set.mem_singleton_iff] at h_in₂
          rewrite [h_in₂]
          apply Deduction.axiom'
          apply Axiom.axiomI
  | axiom' _ χ ax =>
      have h_deriv : Γ ⊢ χ := Deduction.axiom' Γ χ ax
      have h_step : Γ ⊢ (χ → (φ → χ)) := by
        apply Deduction.axiom'
        apply Axiom.axiomK
      exact Deduction.modusPonens Γ χ (φ → χ) h_deriv h_step
  | modusPonens _ χ₁ χ₂ _ _ ih₁ ih₂  =>
      subst h_eq
      simp only [forall_const] at ih₁ ih₂
      have h_comp : Γ ⊢ ((φ → χ₁ → χ₂) → ((φ → χ₁) → (φ → χ₂))) := by
        apply Deduction.axiom'
        apply Axiom.axiomS
      have h_step : Γ ⊢ ((φ → χ₁) → (φ → χ₂)) :=
        Deduction.modusPonens Γ (φ → χ₁ → χ₂) ((φ → χ₁) → (φ → χ₂)) ih₂ h_comp
      exact Deduction.modusPonens Γ (φ → χ₁) (φ → χ₂) ih₁ h_step
  | necessitation _ α χ h_empty_deriv ih =>
      subst h_eq
      simp only [forall_const] at ih
      have h_nec : Γ ⊢ [α] χ := by
        apply Deduction.necessitation
        exact h_empty_deriv
      have h_weak : Γ ⊢ (([α] χ) → (φ → ([α] χ))) := by
        apply Deduction.axiom'
        apply Axiom.axiomK
      exact Deduction.modusPonens Γ ([α] χ) (φ → ([α] χ)) h_nec h_weak

theorem deduction_theorem : ∀ {Γ : Set Formula} {φ ψ : Formula},
    (Γ ∪ {φ} ⊢ ψ) →
    (Γ ⊢ (φ → ψ)) := by
  intros _ _ _ h_union_deriv
  exact deduction_theorem_general h_union_deriv rfl

lemma cut_admissibility_general :
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

theorem cut_admissibility : ∀ {Γ : Set Formula} {φ ψ : Formula},
    (Γ ⊢ φ) →
    (Γ ∪ {φ} ⊢ ψ) →
    Γ ⊢ ψ := by
  intros _ _ _ h₁ h₂
  exact cut_admissibility_general h₂ rfl h₁

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
    apply Axiom.classicalReductio

lemma deduction_consistency : ∀ {φ : Formula},
    ((⊢ φ) ↔ ¬ IsConsistent {¬ φ}) := by
  intros φ
  have h : (∅ ⊢ φ) ↔ ¬ IsConsistent (∅ ∪ {¬ φ}) := @deduction_consistency_aux ∅ φ
  simp only [Set.empty_union] at h
  exact h

def MaximalConsistentSet : Type :=
  {Γ : Set Formula // IsMaximalConsistent Γ}

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
  exact cut_admissibility h₁₂ h₂

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

lemma max_extends : ∀ {Γ : Set Formula}, Γ ⊆ max Γ := by
  intro _ _ h_in
  rewrite [max, Set.mem_iUnion]
  use 0
  rewrite [delta]
  exact h_in

lemma derivation_finite_support :
    ∀ {Γ : Set Formula} {φ : Formula}, (Γ ⊢ φ) →
    ∃ (Δ : Set Formula), Finite Δ ∧ (Δ ⊆ Γ) ∧ (Δ ⊢ φ) := by
  intros _ _ h_deriv
  induction h_deriv with
  | premise _ φ h_mem =>
      use {φ}
      constructor
      · exact Set.finite_singleton φ
      constructor
      · intros _ h_in
        simp only [Set.mem_singleton_iff] at h_in
        rewrite [h_in]
        exact h_mem
      · apply Deduction.premise
        simp only [Set.mem_singleton_iff]
  | axiom' _ _ h_ax =>
      use ∅
      constructor
      · exact Set.finite_empty
      constructor
      · simp only [Set.empty_subset]
      · apply Deduction.axiom'
        exact h_ax
  | modusPonens _ _ _ _ _ ih₁ ih₂ =>
      obtain ⟨s₁, h₁_finite, h₁_sub, h₁_deriv⟩ := ih₁
      obtain ⟨s₂, h₂_finite, h₂_sub, h₂_deriv⟩ := ih₂
      use s₁ ∪ s₂
      constructor
      · exact Set.Finite.union h₁_finite h₂_finite
      constructor
      · exact Set.union_subset h₁_sub h₂_sub
      · apply Deduction.modusPonens
        · exact weakening Set.subset_union_left h₁_deriv
        · exact weakening Set.subset_union_right h₂_deriv
  | necessitation _ _ _ h_empty _ =>
      use ∅
      constructor
      · exact Set.finite_empty
      constructor
      · simp only [Set.empty_subset]
      · apply Deduction.necessitation
        exact h_empty

lemma insert_subset : ∀ {opt_φ : Option Formula} {Γ : Set Formula},
    Γ ⊆ insert opt_φ Γ := by
  intros opt_φ _ φ h_in
  cases opt_φ with
  | none =>
      simp only [insert]
      exact h_in
  | some ψ =>
      simp only [insert]
      split_ifs <;> (left; exact h_in)

lemma delta_monotone : ∀ {Γ : Set Formula} {m n : Nat},
    (m ≤ n) → (delta Γ m ⊆ delta Γ n) := by
  intros _ _ _ h_le
  induction h_le with
  | refl => rfl
  | step _ ih => exact subset_trans ih insert_subset

lemma finite_subset_in_some_delta : ∀ {Γ : Set Formula} {Δ : Set Formula},
    Set.Finite Δ →
    (Δ ⊆ max Γ) →
    ∃ n, Δ ⊆ delta Γ n := by
  intros Γ Δ h_finite h_sub
  if h_empty : Δ = ∅ then
    use 0
    rewrite [h_empty]
    simp only [Set.empty_subset]
  else
    have h_nonempty : Δ.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    have h_bounded : ∃ N, ∀ φ ∈ Δ, ∃ n ≤ N, φ ∈ delta Γ n := by
      obtain ⟨s, hs⟩ := Set.Finite.exists_finset_coe h_finite
      have h_induction :
          ∀ {t : Finset Formula}, ((↑t : Set Formula) ⊆ (max Γ)) →
          ∃ N, ∀ φ ∈ (↑t : Set Formula), ∃ n ≤ N, φ ∈ delta Γ n := by
        intro t
        induction t using Finset.induction with
        | empty =>
            intro _
            use 0
            intros _ h_in
            simp only [Finset.coe_empty, Set.mem_empty_iff_false] at h_in
        | insert φ t' h_not_in ih =>
            intro h_insert_sub
            have h_phi_in_max : φ ∈ max Γ := by
              apply h_insert_sub
              simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, true_or]
            obtain ⟨n_φ, h_phi_in_n⟩ := Set.mem_iUnion.mp h_phi_in_max
            have h_t'_sub : (↑t' : Set Formula) ⊆ max Γ := by
              intros _ h_psi_in
              apply h_insert_sub
              simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
              exact Or.inr h_psi_in
            obtain ⟨N_t', hN_t'⟩ := ih h_t'_sub
            use Nat.max n_φ N_t'
            intros ψ h_psi_in
            simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at h_psi_in
            cases' Set.mem_insert_iff.mp h_psi_in with h_eq h_in_t'
            · rewrite [h_eq]
              use n_φ
              exact ⟨Nat.le_max_left n_φ N_t', h_phi_in_n⟩
            · obtain ⟨n, h_n_le, h_psi_in_n⟩ := hN_t' ψ h_in_t'
              use n
              exact ⟨le_trans h_n_le (Nat.le_max_right n_φ N_t'), h_psi_in_n⟩
      rewrite [← hs] at h_sub
      have h_result := h_induction h_sub
      rewrite [hs] at h_result
      exact h_result
    obtain ⟨N, hN⟩ := h_bounded
    use N
    intros φ h_phi_in
    obtain ⟨n, h_n_le, h_phi_in_n⟩ := hN φ h_phi_in
    exact delta_monotone h_n_le h_phi_in_n

lemma max_is_maximal_consistent : ∀ {Γ : Set Formula},
    IsConsistent Γ →
    IsMaximalConsistent (max Γ) := by
  intros Γ h_consistent
  constructor
  . intro h_inconsistent
    obtain ⟨Δ, h_finite, h_sub, h_deriv⟩ := derivation_finite_support h_inconsistent
    obtain ⟨n, h_sub_delta⟩ := finite_subset_in_some_delta h_finite h_sub
    have h_delta_inconsistent : delta Γ n ⊢ ⊥' := weakening h_sub_delta h_deriv
    have h_delta_consistent : IsConsistent (delta Γ n) :=
      delta_preserves_consistency Γ n h_consistent
    exact h_delta_consistent h_delta_inconsistent
  . intros φ h_not_in h_consistent_with_phi
    sorry

lemma lindenbaum (Γ : Set Formula) :
    IsConsistent Γ →
    ∃ (Δ : MaximalConsistentSet), Γ ⊆ Δ.val := by
  intros h_consistent
  have h_max : IsMaximalConsistent (max Γ) := max_is_maximal_consistent h_consistent
  exists ⟨max Γ, h_max⟩
  exact max_extends

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

lemma truth_lemma : ∀ {φ : Formula} {Γ : canonicalModel.F.W},
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
  have h₁ : IsConsistent {¬ φ} := by
    rewrite [deduction_consistency] at h_not_prov
    exact Decidable.not_not.mp h_not_prov
  obtain ⟨Γ, h₂⟩ := Lindenbaum.lindenbaum {¬ φ} h₁
  have h₃ : (¬ φ) ∈ Γ.val := h₂ (Set.mem_singleton (¬ φ))
  have h₄ : φ ∉ Γ.val := by
    by_contra h_in
    have h_not_in : (¬ φ) ∉ Γ.val := mcs_no_contradiction Γ φ h_in
    exact h_not_in h₃
  have h₅ : ¬ ((canonicalModel, Γ) ⊨ φ) := by
    rewrite [truth_lemma]
    exact h₄
  use canonicalModel, inferInstance
  intro h_global_sat
  have h_sat : (canonicalModel, Γ) ⊨ φ := h_global_sat
  exact h₅ h_sat

theorem completeness : ∀ {φ : Formula},
    (⊨ φ) →
    (⊢ φ) := by
  intros φ h_valid
  by_contra h_not_prov
  obtain ⟨M, _, h_not_global_sat⟩ := contrapositive_completeness h_not_prov
  have h_global_sat : M ⊨ φ := h_valid rfl
  exact h_not_global_sat h_global_sat
