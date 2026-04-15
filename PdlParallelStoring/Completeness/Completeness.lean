import PdlParallelStoring.Completeness.GeneratedSubmodel

open Classical Lindenbaum

/-!
# Completeness of RSPDL₀

This module proves that every formula valid in all proper standard₀ models is derivable
in the RSPDL₀ axiomatic system: if ⊨ φ then ⊢ φ.

The proof follows the canonical model construction: maximal consistent sets serve as
worlds, the canonical relation is defined via the box operator, and a generated submodel
is used to obtain a proper standard₀ countermodel for any non-theorem.
-/

lemma contrapositive_completeness : ∀ {φ : Formula},
    (¬ ⊢ φ) →
    ∃ (M : Model) (_ : ProperStandard₀ M), ¬ (M ⊨ φ) := by
  intros φ h_not_prov
  have h₁ : IsConsistent {¬ φ} := by
    rewrite [deduction_consistency] at h_not_prov
    exact Decidable.not_not.mp h_not_prov
  obtain ⟨Γ, h₂⟩ := lindenbaum h₁
  have h₃ : (¬ φ) ∈ Γ.val := h₂ (Set.mem_singleton (¬ φ))
  have h₄ : φ ∉ Γ.val := λ h_in => mcs_no_contradiction h_in h₃
  use generatedSubmodel Γ, generatedSubmodelProperStandard Γ
  intro h_global_sat
  have h_sat : (generatedSubmodel Γ, gamma_is_world Γ) ⊨ φ := h_global_sat
  have h_in : φ ∈ (gamma_is_world Γ).val.val := submodel_truth_lemma.mp h_sat
  exact h₄ h_in

theorem completeness : ∀ {φ : Formula},
    (⊨ φ) →
    (⊢ φ) := by
  intros φ h_valid
  by_contra h_not_prov
  obtain ⟨M, _, h_not_global_sat⟩ := contrapositive_completeness h_not_prov
  exact h_not_global_sat (h_valid rfl)
