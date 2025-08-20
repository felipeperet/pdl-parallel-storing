import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import PdlParallelStoring.Syntax

open Program

----------------------------------------------------------------------------------------------------
-- Axiomatic System for RSPDL₀ (Hilbert-style with context)
----------------------------------------------------------------------------------------------------
-- This is a fragment called RSPDL₀. In this fragment, we do not allow the use of the operators of
-- test (?), iteration (★) and parallel composition (‖).

inductive Axiom : Formula → Prop where
  -- Propositional Logic Axioms
  | axiomI φ : Axiom (φ → φ)
  | axiomK φ ψ : Axiom (φ → (ψ → φ))
  | axiomS φ ψ χ : Axiom ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))
  | conjIntro φ ψ : Axiom (φ → (ψ → (φ ∧ ψ)))
  | contradiction φ : Axiom ((φ ∧ (¬ φ)) → ⊥')
  -- Classical Logic Axiom
  | classicalReductio φ : Axiom (((¬ φ) → ⊥') → φ)
  -- Modal Axioms
  | modalComposition α β φ : Axiom (([α ; β] φ) ↔ ([α] [β] φ))
  | modalChoice α β φ : Axiom (([α ∪ β] φ) ↔ (([α] φ) ∧ ([β] φ)))
  | modalK α φ₁ φ₂ : Axiom (([α] (φ₁ → φ₂)) → (([α] φ₁) → ([α] φ₂)))
  -- RSPDL₀ Specific Axioms
  | functionalR₁ φ : Axiom ((⟨r₁⟩ φ) → ([r₁] φ))
  | functionalR₂ φ : Axiom ((⟨r₂⟩ φ) → ([r₂] φ))
  | temporalForward φ : Axiom (φ → ([s₁] ⟨r₁⟩ φ))
  | temporalBackward φ : Axiom (⟨s₁⟩ ⟨r₁⟩ φ → φ)
  | s₁r₁Converse φ : Axiom ((⟨s₁⟩ φ) → (⟨r₁⟩ φ))
  | r₁s₁Converse φ : Axiom ((⟨r₁⟩ φ) → (⟨s₁⟩ φ))
  | temporalForward₂ φ : Axiom (φ → ([s₂] ⟨r₂⟩ φ))
  | temporalBackward₂ φ : Axiom (⟨s₂⟩ ⟨r₂⟩ φ → φ)
  | s₂r₂Converse φ : Axiom ((⟨s₂⟩ φ) → (⟨r₂⟩ φ))
  | r₂s₂Converse φ : Axiom (⟨r₂⟩ φ → (⟨s₂⟩ φ))
  | sameDomain : Axiom ((⟨r₁⟩ ⊤') ↔ (⟨r₂⟩ ⊤'))
  | unicity φ : Axiom ((⟨s₁ ; r₁⟩ φ) ↔ ([s₁ ; r₁] φ))
  | storeRestoreId φ : Axiom (([s₁ ; r₂] φ) → φ)
  | storeRestoreDiamond φ : Axiom (φ → ([s₁ ; r₂] ⟨s₁ ; r₂⟩ φ))
  | storeRestoreIterate φ : Axiom (([s₁ ; r₂] φ) → ([s₁ ; r₂] [s₁ ; r₂] φ))

-- Deduction system with context.
inductive Deduction : Set Formula → Formula → Prop where
  | premise Γ φ : (φ ∈ Γ) → Deduction Γ φ
  | axiom' Γ φ : Axiom φ → Deduction Γ φ
  | modusPonens Γ φ ψ :
      Deduction Γ φ →
      Deduction Γ (φ → ψ) →
      Deduction Γ ψ
  | necessitation Γ α φ :
      Deduction ∅ φ →
      Deduction Γ ([α] φ)

notation:40 Γ " ⊢ " φ => Deduction Γ φ

notation:40 "⊢ " φ => ∅ ⊢ φ

----------------------------------------------------------------------------------------------------
-- Properties of the system
----------------------------------------------------------------------------------------------------
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
