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
  | conjElimL φ ψ : Axiom ((φ ∧ ψ) → φ)
  | conjElimR φ ψ : Axiom ((φ ∧ ψ) → ψ)
  | contradiction φ : Axiom ((φ ∧ (¬ φ)) → ⊥')
  -- Classical Logic Axiom
  | classicalReductio φ : Axiom (((¬ φ) → ⊥') → φ)
  -- Modal Axioms
  | duality α φ : Axiom ((⟨α⟩ φ) ↔ ¬ ([α] ¬ φ))
  -- Axiom 2
  | modalK α φ₁ φ₂ : Axiom (([α] (φ₁ → φ₂)) → (([α] φ₁) → ([α] φ₂)))
  -- Axiom 3
  | modalComposition α β φ : Axiom (([α ; β] φ) ↔ ([α] [β] φ))
  -- Axiom 4
  | modalChoice α β φ : Axiom (([α ∪ β] φ) ↔ (([α] φ) ∧ ([β] φ)))
  -- RSPDL₀ Specific Axioms
  -- Axiom 5
  | functionalR₁ φ : Axiom ((⟨r₁⟩ φ) → ([r₁] φ))
  | functionalR₂ φ : Axiom ((⟨r₂⟩ φ) → ([r₂] φ))
  -- Axiom 6
  | temporalForward φ : Axiom (φ → ([s₁] ⟨r₁⟩ φ))
  | temporalBackward φ : Axiom (φ → ([r₁] ⟨s₁⟩ φ))
  | temporalForward₂ φ : Axiom (φ → ([s₂] ⟨r₂⟩ φ))
  | temporalBackward₂ φ : Axiom (φ → ([r₂] ⟨s₂⟩ φ))
  -- Axiom 7
  | sameDomain : Axiom ((⟨r₁⟩ ⊤') ↔ (⟨r₂⟩ ⊤'))
  | sameDomain₂ : Axiom ((⟨s₁⟩ ⊤') ↔ (⟨s₂⟩ ⊤'))
  -- Axiom 8
  | unicity φ : Axiom ((⟨s₁ ; r₁⟩ φ) ↔ ([s₁ ; r₁] φ))
  | unicity₂ φ : Axiom ((⟨s₂ ; r₂⟩ φ) ↔ ([s₂ ; r₂] φ))
  -- Axiom 9
  | storeRestoreId φ : Axiom (([s₁ ; r₂] φ) → φ)
  -- Axiom 10
  | storeRestoreDiamond φ : Axiom (φ → ([s₁ ; r₂] ⟨s₁ ; r₂⟩ φ))
  -- Axiom 11
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

----------------------------------------------------------------------------------------------------
--- Laws of the system
----------------------------------------------------------------------------------------------------

lemma iff_mp {Γ : Set Formula} {φ ψ : Formula} :
    (Γ ⊢ (φ ↔ ψ)) → (Γ ⊢ (φ → ψ)) := by
  intro h
  exact Deduction.modusPonens Γ (φ ↔ ψ) (φ → ψ) h
    (Deduction.axiom' Γ ((φ ↔ ψ) → (φ → ψ)) (Axiom.conjElimL (φ → ψ) (ψ → φ)))

lemma iff_mpr {Γ : Set Formula} {φ ψ : Formula} :
    (Γ ⊢ (φ ↔ ψ)) → (Γ ⊢ (ψ → φ)) := by
  intro h
  exact Deduction.modusPonens Γ (φ ↔ ψ) (ψ → φ) h
    (Deduction.axiom' Γ ((φ ↔ ψ) → (ψ → φ)) (Axiom.conjElimR (φ → ψ) (ψ → φ)))

lemma double_neg_elim (φ : Formula) : ⊢ (((¬ (¬ φ)) → φ)) := by
  apply deduction_theorem
  apply Deduction.modusPonens (∅ ∪ {¬ ¬ φ}) ((¬ φ) → ⊥')
  · apply deduction_theorem
    apply Deduction.modusPonens ((∅ ∪ {¬ ¬ φ}) ∪ {¬ φ}) ((¬ φ) ∧ ¬ ¬ φ)
    · apply Deduction.modusPonens ((∅ ∪ {¬ ¬ φ}) ∪ {¬ φ}) (¬ ¬ φ)
      · exact Deduction.premise ((∅ ∪ {¬ ¬ φ}) ∪ {¬ φ}) (¬ ¬ φ) (by simp)
      · apply Deduction.modusPonens ((∅ ∪ {¬ ¬ φ}) ∪ {¬ φ}) (¬ φ)
        · exact Deduction.premise ((∅ ∪ {¬ ¬ φ}) ∪ {¬ φ}) (¬ φ) (by simp)
        · apply Deduction.axiom'
          exact Axiom.conjIntro (¬ φ) (¬ ¬ φ)
    · apply Deduction.axiom'
      exact Axiom.contradiction (¬ φ)
  · apply Deduction.axiom'
    exact Axiom.classicalReductio φ

lemma contrapositive {Γ : Set Formula} {φ ψ : Formula} :
    (Γ ⊢ (φ → ψ)) → (Γ ⊢ (( ¬ ψ) → (¬ φ))) := by
  intro h_deriv
  apply deduction_theorem
  show Γ ∪ {¬ ψ} ⊢ ¬ φ
  apply Deduction.modusPonens (Γ ∪ {¬ ψ}) ((¬ (¬ φ)) → ⊥')
  · apply deduction_theorem
    show (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} ⊢ ⊥'
    have h_φ : (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} ⊢ φ := by
      apply Deduction.modusPonens ((Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ}) (¬ ¬ φ) φ
      · exact Deduction.premise
          ((Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ})
          (¬ ¬ φ)
          (Set.mem_union_right (Γ ∪ {¬ ψ}) (Set.mem_singleton (¬ ¬ φ)))
      · apply weakening (show ∅ ⊆ (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} by simp)
        exact double_neg_elim φ
    have h_ψ : (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} ⊢ ψ := by
      apply Deduction.modusPonens ((Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ}) φ ψ
      · exact h_φ
      · apply weakening (show Γ ⊆ (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} from
          Set.subset_union_of_subset_left (Set.subset_union_left) _)
        exact h_deriv
    apply Deduction.modusPonens ((Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ}) (ψ ∧ ¬ ψ)
    · apply Deduction.modusPonens ((Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ}) (¬ ψ)
      · exact Deduction.premise ((Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ}) (¬ ψ) (by simp)
      · apply Deduction.modusPonens ((Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ}) ψ
        · exact h_ψ
        · apply Deduction.axiom'
          apply Axiom.conjIntro
    · apply Deduction.axiom'
      apply Axiom.contradiction
  · apply Deduction.axiom'
    apply Axiom.classicalReductio

lemma diamond_monotonicity (α : Program) {φ ψ : Formula} :
    (⊢ (φ → ψ)) → (⊢ ((⟨α⟩ φ) → (⟨α⟩ ψ))) := by
  intros h_deriv
  apply deduction_theorem
  simp only [Set.union_singleton, insert_empty_eq]
  have h_dual_φ : {⟨α⟩ φ} ⊢ (⟨α⟩ φ) ↔ ¬ ([α] ¬ φ) :=
    Deduction.axiom' {⟨α⟩ φ} ((⟨α⟩ φ) ↔ ¬ ([α] ¬ φ)) (Axiom.duality α φ)
  have h_to_box_φ : {⟨α⟩ φ} ⊢ ((⟨α⟩ φ) → ¬ ([α] ¬ φ)) :=
    iff_mp h_dual_φ
  have h_prem_φ : {⟨α⟩ φ} ⊢ (⟨α⟩ φ) :=
    Deduction.premise {⟨α⟩ φ} (⟨α⟩ φ) (Set.mem_singleton (⟨α⟩ φ))
  have h_neg_box_φ : {⟨α⟩ φ} ⊢ ¬ ([α] ¬ φ) :=
    Deduction.modusPonens {⟨α⟩ φ} (⟨α⟩ φ) (¬ ([α] ¬ φ)) h_prem_φ h_to_box_φ
  have h_nec : {⟨α⟩ φ} ⊢ [α] ((¬ ψ) → ¬ φ) :=
    Deduction.necessitation {⟨α⟩ φ} α ((¬ ψ) → ¬ φ) (contrapositive h_deriv)
  have h_modalK_ax : {⟨α⟩ φ} ⊢ ([α] ((¬ ψ) → ¬ φ)) → (([α] (¬ ψ)) → ([α] (¬ φ))) :=
    Deduction.axiom'
      {⟨α⟩ φ}
      (([α] ((¬ ψ) → ¬ φ)) → (([α] (¬ ψ)) → ([α] (¬ φ))))
      (Axiom.modalK α (¬ ψ) (¬ φ))
  have h_modalK : {⟨α⟩ φ} ⊢ (([α] (¬ ψ)) → ([α] (¬ φ))) :=
    Deduction.modusPonens {⟨α⟩ φ} ([α] ((¬ ψ) → ¬ φ)) (([α] (¬ ψ)) → ([α] (¬ φ))) h_nec h_modalK_ax
  have h_neg_box_ψ : {⟨α⟩ φ} ⊢ ¬ ([α] ¬ ψ) :=
    Deduction.modusPonens {⟨α⟩ φ} (¬ ([α] ¬ φ)) (¬ ([α] ¬ ψ)) h_neg_box_φ (contrapositive h_modalK)
  have h_dual_ψ : {⟨α⟩ φ} ⊢ (⟨α⟩ ψ) ↔ ¬ ([α] ¬ ψ) :=
    Deduction.axiom' {⟨α⟩ φ} ((⟨α⟩ ψ) ↔ ¬ ([α] ¬ ψ)) (Axiom.duality α ψ)
  have h_from_box_ψ : {⟨α⟩ φ} ⊢ ((¬ ([α] ¬ ψ)) → (⟨α⟩ ψ)) :=
    iff_mpr h_dual_ψ
  exact Deduction.modusPonens {⟨α⟩ φ} (¬ ([α] ¬ ψ)) (⟨α⟩ ψ) h_neg_box_ψ h_from_box_ψ

lemma neg_diamond_to_box_neg (α : Program) (φ : Formula) :
    ⊢ ((¬ (⟨α⟩ φ)) → ([α] ¬ φ)) := by
  simp [box]
  exact contrapositive (diamond_monotonicity α (double_neg_elim φ))
