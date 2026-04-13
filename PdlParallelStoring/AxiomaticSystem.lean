import Mathlib.Data.Set.Finite.Basic

import PdlParallelStoring.Syntax

open Classical Program

----------------------------------------------------------------------------------------------------
-- Axiomatic System for RSPDL₀ (Hilbert-style with context)
----------------------------------------------------------------------------------------------------

/- This is a fragment called RSPDL₀. In this fragment, we do not allow the use of the operators of
   test (?), iteration (*) and parallel composition (‖).
-/
inductive Axiom : Formula → Prop where
  -- Propositional Logic Axioms
  | axiomI φ : Axiom (φ → φ)
  | axiomK φ ψ : Axiom (φ → (ψ → φ))
  | axiomS φ ψ χ : Axiom ((φ → (ψ → χ)) → ((φ → ψ) → (φ → χ)))
  | conjIntro φ ψ : Axiom (φ → (ψ → (φ ∧ ψ)))
  | conjElimL φ ψ : Axiom ((φ ∧ ψ) → φ)
  | conjElimR φ ψ : Axiom ((φ ∧ ψ) → ψ)
  | contradiction φ : Axiom ((φ ∧ (¬ φ)) → ⊥')
  | negIntro φ : Axiom ((φ → ⊥') → ¬ φ)
  | negElim φ : Axiom ((¬ φ) → (φ → ⊥'))
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

/-- Deduction system with context.
-/
inductive Deduction : Set Formula → Formula → Prop where
  | premise : ∀ {Γ : Set Formula} {φ : Formula},
      (φ ∈ Γ) →
      Deduction Γ φ
  | axiom' {Γ : Set Formula} {φ : Formula} :
      Axiom φ →
      Deduction Γ φ
  | modusPonens : ∀ {Γ : Set Formula} {φ ψ : Formula},
      Deduction Γ φ →
      Deduction Γ (φ → ψ) →
      Deduction Γ ψ
  | necessitation : ∀ {Γ : Set Formula} {α : Program} {φ : Formula},
      Deduction ∅ φ →
      Deduction Γ ([α] φ)

notation:40 Γ " ⊢ " φ => Deduction Γ φ

notation:40 "⊢ " φ => ∅ ⊢ φ

----------------------------------------------------------------------------------------------------
-- Structural Properties
----------------------------------------------------------------------------------------------------

lemma weakening : ∀ {Γ Δ : Set Formula} {φ : Formula},
    (Γ ⊆ Δ) →
    (Γ ⊢ φ) →
    Δ ⊢ φ := by
  intros _ _ _ h_sub h_deriv
  induction h_deriv with
  | premise h_mem =>
      apply Deduction.premise
      exact h_sub h_mem
  | axiom' h_ax =>
      apply Deduction.axiom'
      exact h_ax
  | modusPonens _ _ ih_phi ih_imp =>
      apply Deduction.modusPonens
      · exact ih_phi h_sub
      · exact ih_imp h_sub
  | necessitation h_empty _ =>
      apply Deduction.necessitation
      exact h_empty

lemma derivation_substitution : ∀ {Γ Δ : Set Formula} {φ : Formula},
    (Δ ⊢ φ) →
    (∀ ψ ∈ Δ, Γ ⊢ ψ) →
    Γ ⊢ φ := by
  intros Γ Δ φ h_deriv h_in
  induction h_deriv with
  | @premise Ω ψ h_in₂ => exact h_in ψ h_in₂
  | @axiom' Ω ψ h_ax => exact Deduction.axiom' h_ax
  | @modusPonens Ω ψ χ h_deriv h_step ih₁ ih₂  =>
      have h_deriv' : Γ ⊢ ψ := ih₁ h_in
      have h_step' : Γ ⊢ ψ → χ := ih₂ h_in
      exact Deduction.modusPonens h_deriv' h_step'
  | @necessitation Ω α ψ h_empty_deriv ih => exact Deduction.necessitation h_empty_deriv

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
  | @premise _ χ h_in =>
      rewrite [h_eq] at h_in
      cases h_in with
      | inl h_in₁ =>
          have h_deriv : Γ ⊢ χ := Deduction.premise h_in₁
          have h_weak : Γ ⊢ (χ → (φ → χ)) := by
            apply Deduction.axiom'
            apply Axiom.axiomK
          exact Deduction.modusPonens h_deriv h_weak
      | inr h_in₂ =>
          simp only [Set.mem_singleton_iff] at h_in₂
          rewrite [h_in₂]
          apply Deduction.axiom'
          apply Axiom.axiomI
  | @axiom' _ χ ax =>
      have h_deriv : Γ ⊢ χ := Deduction.axiom' ax
      have h_step : Γ ⊢ (χ → (φ → χ)) := by
        apply Deduction.axiom'
        apply Axiom.axiomK
      exact Deduction.modusPonens h_deriv h_step
  | @modusPonens _ χ₁ χ₂ _ _ ih₁ ih₂  =>
      subst h_eq
      simp only [forall_const] at ih₁ ih₂
      have h_comp : Γ ⊢ ((φ → χ₁ → χ₂) → ((φ → χ₁) → (φ → χ₂))) := by
        apply Deduction.axiom'
        apply Axiom.axiomS
      have h_step : Γ ⊢ ((φ → χ₁) → (φ → χ₂)) :=
        Deduction.modusPonens ih₂ h_comp
      exact Deduction.modusPonens ih₁ h_step
  | @necessitation _ α χ h_empty_deriv ih =>
      subst h_eq
      simp only [forall_const] at ih
      have h_nec : Γ ⊢ [α] χ := by
        apply Deduction.necessitation
        exact h_empty_deriv
      have h_weak : Γ ⊢ (([α] χ) → (φ → ([α] χ))) := by
        apply Deduction.axiom'
        apply Axiom.axiomK
      exact Deduction.modusPonens h_nec h_weak

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
  | @premise _ φ h_in =>
      intros Δ _ h_eq h_deriv
      rewrite [h_eq] at h_in
      cases h_in with
      | inl h_in_D => exact Deduction.premise h_in_D
      | inr h_in_singleton =>
          rewrite [Set.mem_singleton_iff] at h_in_singleton
          rewrite [h_in_singleton]
          exact h_deriv
  | @axiom' _ φ h_ax =>
      intros Δ _ _ _
      exact Deduction.axiom' h_ax
  | @modusPonens _ φ ψ _ _ ih₁ ih₂ =>
      intros Δ _ h_eq h_deriv
      have h_ant : Δ ⊢ φ := ih₁ h_eq h_deriv
      have h_cond : Δ ⊢ (φ → ψ) := ih₂ h_eq h_deriv
      exact Deduction.modusPonens h_ant h_cond
  | @necessitation _ α φ h_empty_deriv _ =>
      intros Δ _ _ _
      exact Deduction.necessitation h_empty_deriv

theorem cut_admissibility : ∀ {Γ : Set Formula} {φ ψ : Formula},
    (Γ ⊢ φ) →
    (Γ ∪ {φ} ⊢ ψ) →
    Γ ⊢ ψ := by
  intros _ _ _ h₁ h₂
  exact cut_admissibility_general h₂ rfl h₁

----------------------------------------------------------------------------------------------------
--- Propositional Logic Lemmas
----------------------------------------------------------------------------------------------------

lemma iff_mp {Γ : Set Formula} {φ ψ : Formula} :
    (Γ ⊢ (φ ↔ ψ)) →
    (Γ ⊢ (φ → ψ)) := by
  intro h
  exact Deduction.modusPonens h
    (Deduction.axiom' (Axiom.conjElimL (φ → ψ) (ψ → φ)))

lemma iff_mpr {Γ : Set Formula} {φ ψ : Formula} :
    (Γ ⊢ (φ ↔ ψ)) →
    (Γ ⊢ (ψ → φ)) := by
  intro h
  exact Deduction.modusPonens h
    (Deduction.axiom' (Axiom.conjElimR (φ → ψ) (ψ → φ)))

lemma double_neg_elim (φ : Formula) : ⊢ (((¬ (¬ φ)) → φ)) := by
  apply deduction_theorem
  apply Deduction.modusPonens
  · apply deduction_theorem
    apply Deduction.modusPonens
    · apply Deduction.modusPonens
      · apply @Deduction.premise ((∅ ∪ {¬ ¬ φ}) ∪ {¬ φ}) (¬ ¬ φ) (by simp)
      · apply Deduction.modusPonens
        · exact @Deduction.premise ((∅ ∪ {¬ ¬ φ}) ∪ {¬ φ}) (¬ φ) (by simp)
        · apply Deduction.axiom'
          exact Axiom.conjIntro (¬ φ) (¬ ¬ φ)
    · apply Deduction.axiom'
      exact Axiom.contradiction (¬ φ)
  · apply Deduction.axiom'
    exact Axiom.classicalReductio φ

lemma explosion : ∀ {Γ : Set Formula} {φ : Formula},
    (Γ ⊢ ⊥') →
    Γ ⊢ φ := by
  intros _ φ h
  exact Deduction.modusPonens
          (deduction_theorem (monotonicity h))
          (Deduction.axiom' (Axiom.classicalReductio φ))

lemma false_impl : ∀ {φ : Formula}, ⊢ ⊥' → φ := by
  intros φ
  apply deduction_theorem
  apply Deduction.modusPonens _ (Deduction.axiom' (Axiom.classicalReductio φ))
  apply deduction_theorem
  exact Deduction.premise (Set.mem_union_left _ (Set.mem_union_right _ rfl))

lemma contrapositive {Γ : Set Formula} {φ ψ : Formula} :
    (Γ ⊢ (φ → ψ)) →
    (Γ ⊢ (( ¬ ψ) → (¬ φ))) := by
  intro h_deriv
  apply deduction_theorem
  show Γ ∪ {¬ ψ} ⊢ ¬ φ
  apply Deduction.modusPonens
  · apply deduction_theorem
    show (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} ⊢ ⊥'
    have h_φ : (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} ⊢ φ := by
      apply Deduction.modusPonens
      · exact Deduction.premise
          (Set.mem_union_right (Γ ∪ {¬ ψ}) (Set.mem_singleton (¬ ¬ φ)))
      · apply weakening (show ∅ ⊆ (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} by simp)
        exact double_neg_elim φ
    have h_ψ : (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} ⊢ ψ := by
      apply Deduction.modusPonens
      · exact h_φ
      · apply weakening (show Γ ⊆ (Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ} from
          Set.subset_union_of_subset_left (Set.subset_union_left) _)
        exact h_deriv
    apply Deduction.modusPonens
    · apply Deduction.modusPonens
      · exact @Deduction.premise ((Γ ∪ {¬ ψ}) ∪ {¬ ¬ φ}) (¬ ψ) (by simp)
      · apply Deduction.modusPonens
        · exact h_ψ
        · apply Deduction.axiom'
          apply Axiom.conjIntro
    · apply Deduction.axiom'
      apply Axiom.contradiction
  · apply Deduction.axiom'
    apply Axiom.classicalReductio

lemma impl_chain : ∀ {φ ψ χ : Formula},
    (⊢ φ → ψ) →
    (⊢ ψ → χ) →
    (⊢ φ → χ) := by
  intros _ _ _ h₁ h₂
  apply deduction_theorem
  apply Deduction.modusPonens
  · exact Deduction.modusPonens
      (Deduction.premise (Set.mem_union_right _ rfl))
      (weakening (Set.empty_subset _) h₁)
  · exact weakening (Set.empty_subset _) h₂

lemma disj_intro_left : ∀ {φ ψ : Formula}, ⊢ (φ → (φ ∨ ψ)) := by
  intros φ ψ
  let θ := (¬ φ) ∧ (¬ ψ)
  show ∅ ⊢ (φ → ¬ θ)
  apply deduction_theorem
  apply Deduction.modusPonens
  · apply deduction_theorem
    have h_phi : (∅ ∪ {φ}) ∪ {θ} ⊢ φ :=
      Deduction.premise (Set.mem_union_left _ (Set.mem_union_right _ rfl))
    have h_theta : (∅ ∪ {φ}) ∪ {θ} ⊢ θ :=
      Deduction.premise (Set.mem_union_right _ rfl)
    have h_neg_phi : (∅ ∪ {φ}) ∪ {θ} ⊢ ¬ φ :=
      Deduction.modusPonens h_theta
        (Deduction.axiom' (Axiom.conjElimL (¬ φ) (¬ ψ)))
    have h_conj : (∅ ∪ {φ}) ∪ {θ} ⊢ (φ ∧ ¬ φ) :=
      Deduction.modusPonens h_neg_phi
        (Deduction.modusPonens h_phi (Deduction.axiom' (Axiom.conjIntro φ (¬ φ))))
    exact Deduction.modusPonens h_conj (Deduction.axiom' (Axiom.contradiction φ))
  · exact Deduction.axiom' (Axiom.negIntro θ)

lemma disj_intro_right : ∀ {φ ψ : Formula}, ⊢ (ψ → (φ ∨ ψ)) := by
  intros φ ψ
  let θ := (¬ φ) ∧ (¬ ψ)
  show ∅ ⊢ (ψ → ¬ θ)
  apply deduction_theorem
  apply Deduction.modusPonens
  · apply deduction_theorem
    have h_psi : (∅ ∪ {ψ}) ∪ {θ} ⊢ ψ :=
      Deduction.premise (Set.mem_union_left _ (Set.mem_union_right _ rfl))
    have h_theta : (∅ ∪ {ψ}) ∪ {θ} ⊢ θ :=
      Deduction.premise (Set.mem_union_right _ rfl)
    have h_neg_psi : (∅ ∪ {ψ}) ∪ {θ} ⊢ ¬ ψ :=
      Deduction.modusPonens h_theta
        (Deduction.axiom' (Axiom.conjElimR (¬ φ) (¬ ψ)))
    have h_conj : (∅ ∪ {ψ}) ∪ {θ} ⊢ (ψ ∧ ¬ ψ) :=
      Deduction.modusPonens h_neg_psi
        (Deduction.modusPonens h_psi (Deduction.axiom' (Axiom.conjIntro ψ (¬ ψ))))
    exact Deduction.modusPonens h_conj (Deduction.axiom' (Axiom.contradiction ψ))
  · exact Deduction.axiom' (Axiom.negIntro θ)

lemma disj_from_neg_imp : ∀ {Γ : Set Formula} {φ ψ : Formula},
    (Γ ∪ {¬ φ} ⊢ ψ) →
    (Γ ⊢ disj φ ψ) := by
  intros Γ φ ψ h
  let θ := (¬ φ) ∧ (¬ ψ)
  suffices Γ ⊢ ¬ θ from this
  apply Deduction.modusPonens _ (Deduction.axiom' (Axiom.negIntro θ))
  apply deduction_theorem
  have h_neg_phi : Γ ∪ {θ} ⊢ ¬ φ :=
    Deduction.modusPonens (Deduction.premise (Set.mem_union_right _ rfl))
      (Deduction.axiom' (Axiom.conjElimL (¬ φ) (¬ ψ)))
  have h_neg_psi : Γ ∪ {θ} ⊢ ¬ ψ :=
    Deduction.modusPonens (Deduction.premise (Set.mem_union_right _ rfl))
      (Deduction.axiom' (Axiom.conjElimR (¬ φ) (¬ ψ)))
  have h_psi : Γ ∪ {θ} ⊢ ψ := by
    apply cut_admissibility h_neg_phi
    apply weakening _ h
    intro x hx
    cases hx with
    | inl hx => exact Set.mem_union_left _ (Set.mem_union_left _ hx)
    | inr hx => exact Set.mem_union_right _ hx
  exact Deduction.modusPonens
    (Deduction.modusPonens h_neg_psi
      (Deduction.modusPonens h_psi (Deduction.axiom' (Axiom.conjIntro ψ (¬ ψ)))))
    (Deduction.axiom' (Axiom.contradiction ψ))

lemma disj_elim : ∀ {φ ψ χ : Formula},
    (⊢ φ → χ) →
    (⊢ ψ → χ) →
    (⊢ (φ ∨ ψ) → χ) := by
  intros φ ψ χ h₁ h₂
  let θ := (¬ φ) ∧ (¬ ψ)
  apply deduction_theorem
  apply Deduction.modusPonens _ (Deduction.axiom' (Axiom.classicalReductio χ))
  apply deduction_theorem
  have h_neg_chi : (∅ ∪ {¬ θ}) ∪ {¬ χ} ⊢ ¬ χ :=
    Deduction.premise (Set.mem_union_right _ rfl)
  have h_neg_phi : (∅ ∪ {¬ θ}) ∪ {¬ χ} ⊢ ¬ φ := by
    apply Deduction.modusPonens h_neg_chi
    exact weakening (Set.empty_subset _) (contrapositive h₁)
  have h_neg_psi : (∅ ∪ {¬ θ}) ∪ {¬ χ} ⊢ ¬ ψ := by
    apply Deduction.modusPonens h_neg_chi
    exact weakening (Set.empty_subset _) (contrapositive h₂)
  have h_theta : (∅ ∪ {¬ θ}) ∪ {¬ χ} ⊢ θ :=
    Deduction.modusPonens h_neg_psi
      (Deduction.modusPonens h_neg_phi
        (Deduction.axiom' (Axiom.conjIntro (¬ φ) (¬ ψ))))
  have h_neg_theta : (∅ ∪ {¬ θ}) ∪ {¬ χ} ⊢ ¬ θ :=
    Deduction.premise (Set.mem_union_left _ (Set.mem_union_right _ rfl))
  exact Deduction.modusPonens
    (Deduction.modusPonens h_neg_theta
      (Deduction.modusPonens h_theta
        (Deduction.axiom' (Axiom.conjIntro θ (¬ θ)))))
    (Deduction.axiom' (Axiom.contradiction θ))

----------------------------------------------------------------------------------------------------
--- Modal Logic Lemmas
----------------------------------------------------------------------------------------------------

lemma diamond_monotonicity : ∀ {α : Program} {φ ψ : Formula},
    (⊢ (φ → ψ)) →
    (⊢ ((⟨α⟩ φ) → (⟨α⟩ ψ))) := by
  intros α φ ψ h_deriv
  apply deduction_theorem
  simp only [Set.union_singleton, insert_empty_eq]
  have h_dual_φ : {⟨α⟩ φ} ⊢ (⟨α⟩ φ) ↔ ¬ ([α] ¬ φ) :=
    Deduction.axiom' (Axiom.duality α φ)
  have h_to_box_φ : {⟨α⟩ φ} ⊢ ((⟨α⟩ φ) → ¬ ([α] ¬ φ)) :=
    iff_mp h_dual_φ
  have h_prem_φ : {⟨α⟩ φ} ⊢ (⟨α⟩ φ) :=
    Deduction.premise (Set.mem_singleton (⟨α⟩ φ))
  have h_neg_box_φ : {⟨α⟩ φ} ⊢ ¬ ([α] ¬ φ) :=
    Deduction.modusPonens h_prem_φ h_to_box_φ
  have h_nec : {⟨α⟩ φ} ⊢ [α] ((¬ ψ) → ¬ φ) :=
    Deduction.necessitation (contrapositive h_deriv)
  have h_modalK_ax : {⟨α⟩ φ} ⊢ ([α] ((¬ ψ) → ¬ φ)) → (([α] (¬ ψ)) → ([α] (¬ φ))) :=
    Deduction.axiom' (Axiom.modalK α (¬ ψ) (¬ φ))
  have h_modalK : {⟨α⟩ φ} ⊢ (([α] (¬ ψ)) → ([α] (¬ φ))) :=
    Deduction.modusPonens h_nec h_modalK_ax
  have h_neg_box_ψ : {⟨α⟩ φ} ⊢ ¬ ([α] ¬ ψ) :=
    Deduction.modusPonens h_neg_box_φ (contrapositive h_modalK)
  have h_dual_ψ : {⟨α⟩ φ} ⊢ (⟨α⟩ ψ) ↔ ¬ ([α] ¬ ψ) :=
    Deduction.axiom' (Axiom.duality α ψ)
  have h_from_box_ψ : {⟨α⟩ φ} ⊢ ((¬ ([α] ¬ ψ)) → (⟨α⟩ ψ)) :=
    iff_mpr h_dual_ψ
  exact Deduction.modusPonens h_neg_box_ψ h_from_box_ψ

lemma box_monotonicity : ∀ {α : Program} {φ ψ : Formula},
    (⊢ (φ → ψ)) →
    (⊢ (([α] φ) → ([α] ψ))) :=
  λ h => contrapositive (diamond_monotonicity (contrapositive h))

lemma diamond_box_neg_inconsistent : ∀ {Γ : Set Formula} {α : Program} {φ : Formula},
    (Γ ⊢ ⟨α⟩ φ) →
    (Γ ⊢ [α] ¬ φ) →
    Γ ⊢ ⊥' := by
  intros Γ α φ h₁ h₂
  have h_dual : Γ ⊢ (⟨α⟩ φ) ↔ ¬ ([α] ¬ φ) := Deduction.axiom' (Axiom.duality α φ)
  have h_to_neg_box : Γ ⊢ (⟨α⟩ φ) → ¬ ([α] ¬ φ) := iff_mp h_dual
  have h_neg_box : Γ ⊢ ¬ ([α] ¬ φ) := Deduction.modusPonens h₁ h_to_neg_box
  have h_conj : Γ ⊢ (([α] ¬ φ) → ((¬ ([α] ¬ φ)) → (([α] ¬ φ) ∧  ¬ ([α] ¬ φ)))) := by
    apply Deduction.axiom'
    apply Axiom.conjIntro
  have h_step₁ : Γ ⊢ ((¬ ([α] ¬ φ)) → (([α] ¬ φ) ∧  ¬ ([α] ¬ φ))) :=
    Deduction.modusPonens h₂ h_conj
  have h_step₂ : Γ ⊢ (([α] ¬ φ) ∧  ¬ ([α] ¬ φ)) :=
    Deduction.modusPonens h_neg_box h_step₁
  have h_contra : Γ ⊢ (([α] ¬ φ) ∧  ¬ ([α] ¬ φ)) → ⊥' :=
    Deduction.axiom' (Axiom.contradiction _)
  apply Deduction.modusPonens h_step₂ h_contra

lemma neg_diamond_to_box_neg (α : Program) (φ : Formula) :
    ⊢ ((¬ (⟨α⟩ φ)) →
    ([α] ¬ φ)) := by
  simp [box]
  exact contrapositive (diamond_monotonicity (double_neg_elim φ))

lemma box_of_derivation :
    ∀ {Γ : Set Formula} {α : Program} {Δ : Set Formula} {φ : Formula},
    (Δ ⊢ φ) →
    (∀ ψ ∈ Δ, ([α] ψ) ∈ Γ) →
    Γ ⊢ ([α] φ) := by
  intros Γ α Δ φ h_deriv h_box
  induction h_deriv with
  | @premise Ω ψ h_mem =>
      exact Deduction.premise (h_box ψ h_mem)
  | @axiom' Γ.val ψ h_ax =>
      exact weakening (Set.empty_subset _) (Deduction.necessitation (Deduction.axiom' h_ax))
  | @modusPonens Ω ψ χ h₁ h₂ ih₁ ih₂ =>
      have h_K : Γ ⊢ ([α] ψ → χ) → ([α] ψ) → ([α] χ) :=
        Deduction.axiom' (Axiom.modalK α ψ χ)
      exact Deduction.modusPonens (ih₁ h_box)
        (Deduction.modusPonens (ih₂ h_box) h_K)
  | @necessitation Ω β ψ h_empty ih =>
      exact weakening
        (Set.empty_subset _)
        (Deduction.necessitation (Deduction.necessitation h_empty))

----------------------------------------------------------------------------------------------------
-- Connective Lemmas
----------------------------------------------------------------------------------------------------

def list_conjunction : List Formula → Formula
  | [] => ⊤'
  | φ :: rest => φ ∧ (list_conjunction rest)

lemma list_conjunction_elim : ∀ {φ : Formula} {L : List Formula},
    (φ ∈ L) →
    ∅ ⊢ list_conjunction L → φ := by
  intros φ L h_in
  induction L with
  | nil =>
      by_contra
      exact (List.not_mem_nil h_in)
  | cons ψ tail ih =>
      have h_either : (φ = ψ) ∨ (φ ∈ tail) := List.mem_cons.mp h_in
      cases h_either with
      | inl h_eq =>
          subst h_eq
          exact Deduction.axiom' (Axiom.conjElimL φ (list_conjunction tail))
      | inr h_in' =>
          have h_empty_deriv : ∅ ⊢ list_conjunction tail → φ := ih h_in'
          exact
            impl_chain (Deduction.axiom' (Axiom.conjElimR ψ (list_conjunction tail))) h_empty_deriv

def list_disjunction : List Formula → Formula
  | [] => ⊥'
  | φ :: rest => φ ∨ list_disjunction rest

lemma neg_list_to_disj : ∀ {L : List Formula} {Δ : Set Formula},
    (Δ ∪ ↑(L.map Formula.neg).toFinset ⊢ ⊥') →
    (Δ ⊢ list_disjunction L) := by
  intro L
  induction L with
  | nil =>
      intro Δ h
      simp [list_disjunction, List.map, List.toFinset] at *
      exact h
  | cons φ rest ih =>
      intro Δ h
      simp only [list_disjunction]
      have h' : (Δ ∪ {¬ φ}) ∪ ↑(rest.map Formula.neg).toFinset ⊢ ⊥' := by
        apply weakening _ h
        intro x hx
        simp only [Set.mem_union, Finset.mem_coe, List.toFinset_cons, Finset.mem_insert,
          List.mem_toFinset, List.mem_map] at hx ⊢
        aesop
      have h_rest : Δ ∪ {¬ φ} ⊢ list_disjunction rest := ih h'
      exact disj_from_neg_imp h_rest

lemma list_disjunction_box_imp : ∀ {α : Program} (L : List Formula),
    ⊢ list_disjunction (L.map (box α)) →
    ([α] (list_disjunction L)) := by
  intro α L
  induction L with
  | nil =>
      simp only [list_disjunction, List.map]
      exact false_impl
  | cons φ rest ih =>
      simp only [list_disjunction, List.map]
      apply disj_elim
      · exact box_monotonicity disj_intro_left
      · exact impl_chain ih (box_monotonicity disj_intro_right)
