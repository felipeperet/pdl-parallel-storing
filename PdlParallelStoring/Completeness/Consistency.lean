import PdlParallelStoring.AxiomaticSystem

open Classical

def IsConsistent (Γ : Set Formula) : Prop :=
  ¬ (Γ ⊢ ⊥')

def IsMaximalConsistent (Γ : Set Formula) : Prop :=
  IsConsistent Γ ∧
  ∀ {φ}, (φ ∉ Γ) → ¬ IsConsistent (Γ ∪ {φ})

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
        exact Deduction.modusPonens h₁ h_ax
      exact Deduction.modusPonens h₂ h_step
    have h₄ : Γ ∪ {¬ φ} ⊢ ((φ ∧ (¬ φ)) → ⊥') := by
      apply Deduction.axiom'
      apply Axiom.contradiction
    exact Deduction.modusPonens h₃ h₄
  . intros h_inconsistent
    simp only [IsConsistent, Decidable.not_not] at h_inconsistent
    have h_imp : Γ ⊢ ((¬ φ) → ⊥') := deduction_theorem h_inconsistent
    apply Deduction.modusPonens h_imp
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

lemma mcs_no_contradiction : ∀ {Γ : MaximalConsistentSet} {φ : Formula},
    (φ ∈ Γ.val) →
    (¬ φ) ∉ Γ.val := by
  intros Γ φ h_phi_in h_not_phi_in
  simp only [MaximalConsistentSet] at Γ
  obtain ⟨h_consistent, _⟩ := Γ.property
  apply h_consistent
  have h_derives_phi : Γ ⊢ φ := Deduction.premise h_phi_in
  have h_derives_not_phi : Γ ⊢ ¬ φ := Deduction.premise h_not_phi_in
  have h_conj : Γ ⊢ (φ ∧ ¬ φ) := by
    have h_conj_intro : Γ ⊢ (φ → (¬ φ) → (φ ∧ ¬ φ)) := by
      apply Deduction.axiom'
      apply Axiom.conjIntro
    have h_step : Γ ⊢ (¬ φ) → (φ ∧ ¬ φ) :=
      Deduction.modusPonens h_derives_phi h_conj_intro
    exact Deduction.modusPonens h_derives_not_phi h_step
  have h_contra_intro : Γ ⊢ ((φ ∧ ¬ φ) → ⊥') := by
    apply Deduction.axiom'
    apply Axiom.contradiction
  exact Deduction.modusPonens h_conj h_contra_intro

lemma consistency_either : ∀ {Γ : Set Formula} {φ : Formula},
    IsConsistent Γ →
    IsConsistent (Γ ∪ {φ}) ∨ IsConsistent (Γ ∪ {¬ φ}) := by
  intros Γ φ h_consistent
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

lemma mcs_complete : ∀ {Γ : MaximalConsistentSet} {φ : Formula},
    (φ ∉ Γ.val) →
    (¬ φ) ∈ Γ.val := by
  intros Γ φ h_phi_nin
  obtain ⟨h_cons, h_max⟩ := Γ.property
  by_contra h_neg_phi_nin
  have h_incons_phi : ¬ IsConsistent (Γ.val ∪ {φ}) := h_max h_phi_nin
  have h_incons_neg_phi : ¬ IsConsistent (Γ.val ∪ {¬ φ}) := h_max h_neg_phi_nin
  cases consistency_either h_cons with
  | inl h => exact h_incons_phi h
  | inr h => exact h_incons_neg_phi h

lemma mcs_is_closed : ∀ {Γ : MaximalConsistentSet} {φ : Formula},
    (Γ.val ⊢ φ) →
    φ ∈ Γ.val := by
  intros Γ φ h_deriv
  by_contra h_not_in
  obtain ⟨h_cons, h_max⟩ := Γ.property
  have h_phi_incons : ¬ IsConsistent (Γ.val ∪ {φ}) := h_max h_not_in
  simp only [IsConsistent, not_not] at h_phi_incons
  have h_cut : Γ.val ⊢ ⊥' := cut_admissibility h_deriv h_phi_incons
  exact h_cons h_cut

lemma false_not_in_mcs : ∀ {Γ : MaximalConsistentSet}, Formula.false ∉ Γ.val := by
  intro Γ h
  exact Γ.property.1 (Deduction.premise h)

lemma list_conjunction_in_mcs : ∀ {Γ : MaximalConsistentSet} {L : List Formula},
    (∀ φ ∈ L, φ ∈ Γ.val) →
    list_conjunction L ∈ Γ.val := by
  intros Γ L h
  induction L with
  | nil =>
      simp only [list_conjunction]
      exact mcs_complete false_not_in_mcs
  | cons ψ tail ih =>
      simp only [list_conjunction]
      have hψ : ψ ∈ Γ.val := h ψ (.head tail)
      have htail : list_conjunction tail ∈ Γ.val := ih (λ φ hφ => h φ (List.mem_cons_of_mem ψ hφ))
      exact mcs_is_closed
        (Deduction.modusPonens (Deduction.premise htail)
          (Deduction.modusPonens (Deduction.premise hψ)
            (Deduction.axiom' (Axiom.conjIntro ψ (list_conjunction tail)))))

def canonicalRelation (α : Program) (Γ Δ : MaximalConsistentSet) : Prop :=
  ∀ {φ}, (([α] φ) ∈ Γ.val) → φ ∈ Δ.val

def semantic_interpretation : Formula → Prop
  | .false => False
  | .atom _ => True
  | .neg φ => ¬ semantic_interpretation φ
  | .conj φ ψ => semantic_interpretation φ ∧ semantic_interpretation ψ
  | .diamond _ φ => semantic_interpretation φ

lemma semantic_interpretation_sound : ∀ {Γ : Set Formula} {φ : Formula},
    (Γ ⊢ φ) →
    (∀ ψ ∈ Γ, semantic_interpretation ψ) →
    semantic_interpretation φ := by
  intros _ _ h
  induction h with
  | premise h_mem =>
      intro h_all
      exact h_all _ h_mem
  | axiom' h_ax =>
      intro _
      cases h_ax <;> simp only [semantic_interpretation] <;> tauto
  | modusPonens _ _ ih₁ ih₂ =>
      intro h_all
      have h1 := ih₁ h_all
      have h2 := ih₂ h_all
      simp only [semantic_interpretation] at h2
      tauto
  | necessitation _ ih =>
      intro _
      simp only [semantic_interpretation]
      exact not_not.mpr (ih (by simp))

lemma empty_consistent : IsConsistent ∅ :=
  λ h => semantic_interpretation_sound h (by simp)
