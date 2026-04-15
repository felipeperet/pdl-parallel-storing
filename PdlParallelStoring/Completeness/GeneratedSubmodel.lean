import PdlParallelStoring.Completeness.CanonicalModel

open Classical Program Lindenbaum

def reachableWorlds (Γ : MaximalConsistentSet) : Set MaximalConsistentSet :=
  {Δ | canonicalRelation (s₁ ; r₂) Γ Δ}

lemma r₁_functional : ∀ {Γ Δ Ω : MaximalConsistentSet},
    canonicalRelation r₁ Γ Δ →
    canonicalRelation r₁ Γ Ω →
    Δ = Ω := by
  intros Γ Δ Ω h₁ h₂
  simp only [canonicalRelation] at *
  apply Subtype.ext
  apply Set.ext
  intros φ
  constructor
  . intros h_in
    have h_dia : (⟨r₁⟩ φ) ∈ Γ.val := by
      by_contra h_not
      have h_neg_dia : (¬ (⟨r₁⟩ φ)) ∈ Γ.val := mcs_complete h_not
      have h_box_neg : ([r₁] ¬ φ) ∈ Γ.val := by
        apply mcs_is_closed
        apply Deduction.modusPonens
          (Deduction.premise h_neg_dia)
          (weakening (Set.empty_subset Γ.val) (neg_diamond_to_box_neg r₁ φ))
      exact (mcs_no_contradiction h_in) (h₁ h_box_neg)
    have h_box : ([r₁] φ) ∈ Γ.val := by
      apply mcs_is_closed
      apply Deduction.modusPonens
        (Deduction.premise h_dia)
        (Deduction.axiom' (Axiom.functionalR₁ φ))
    exact h₂ h_box
  . intros h_in
    have h_dia : (⟨r₁⟩ φ) ∈ Γ.val := by
      by_contra h_not
      have h_neg_dia : (¬ (⟨r₁⟩ φ)) ∈ Γ.val := mcs_complete h_not
      have h_box_neg : ([r₁] ¬ φ) ∈ Γ.val := by
        apply mcs_is_closed
        apply Deduction.modusPonens
          (Deduction.premise h_neg_dia)
          (weakening (Set.empty_subset Γ.val) (neg_diamond_to_box_neg r₁ φ))
      exact (mcs_no_contradiction h_in) (h₂ h_box_neg)
    have h_box : ([r₁] φ) ∈ Γ.val := by
      apply mcs_is_closed
      apply Deduction.modusPonens
        (Deduction.premise h_dia)
        (Deduction.axiom' (Axiom.functionalR₁ φ))
    exact h₁ h_box

lemma r₂_functional : ∀ {Γ Δ Ω : MaximalConsistentSet},
    canonicalRelation r₂ Γ Δ →
    canonicalRelation r₂ Γ Ω →
    Δ = Ω := by
  intros Γ Δ Ω h₁ h₂
  simp only [canonicalRelation] at *
  apply Subtype.ext
  apply Set.ext
  intros φ
  constructor
  . intros h_in
    have h_dia : (⟨r₂⟩ φ) ∈ Γ.val := by
      by_contra h_not
      have h_neg_dia : (¬ (⟨r₂⟩ φ)) ∈ Γ.val := mcs_complete h_not
      have h_box_neg : ([r₂] ¬ φ) ∈ Γ.val := by
        apply mcs_is_closed
        apply Deduction.modusPonens
          (Deduction.premise h_neg_dia)
          (weakening (Set.empty_subset Γ.val) (neg_diamond_to_box_neg r₂ φ))
      exact (mcs_no_contradiction h_in) (h₁ h_box_neg)
    have h_box : ([r₂] φ) ∈ Γ.val := by
      apply mcs_is_closed
      apply Deduction.modusPonens
        (Deduction.premise h_dia)
        (Deduction.axiom' (Axiom.functionalR₂ φ))
    exact h₂ h_box
  . intros h_in
    have h_dia : (⟨r₂⟩ φ) ∈ Γ.val := by
      by_contra h_not
      have h_neg_dia : (¬ (⟨r₂⟩ φ)) ∈ Γ.val := mcs_complete h_not
      have h_box_neg : ([r₂] ¬ φ) ∈ Γ.val := by
        apply mcs_is_closed
        apply Deduction.modusPonens
          (Deduction.premise h_neg_dia)
          (weakening (Set.empty_subset Γ.val) (neg_diamond_to_box_neg r₂ φ))
      exact (mcs_no_contradiction h_in) (h₂ h_box_neg)
    have h_box : ([r₂] φ) ∈ Γ.val := by
      apply mcs_is_closed
      apply Deduction.modusPonens
        (Deduction.premise h_dia)
        (Deduction.axiom' (Axiom.functionalR₂ φ))
    exact h₁ h_box

lemma s₁r₂_refl : ∀ {Γ : MaximalConsistentSet},
    canonicalRelation (s₁ ; r₂) Γ Γ := by
  intro Γ φ h_in
  exact mcs_is_closed (Deduction.modusPonens
    (Deduction.premise h_in)
    (Deduction.axiom' (Axiom.storeRestoreId φ)))

lemma s₁r₂_symm : ∀ {Γ Δ : MaximalConsistentSet},
    canonicalRelation (s₁ ; r₂) Γ Δ →
    canonicalRelation (s₁ ; r₂) Δ Γ := by
  intros Γ Δ h
  simp [canonicalRelation] at *
  intros φ h_in
  by_contra h_not_prov
  have h_neg_phi_in : (¬ φ) ∈ Γ.val := mcs_complete h_not_prov
  have h_box_dia_in : ([s₁ ; r₂] ⟨s₁ ; r₂⟩ (¬ φ)) ∈ Γ.val := by
    have h_neg_phi : Γ.val ⊢ ¬ φ := Deduction.premise h_neg_phi_in
    have h_box_dia : Γ.val ⊢ [s₁ ; r₂] ⟨s₁ ; r₂⟩ (¬ φ) := by
      apply Deduction.modusPonens h_neg_phi (Deduction.axiom' (Axiom.storeRestoreDiamond (¬ φ)))
    exact mcs_is_closed h_box_dia
  have h_dia : (⟨s₁ ; r₂⟩ ¬ φ) ∈ Δ.val := by
    exact h h_box_dia_in
  exact mcs_no_contradiction h_dia h_in

lemma s₁r₂_trans : ∀ {Γ Δ Θ : MaximalConsistentSet},
    canonicalRelation (s₁ ; r₂) Γ Δ →
    canonicalRelation (s₁ ; r₂) Δ Θ →
    canonicalRelation (s₁ ; r₂) Γ Θ := by
  intros Γ Δ Θ h₁ h₂
  simp only [canonicalRelation] at *
  intros φ h_in
  have h_iter : ([s₁ ; r₂] [s₁ ; r₂] φ) ∈ Γ.val := by
    apply mcs_is_closed
    exact Deduction.modusPonens
      (Deduction.premise h_in) (Deduction.axiom' (Axiom.storeRestoreIterate φ))
  have h_in_delta : ([s₁ ; r₂] φ) ∈ Δ.val := h₁ h_iter
  exact h₂ h_in_delta

lemma r₁_to_s₁ : ∀ {Ω Δ : MaximalConsistentSet},
    canonicalRelation r₁ Ω Δ →
    canonicalRelation s₁ Δ Ω := by
  intros Ω Δ h_r₁
  intro φ h_box_s₁
  by_contra h_not
  have h_neg : (¬ φ) ∈ Ω.val := mcs_complete h_not
  have h_box_r₁ : ([r₁] ⟨s₁⟩ (¬ φ)) ∈ Ω.val := mcs_is_closed
    (Deduction.modusPonens (Deduction.premise h_neg)
      (Deduction.axiom' (Axiom.temporalBackward (¬ φ))))
  have h_dia : (⟨s₁⟩ (¬ φ)) ∈ Δ.val := h_r₁ h_box_r₁
  exact mcs_no_contradiction h_dia h_box_s₁

lemma s₁_to_r₁ : ∀ {Δ Ω : MaximalConsistentSet},
    canonicalRelation s₁ Δ Ω →
    canonicalRelation r₁ Ω Δ := by
  intros Δ Ω h_s₁
  intro φ h_box_r₁
  by_contra h_not
  have h_neg : (¬ φ) ∈ Δ.val := mcs_complete h_not
  have h_box_s₁ : ([s₁] ⟨r₁⟩ (¬ φ)) ∈ Δ.val := mcs_is_closed
    (Deduction.modusPonens (Deduction.premise h_neg)
      (Deduction.axiom' (Axiom.temporalForward (¬ φ))))
  have h_dia : (⟨r₁⟩ (¬ φ)) ∈ Ω.val := h_s₁ h_box_s₁
  exact mcs_no_contradiction h_dia h_box_r₁

lemma r₂_to_s₂ : ∀ {Ω Δ : MaximalConsistentSet},
    canonicalRelation r₂ Ω Δ →
    canonicalRelation s₂ Δ Ω := by
  intros Ω Δ h_r₂
  intro φ h_box_s₂
  by_contra h_not
  have h_neg : (¬ φ) ∈ Ω.val := mcs_complete h_not
  have h_box_r₂ : ([r₂] ⟨s₂⟩ (¬ φ)) ∈ Ω.val := mcs_is_closed
    (Deduction.modusPonens (Deduction.premise h_neg)
      (Deduction.axiom' (Axiom.temporalBackward₂ (¬ φ))))
  have h_dia : (⟨s₂⟩ (¬ φ)) ∈ Δ.val := h_r₂ h_box_r₂
  exact mcs_no_contradiction h_dia h_box_s₂

lemma s₂_to_r₂ : ∀ {Δ Ω : MaximalConsistentSet},
    canonicalRelation s₂ Δ Ω →
    canonicalRelation r₂ Ω Δ := by
  intros Δ Ω h_s₂
  intro φ h_box_r₂
  by_contra h_not
  have h_neg : (¬ φ) ∈ Δ.val := mcs_complete h_not
  have h_box_s₂ : ([s₂] ⟨r₂⟩ (¬ φ)) ∈ Δ.val := mcs_is_closed
    (Deduction.modusPonens (Deduction.premise h_neg)
      (Deduction.axiom' (Axiom.temporalForward₂ (¬ φ))))
  have h_dia : (⟨r₂⟩ (¬ φ)) ∈ Ω.val := h_s₂ h_box_s₂
  exact mcs_no_contradiction h_dia h_box_r₂

lemma star_exists : ∀ {Γ Δ₁ Δ₂ : MaximalConsistentSet},
    (Δ₁ ∈ reachableWorlds Γ) →
    (Δ₂ ∈ reachableWorlds Γ) →
    ∃ Ω, canonicalRelation r₁ Ω Δ₁ ∧ canonicalRelation r₂ Ω Δ₂ := by
  intros Γ Δ₁ Δ₂ h_in₁ h_in₂
  simp only [reachableWorlds] at h_in₁ h_in₂
  let S : Set Formula := {⟨r₁⟩ φ | φ ∈ Δ₁.val} ∪ {⟨r₂⟩ φ | φ ∈ Δ₂.val}
  have h_cons : IsConsistent S := by
    intros h_incons
    obtain ⟨Δ, h_fin, h_sub, h_deriv⟩ := derivation_finite_support h_incons
    let r₁_formulas := {φ | (⟨r₁⟩ φ) ∈ Δ}
    let r₂_formulas := {ψ | (⟨r₂⟩ ψ) ∈ Δ}
    have h_r₁_finite : (r₁_formulas : Set Formula).Finite := by
      have hΔ_fin : Set.Finite Δ := Set.finite_coe_iff.mpr h_fin
      have : r₁_formulas = (λ φ => (⟨r₁⟩ φ)) ⁻¹' Δ := rfl
      rw [this]
      apply Set.Finite.preimage _ hΔ_fin
      intro a _ b _ h
      exact (Formula.diamond.inj h).2
    have h_r₂_finite : (r₂_formulas : Set Formula).Finite := by
      have hΔ_fin : Set.Finite Δ := Set.finite_coe_iff.mpr h_fin
      have : r₂_formulas = (λ ψ => (⟨r₂⟩ ψ)) ⁻¹' Δ := rfl
      rw [this]
      apply Set.Finite.preimage _ hΔ_fin
      intro a _ b _ h
      exact (Formula.diamond.inj h).2
    let L₁_list := h_r₁_finite.toFinset.toList
    let L₂_list := h_r₂_finite.toFinset.toList
    let Φ := list_conjunction L₁_list
    let Ψ := list_conjunction L₂_list
    have h_colapsed_deriv : {⟨r₁⟩ Φ, ⟨r₂⟩ Ψ} ⊢ ⊥' := by
      have h_in_Δ : ∀ (χ : Formula), (χ ∈ Δ) → {⟨r₁⟩ Φ, ⟨r₂⟩ Ψ} ⊢ χ := by
        intros χ χ_in_Δ
        have χ_in_S : χ ∈ S := by exact h_sub χ_in_Δ
        unfold S at χ_in_S
        rcases χ_in_S with ⟨φ, hφ_in, hχ_eq⟩ | ⟨ψ, hψ_in, hχ_eq⟩
        . subst hχ_eq
          have hφ_in_r₁ : φ ∈ r₁_formulas := χ_in_Δ
          have hφ_in_list : φ ∈ L₁_list :=
            Finset.mem_toList.mpr (h_r₁_finite.mem_toFinset.mpr hφ_in_r₁)
          have h_impl : ⊢ Φ → φ := list_conjunction_elim hφ_in_list
          have h_dia : ⊢ (⟨r₁⟩ Φ) → (⟨r₁⟩ φ) := diamond_monotonicity h_impl
          exact
            Deduction.modusPonens
              (Deduction.premise (by simp))
              (weakening (Set.empty_subset _) h_dia)
        . subst hχ_eq
          have hψ_in_r₂ : ψ ∈ r₂_formulas := χ_in_Δ
          have hψ_in_list : ψ ∈ L₂_list :=
            Finset.mem_toList.mpr (h_r₂_finite.mem_toFinset.mpr hψ_in_r₂)
          have h_impl : ⊢ Ψ → ψ := list_conjunction_elim hψ_in_list
          have h_dia : ⊢ (⟨r₂⟩ Ψ) → (⟨r₂⟩ ψ) := diamond_monotonicity h_impl
          exact
            Deduction.modusPonens
              (Deduction.premise (by simp))
              (weakening (Set.empty_subset _) h_dia)
      exact derivation_substitution h_deriv h_in_Δ
    have h_step₁ : {⟨r₁⟩ Φ} ⊢ (⟨r₂⟩ Ψ) → ⊥' := by
      have h_empty_union : ({⟨r₁⟩ Φ} ∪ {⟨r₂⟩ Ψ }) ⊢ ⊥' := by
        apply weakening
        . simp only [Set.union_singleton]
          exact Set.Subset.rfl
        . apply weakening _ h_colapsed_deriv
          intro χ h_in
          cases h_in with
          | inl h =>
              right
              exact h
          | inr h =>
              left
              exact h
      apply deduction_theorem h_empty_union
    have h_step₂ : ∅ ⊢ (⟨r₁⟩ Φ) → (⟨r₂⟩ Ψ) → ⊥' := by
      apply deduction_theorem
      apply weakening (by simp) h_step₁
    have h_step₃ : ∅ ⊢ (⟨r₁⟩ Φ) → ¬ (⟨r₂⟩ Ψ) :=
      impl_chain h_step₂ (Deduction.axiom' (Axiom.negIntro (⟨r₂⟩ Ψ)))
    have h_step₄ : ∅ ⊢ (⟨r₁⟩ Φ) → ([r₂] ¬ Ψ) := impl_chain h_step₃ (neg_diamond_to_box_neg r₂ Ψ)
    have h_step₅ : ∅ ⊢ ([s₁] ⟨r₁⟩ Φ) → ([s₁] [r₂] ¬ Ψ) := box_monotonicity (h_step₄)
    have h_Φ_in_Δ₁ : Φ ∈ Δ₁.val := by
      apply list_conjunction_in_mcs
      intro φ hφ_in_list
      have hφ_in_r₁ : φ ∈ r₁_formulas :=
        h_r₁_finite.mem_toFinset.mp (Finset.mem_toList.mp hφ_in_list)
      have h_dia_in_Δ : (⟨r₁⟩ φ) ∈ Δ := hφ_in_r₁
      have h_dia_in_S : (⟨r₁⟩ φ) ∈ S := h_sub h_dia_in_Δ
      unfold S at h_dia_in_S
      rcases h_dia_in_S with ⟨ψ, hψ_in, hψ_eq⟩ | ⟨ψ, hψ_in, hψ_eq⟩
      . exact (Formula.diamond.inj hψ_eq).2 ▸ hψ_in
      . exact absurd hψ_eq (by simp [Formula.diamond.injEq])
    have h_s₁_r₁_Φ : ([s₁] ⟨r₁⟩ Φ) ∈ Δ₁.val := mcs_is_closed
      (Deduction.modusPonens (Deduction.premise h_Φ_in_Δ₁)
        (Deduction.axiom' (Axiom.temporalForward Φ)))
    have h_s₁_r₂_neg_Ψ : ([s₁] [r₂] ¬ Ψ) ∈ Δ₁.val := mcs_is_closed
      (Deduction.modusPonens (Deduction.premise h_s₁_r₁_Φ)
        (weakening (Set.empty_subset _) h_step₅))
    have h_s₁r₂_neg_Ψ : ([s₁ ; r₂] ¬ Ψ) ∈ Δ₁.val := mcs_is_closed
      (Deduction.modusPonens (Deduction.premise h_s₁_r₂_neg_Ψ)
        (iff_mpr (Deduction.axiom' (Axiom.modalComposition s₁ r₂ (¬ Ψ)))))
    have h_Δ₁_Δ₂ : canonicalRelation (s₁ ; r₂) Δ₁ Δ₂ :=
      s₁r₂_trans (s₁r₂_symm h_in₁) h_in₂
    have h_neg_Ψ_in_Δ₂ : (¬ Ψ) ∈ Δ₂.val := h_Δ₁_Δ₂ h_s₁r₂_neg_Ψ
    have h_Ψ_in_Δ₂ : Ψ ∈ Δ₂.val := by
      apply list_conjunction_in_mcs
      intro ψ hψ_in_list
      have hψ_in_r₂ : ψ ∈ r₂_formulas :=
        h_r₂_finite.mem_toFinset.mp (Finset.mem_toList.mp hψ_in_list)
      have h_dia_in_Δ : (⟨r₂⟩ ψ) ∈ Δ := hψ_in_r₂
      have h_dia_in_S : (⟨r₂⟩ ψ) ∈ S := h_sub h_dia_in_Δ
      unfold S at h_dia_in_S
      rcases h_dia_in_S with ⟨χ, hχ_in, hχ_eq⟩ | ⟨χ, hχ_in, hχ_eq⟩
      . exact absurd hχ_eq (by simp [Formula.diamond.injEq])
      . exact (Formula.diamond.inj hχ_eq).2 ▸ hχ_in
    exact mcs_no_contradiction h_Ψ_in_Δ₂ h_neg_Ψ_in_Δ₂
  obtain ⟨Ω, h_ext⟩ := lindenbaum h_cons
  exact ⟨Ω,
    λ {φ} h_box => by
      by_contra h_not
      have h_neg : (¬ φ) ∈ Δ₁.val := mcs_complete h_not
      have h_dia : (⟨r₁⟩ (¬ φ)) ∈ Ω.val :=
        h_ext (Set.mem_union_left _ ⟨¬ φ, h_neg, rfl⟩)
      exact mcs_no_contradiction h_dia h_box,
    λ {φ} h_box => by
      by_contra h_not
      have h_neg : (¬ φ) ∈ Δ₂.val := mcs_complete h_not
      have h_dia : (⟨r₂⟩ (¬ φ)) ∈ Ω.val :=
        h_ext (Set.mem_union_right _ ⟨¬ φ, h_neg, rfl⟩)
      exact mcs_no_contradiction h_dia h_box⟩

def generatedSubmodel (Γ : MaximalConsistentSet) : Model where
  F := {
    W := reachableWorlds Γ
    R := λ α ⟨Δ, _⟩  ⟨Δ', _⟩ => canonicalRelation α Δ Δ'
    nonempty := ⟨Γ, s₁r₂_refl⟩
  }
  V := λ lit ⟨Δ, _⟩ => canonicalValuation lit Δ

lemma reach_closed : ∀ {Γ Δ Δ' : MaximalConsistentSet} {α : Program},
    (Δ ∈ reachableWorlds Γ) →
    canonicalRelation α Δ Δ' →
    Δ' ∈ reachableWorlds Γ := by
  intros Γ Δ Δ' α h_reach h_rel
  simp only [reachableWorlds, Set.mem_setOf_eq] at *
  intro φ h_in
  have h_iter : ([s₁ ; r₂] [s₁ ; r₂] φ) ∈ Γ.val := mcs_is_closed
    (Deduction.modusPonens (Deduction.premise h_in)
      (Deduction.axiom' (Axiom.storeRestoreIterate φ)))
  have h_delta : ([s₁ ; r₂] φ) ∈ Δ.val := h_reach h_iter
  have h_alpha : ([α] φ) ∈ Δ.val := mcs_is_closed
    (Deduction.modusPonens (Deduction.premise h_delta)
      (Deduction.axiom' (Axiom.equivSubsume α φ)))
  exact h_rel h_alpha

instance generatedSubmodelState (Γ : MaximalConsistentSet) :
    State (reachableWorlds Γ) where
  E := λ _ _ => True
  equiv := ⟨λ _ => trivial, λ _ => trivial, λ _ _ => trivial⟩
  star := λ ⟨Δ₁, h₁⟩ ⟨Δ₂, h₂⟩ =>
    { Ω : reachableWorlds Γ |
      canonicalRelation r₁ Ω.val Δ₁ ∧ canonicalRelation r₂ Ω.val Δ₂ }
  separated := by
    intro ⟨z, hz⟩ ⟨x, hx⟩ ⟨y, hy⟩ ⟨x', hx'⟩ ⟨y', hy'⟩
    intro ⟨hr₁, hr₂⟩ ⟨hr₁', hr₂'⟩
    exact ⟨Subtype.ext (r₁_functional hr₁ hr₁'), Subtype.ext (r₂_functional hr₂ hr₂')⟩
  serial := by
    intro ⟨Δ₁, h₁⟩ ⟨Δ₂, h₂⟩
    obtain ⟨Ω, hΩ_r₁, hΩ_r₂⟩ := star_exists h₁ h₂
    exact ⟨⟨Ω, reach_closed h₁ (r₁_to_s₁ hΩ_r₁)⟩, hΩ_r₁, hΩ_r₂⟩
  nonempty := ⟨⟨Γ, s₁r₂_refl⟩⟩

lemma has_r₁_decomp {Ω Δ : MaximalConsistentSet}
    (h : canonicalRelation r₁ Ω Δ) : (⟨r₁⟩ (¬ ⊥' : Formula)) ∈ Ω.val := by
  by_contra h_not
  have not_not_phi_in : (¬ (¬ ⊥' : Formula)) ∈ Δ.val :=
    h (mcs_is_closed (Deduction.modusPonens (Deduction.premise (mcs_complete h_not))
      (weakening (Set.empty_subset _) (neg_diamond_to_box_neg r₁ (¬ ⊥' : Formula)))))
  exact mcs_no_contradiction (mcs_complete false_not_in_mcs) not_not_phi_in

lemma has_r₂_decomp {Ω Δ : MaximalConsistentSet}
    (h : canonicalRelation r₂ Ω Δ) : (⟨r₂⟩ (¬ ⊥' : Formula)) ∈ Ω.val := by
  by_contra h_not
  have not_not_phi_in : (¬ (¬ ⊥' : Formula)) ∈ Δ.val :=
    h (mcs_is_closed (Deduction.modusPonens (Deduction.premise (mcs_complete h_not))
      (weakening (Set.empty_subset _) (neg_diamond_to_box_neg r₂ (¬ ⊥' : Formula)))))
  exact mcs_no_contradiction (mcs_complete false_not_in_mcs) not_not_phi_in

instance generatedSubmodelProperStandard (Γ : MaximalConsistentSet) :
    ProperStandard₀ (generatedSubmodel Γ) where
  comp := by
    intros α β
    funext ⟨Δ, hΔ⟩ ⟨Δ', hΔ'⟩
    apply propext
    constructor
    · intro h
      simp only [generatedSubmodel] at h ⊢
      have h_comp : Relation.Comp (canonicalRelation α) (canonicalRelation β) Δ Δ' := by
        have h_comp' := canonicalStandard.comp (α := α) (β := β)
        simp only [canonicalModel, canonicalFrame] at h_comp'
        rewrite [h_comp'] at h
        exact h
      obtain ⟨mid, hα, hβ⟩ := h_comp
      have h_mid_reach : mid ∈ reachableWorlds Γ := reach_closed hΔ hα
      exact ⟨⟨mid, h_mid_reach⟩, hα, hβ⟩
    · intros h
      simp only [generatedSubmodel, Relation.Comp] at h
      obtain ⟨⟨mid, hmid⟩, hα, hβ⟩ := h
      intro φ h_box_comp
      have h_nested : ([α] [β] φ) ∈ Δ.val := mcs_is_closed
        (Deduction.modusPonens (Deduction.premise h_box_comp)
          (iff_mp (Deduction.axiom' (Axiom.modalComposition α β φ))))
      exact hβ (hα h_nested)
  choice := by
    intros α β
    funext ⟨Δ, hΔ⟩ ⟨Δ', hΔ'⟩
    apply propext
    constructor
    . intro h
      simp [generatedSubmodel] at h ⊢
      have h_choice := canonicalStandard.choice (α := α) (β := β)
      simp only [canonicalModel, canonicalFrame] at h_choice
      rewrite [h_choice] at h
      exact h
    · intro h
      simp only [generatedSubmodel] at h ⊢
      have h_choice := canonicalStandard.choice (α := α) (β := β)
      simp only [canonicalModel, canonicalFrame] at h_choice
      rewrite [h_choice]
      exact h
  S := generatedSubmodelState Γ
  respects_equiv := λ _ => trivial
  s₁ := by
    intro ⟨Ω, hΩ⟩ ⟨Δ, hΔ⟩
    simp only [generatedSubmodel]
    constructor
    · intro h_s₁
      have h_r₁ : canonicalRelation r₁ Δ Ω := s₁_to_r₁ h_s₁
      have h_dia_r₂ : (⟨r₂⟩ (¬ ⊥' : Formula)) ∈ Δ.val :=
        mcs_is_closed (Deduction.modusPonens (Deduction.premise (has_r₁_decomp h_r₁))
          (iff_mp (Deduction.axiom' Axiom.sameDomain)))
      obtain ⟨Δ₂, h_r₂_rel, _⟩ := existence_lemma h_dia_r₂
      have h_Δ₂_reach : Δ₂ ∈ reachableWorlds Γ := reach_closed hΔ h_r₂_rel
      exact ⟨⟨Ω, hΩ⟩, ⟨Δ₂, h_Δ₂_reach⟩, rfl, h_r₁, h_r₂_rel⟩
    · intro ⟨s, t, h_eq, h_mem⟩
      obtain ⟨h_r₁, _⟩ := h_mem
      intro φ h_box
      have h_box' : ([s₁] φ) ∈ s.val.val := by rw [← h_eq]; exact h_box
      exact r₁_to_s₁ h_r₁ h_box'
  s₂ := by
    intro ⟨Ω, hΩ⟩ ⟨Δ, hΔ⟩
    simp only [generatedSubmodel]
    constructor
    · intro h_s₂
      have h_r₂ : canonicalRelation r₂ Δ Ω := s₂_to_r₂ h_s₂
      have h_dia_r₁ : (⟨r₁⟩ (¬ ⊥' : Formula)) ∈ Δ.val :=
        mcs_is_closed (Deduction.modusPonens (Deduction.premise (has_r₂_decomp h_r₂))
          (iff_mpr (Deduction.axiom' Axiom.sameDomain)))
      obtain ⟨Δ₁, h_r₁_rel, _⟩ := existence_lemma h_dia_r₁
      have h_Δ₁_reach : Δ₁ ∈ reachableWorlds Γ := reach_closed hΔ h_r₁_rel
      exact ⟨⟨Δ₁, h_Δ₁_reach⟩, ⟨Ω, hΩ⟩, rfl, h_r₁_rel, h_r₂⟩
    · intro ⟨s, t, h_eq, h_mem⟩
      obtain ⟨_, h_r₂⟩ := h_mem
      intro φ h_box
      have h_box' : ([s₂] φ) ∈ t.val.val := by rw [← h_eq]; exact h_box
      exact r₂_to_s₂ h_r₂ h_box'
  r₁ := by
    intro ⟨Ω, hΩ⟩ ⟨Δ, hΔ⟩
    simp only [generatedSubmodel]
    constructor
    · intro h_r₁
      have h_dia_r₂ : (⟨r₂⟩ (¬ ⊥' : Formula)) ∈ Ω.val :=
        mcs_is_closed (Deduction.modusPonens (Deduction.premise (has_r₁_decomp h_r₁))
          (iff_mp (Deduction.axiom' Axiom.sameDomain)))
      obtain ⟨Δ₂, h_r₂_rel, _⟩ := existence_lemma h_dia_r₂
      have h_Δ₂_reach : Δ₂ ∈ reachableWorlds Γ := reach_closed hΩ h_r₂_rel
      exact ⟨⟨Δ, hΔ⟩, ⟨Δ₂, h_Δ₂_reach⟩, ⟨h_r₁, h_r₂_rel⟩, rfl⟩
    · intro ⟨s, t, h_mem, h_eq⟩
      obtain ⟨h_r₁, _⟩ := h_mem
      intro φ h_box
      have h_result := h_r₁ h_box
      rw [← h_eq] at h_result
      exact h_result
  r₂ := by
    intro ⟨Ω, hΩ⟩ ⟨Δ, hΔ⟩
    simp only [generatedSubmodel]
    constructor
    · intro h_r₂
      have h_dia_r₁ : (⟨r₁⟩ (¬ ⊥' : Formula)) ∈ Ω.val :=
        mcs_is_closed (Deduction.modusPonens (Deduction.premise (has_r₂_decomp h_r₂))
          (iff_mpr (Deduction.axiom' Axiom.sameDomain)))
      obtain ⟨Δ₁, h_r₁_rel, _⟩ := existence_lemma h_dia_r₁
      have h_Δ₁_reach : Δ₁ ∈ reachableWorlds Γ := reach_closed hΩ h_r₁_rel
      exact ⟨⟨Δ₁, h_Δ₁_reach⟩, ⟨Δ, hΔ⟩, ⟨h_r₁_rel, h_r₂⟩, rfl⟩
    · intro ⟨s, t, h_mem, h_eq⟩
      obtain ⟨_, h_r₂⟩ := h_mem
      intro φ h_box
      have h_result := h_r₂ h_box
      rw [← h_eq] at h_result
      exact h_result

def gamma_is_world (Γ : MaximalConsistentSet) : (generatedSubmodel Γ).F.W :=
  ⟨Γ, s₁r₂_refl⟩

lemma submodel_truth_lemma_aux (Γ : MaximalConsistentSet) :
    ∀ (φ : Formula) (w : (generatedSubmodel Γ).F.W),
    ((generatedSubmodel Γ, w) ⊨ φ) ↔ φ ∈ w.val.val := by
  intro φ
  induction φ using Formula.rec (motive_2 := λ _ => True) with
  | false =>
      intro ⟨Ω, hΩ⟩
      constructor
      · intro h; simp [satisfies] at h
      · intro h; exact absurd (Deduction.premise h) Ω.property.1
  | atom p =>
      intro ⟨Ω, hΩ⟩
      constructor
      · intro h; simp [satisfies, generatedSubmodel, canonicalValuation] at h; exact h
      · intro h; simp [satisfies, generatedSubmodel, canonicalValuation]; exact h
  | neg ψ ih =>
      intro ⟨Ω, hΩ⟩
      constructor
      · intro h; simp [satisfies] at h
        exact mcs_complete ((ih ⟨Ω, hΩ⟩).not.mp h)
      · intro h; simp [satisfies]
        exact λ h_sat => mcs_no_contradiction ((ih ⟨Ω, hΩ⟩).mp h_sat) h
  | conj ψ χ ih_ψ ih_χ =>
      intro ⟨Ω, hΩ⟩
      constructor
      · intro h
        simp [satisfies] at h
        exact mcs_is_closed
          (Deduction.modusPonens (Deduction.premise ((ih_χ ⟨Ω, hΩ⟩).mp h.2))
            (Deduction.modusPonens (Deduction.premise ((ih_ψ ⟨Ω, hΩ⟩).mp h.1))
              (Deduction.axiom' (Axiom.conjIntro ψ χ))))
      · intro h
        simp [satisfies]
        exact ⟨ (ih_ψ ⟨Ω, hΩ⟩).mpr (mcs_is_closed (Deduction.modusPonens (Deduction.premise h)
                  (Deduction.axiom' (Axiom.conjElimL ψ χ))))
              , (ih_χ ⟨Ω, hΩ⟩).mpr (mcs_is_closed (Deduction.modusPonens (Deduction.premise h)
                  (Deduction.axiom' (Axiom.conjElimR ψ χ)))) ⟩
  | diamond α ψ _ ih =>
      intro ⟨Ω, hΩ⟩
      constructor
      · intro h
        simp [satisfies] at h
        obtain ⟨⟨Δ, hΔ_reach⟩, h_rel, h_sat⟩ := h
        have hψ_in : ψ ∈ Δ.val := (ih ⟨Δ, hΔ_reach⟩).mp h_sat
        by_contra h_not
        exact mcs_no_contradiction hψ_in
          (h_rel (mcs_is_closed (Deduction.modusPonens
            (Deduction.premise (mcs_complete h_not))
            (weakening (Set.empty_subset _) (neg_diamond_to_box_neg α ψ)))))
      · intro h
        simp [satisfies]
        obtain ⟨Δ, h_rel, hψ⟩ := existence_lemma h
        have hΔ_reach : Δ ∈ reachableWorlds Γ := reach_closed hΩ h_rel
        exact ⟨⟨Δ, hΔ_reach⟩, h_rel, (ih ⟨Δ, hΔ_reach⟩).mpr hψ⟩
  | atomic p => trivial
  | comp α β _ _ => trivial
  | choice α β _ _ => trivial
  | iter α _ => trivial
  | parallel α β _ _ => trivial
  | test φ _ => trivial
  | s₁ => trivial
  | s₂ => trivial
  | r₁ => trivial
  | r₂ => trivial

lemma submodel_truth_lemma : ∀ {Γ : MaximalConsistentSet}
    {w : (generatedSubmodel Γ).F.W} {φ : Formula},
    ((generatedSubmodel Γ, w) ⊨ φ) ↔ φ ∈ w.val.val :=
  λ {Γ w φ} => submodel_truth_lemma_aux Γ φ w
