import PdlParallelStoring.Semantics
import PdlParallelStoring.Completeness.Lindenbaum

open Classical Lindenbaum

def canonicalFrame : Frame where
  W := MaximalConsistentSet
  R := canonicalRelation
  nonempty := by
    obtain ⟨Γ, _⟩ := lindenbaum empty_consistent
    exact ⟨Γ⟩

def canonicalValuation (lit : Literal) (Γ : MaximalConsistentSet) : Prop :=
  (Formula.atom lit) ∈ Γ.val

def canonicalModel : Model where
  F := canonicalFrame
  V := canonicalValuation

lemma list_disjunction_not_in_mcs : ∀ {L : List Formula} {Δ : MaximalConsistentSet},
    (∀ ψ ∈ L, ψ ∉ Δ.val) →
    list_disjunction L ∉ Δ.val := by
  intro L
  induction L with
  | nil =>
      intro Δ _
      simp only [list_disjunction]
      exact false_not_in_mcs
  | cons φ rest ih =>
      intro Δ h_all
      simp only [list_disjunction]
      have h_φ_not : φ ∉ Δ.val := h_all φ (.head rest)
      have h_rest_not : list_disjunction rest ∉ Δ.val :=
        ih (λ ψ hψ => h_all ψ (.tail φ hψ))
      have h_neg_φ : (¬ φ) ∈ Δ.val := mcs_complete h_φ_not
      have h_neg_rest : (¬ (list_disjunction rest)) ∈ Δ.val := mcs_complete h_rest_not
      let χ : Formula := (¬ φ) ∧ (¬ (list_disjunction rest))
      have h_conj : χ ∈ Δ.val := mcs_is_closed
        (Deduction.modusPonens (Deduction.premise h_neg_rest)
          (Deduction.modusPonens (Deduction.premise h_neg_φ)
            (Deduction.axiom' (Axiom.conjIntro (¬ φ) (¬ (list_disjunction rest))))))
      exact mcs_no_contradiction h_conj

instance canonicalStandard : Standard₀ canonicalModel where
  comp := by
    intros α β
    funext Γ Δ
    apply propext
    constructor
    · intro h_comp_rel
      let Γ_α : Set Formula := {φ | ([α] φ) ∈ Γ.val}
      let S_β : Set Formula := {χ : Formula | ∃ ψ : Formula, (χ = ¬ ([β] ψ)) ∧ (ψ ∉ Δ.val)}
      have h_cons : IsConsistent (Γ_α ∪ S_β) := by
        intro h_incons
        obtain ⟨Δ', h_fin, h_sub, h_deriv⟩ := derivation_finite_support h_incons
        let Δ'_α := {ψ ∈ Δ' | ψ ∈ Γ_α}
        let Δ'_β := {ψ ∈ Δ' | ψ ∈ S_β}
        have h_union : Δ'_α ∪ Δ'_β = Δ' := by
          ext ψ
          constructor
          . intro h
            cases h with
            | inl h => exact h.1
            | inr h => exact h.1
          . intro h
            have := h_sub h
            cases this with
            | inl h' => left; exact ⟨h, h'⟩
            | inr h' => right; exact ⟨h, h'⟩
        have h_deriv' : Δ'_α ∪ Δ'_β ⊢ ⊥' := h_union ▸ h_deriv
        haveI := h_fin
        have h_fin_set : Set.Finite Δ' := Set.toFinite Δ'
        have h_fin_β : Set.Finite Δ'_β := h_fin_set.subset (λ x hx => hx.1)
        let witness_of : Formula → Formula := λ χ =>
          if h : χ ∈ S_β then Classical.choose h else ⊥'
        have witness_of_spec (χ : Formula) (hχ : χ ∈ S_β) :
            (χ = ¬ ([β] (witness_of χ))) ∧ (¬ (witness_of χ ∈ Δ.val)) := by
          show (χ = ¬ ([β] (if h : χ ∈ S_β then Classical.choose h else ⊥')))
               ∧ (¬ ((if h : χ ∈ S_β then Classical.choose h else ⊥') ∈ Δ.val))
          rw [dif_pos hχ]
          exact Classical.choose_spec hχ
        let L := h_fin_β.toFinset.toList
        have hL_to_mem (χ : Formula) (hχ : χ ∈ L) : χ ∈ Δ'_β :=
          h_fin_β.mem_toFinset.mp (Finset.mem_toList.mp hχ)
        have hL_of_mem (χ : Formula) (hχ : χ ∈ Δ'_β) : χ ∈ L :=
          Finset.mem_toList.mpr (h_fin_β.mem_toFinset.mpr hχ)
        have hL_S (χ : Formula) (hχ : χ ∈ L) : χ ∈ S_β := (hL_to_mem χ hχ).2
        let witness_list : List Formula := L.map witness_of
        let box_list : List Formula := witness_list.map (box β)
        have h_neg_eq (χ : Formula) (hχ : χ ∈ L) :
            χ = ¬ ([β] (witness_of χ)) :=
          (witness_of_spec χ (hL_S χ hχ)).1
        have h_mem_neg (χ : Formula) (hχ : χ ∈ L) :
            χ ∈ (box_list.map Formula.neg) := by
          rw [h_neg_eq χ hχ]
          show (¬ ([β] (witness_of χ))) ∈
            ((L.map witness_of).map (box β)).map Formula.neg
          exact List.mem_map.mpr ⟨[β] (witness_of χ),
            List.mem_map.mpr ⟨witness_of χ,
              List.mem_map.mpr ⟨χ, hχ, rfl⟩, rfl⟩, rfl⟩
        have h_sub_neg : Δ'_β ⊆ ↑(box_list.map Formula.neg).toFinset := by
          intro χ hχ
          simp only [Finset.mem_coe, List.mem_toFinset]
          exact h_mem_neg χ (hL_of_mem χ hχ)
        have h_deriv_neg : Δ'_α ∪ ↑(box_list.map Formula.neg).toFinset ⊢ ⊥' :=
          weakening (Set.union_subset_union_right _ h_sub_neg) h_deriv'
        have h_disj : Δ'_α ⊢ list_disjunction box_list := neg_list_to_disj h_deriv_neg
        have h_box_disj : Δ'_α ⊢ [β] (list_disjunction witness_list) :=
          Deduction.modusPonens h_disj
            (weakening (Set.empty_subset _) (list_disjunction_box_imp witness_list))
        have h_alpha_box : Γ.val ⊢ [α] ([β] (list_disjunction witness_list)) :=
          box_of_derivation h_box_disj (λ ψ hψ => hψ.2)
        have h_comp_box : ([(α ; β)] (list_disjunction witness_list)) ∈ Γ.val := by
          apply mcs_is_closed
          exact Deduction.modusPonens h_alpha_box
            (iff_mpr (Deduction.axiom' (Axiom.modalComposition α β _)))
        have h_disj_in : list_disjunction witness_list ∈ Δ.val :=
          h_comp_rel h_comp_box
        have h_witnesses_not_in : ∀ ψ ∈ witness_list, ψ ∉ Δ.val := by
          intro ψ hψ
          obtain ⟨χ, hχ_mem, hχ_eq⟩ := List.mem_map.mp hψ
          rw [← hχ_eq]
          exact (witness_of_spec χ (hL_S χ hχ_mem)).2
        exact list_disjunction_not_in_mcs h_witnesses_not_in h_disj_in
      obtain ⟨mid, h_ext⟩ := lindenbaum h_cons
      exact ⟨mid,
        λ h => h_ext (Set.mem_union_left _ h),
        λ {φ} h_box => by
          by_contra h_not
          exact mcs_no_contradiction h_box
            (h_ext (Set.mem_union_right _ ⟨φ, ⟨rfl, h_not⟩⟩))⟩
    · intro ⟨mid, hα, hβ⟩
      intro φ h_box_comp
      have h_comp_to_nested : Γ.val ⊢ ([α ; β] φ) → ([α] [β] φ) :=
        iff_mp (Deduction.axiom' (Axiom.modalComposition α β φ))
      have h_box_box : ([α] [β] φ) ∈ Γ.val :=
        mcs_is_closed (Deduction.modusPonens (Deduction.premise h_box_comp) h_comp_to_nested)
      exact hβ (hα h_box_box)
  choice := by
    intros α β
    funext Γ Δ
    apply propext
    constructor
    · intro h_union
      by_contra h_neg
      have h_not_α : ¬ canonicalRelation α Γ Δ := λ h => h_neg (Or.inl h)
      have h_not_β : ¬ canonicalRelation β Γ Δ := λ h => h_neg (Or.inr h)
      have hα_witness : ∃ φ : Formula, (([α] φ) ∈ Γ.val) ∧ (φ ∉ Δ.val) := by
        by_contra h_no
        push_neg at h_no
        exact h_not_α (λ {φ} h => h_no φ h)
      have hβ_witness : ∃ φ : Formula, (([β] φ) ∈ Γ.val) ∧ (φ ∉ Δ.val) := by
        by_contra h_no
        push_neg at h_no
        exact h_not_β (λ {φ} h => h_no φ h)
      obtain ⟨φ₁, hα₁, hφ₁_not⟩ := hα_witness
      obtain ⟨φ₂, hβ₂, hφ₂_not⟩ := hβ_witness
      let neg_conj : Formula := (¬ φ₁) ∧ (¬ φ₂)
      have h_box_α_disj : ([α] (φ₁ ∨ φ₂)) ∈ Γ.val := mcs_is_closed
        (Deduction.modusPonens (Deduction.premise hα₁)
          (weakening (Set.empty_subset _) (box_monotonicity disj_intro_left)))
      have h_box_β_disj : ([β] (φ₁ ∨ φ₂)) ∈ Γ.val := mcs_is_closed
        (Deduction.modusPonens (Deduction.premise hβ₂)
          (weakening (Set.empty_subset _) (box_monotonicity disj_intro_right)))
      have h_conj_box : (([α] (φ₁ ∨ φ₂)) ∧ ([β] (φ₁ ∨ φ₂))) ∈ Γ.val := mcs_is_closed
        (Deduction.modusPonens (Deduction.premise h_box_β_disj)
          (Deduction.modusPonens (Deduction.premise h_box_α_disj)
            (Deduction.axiom' (Axiom.conjIntro ([α] (φ₁ ∨ φ₂)) ([β] (φ₁ ∨ φ₂))))))
      have h_choice_box : ([α ∪ β] (φ₁ ∨ φ₂)) ∈ Γ.val := mcs_is_closed
        (Deduction.modusPonens (Deduction.premise h_conj_box)
          (iff_mpr (Deduction.axiom' (Axiom.modalChoice α β (φ₁ ∨ φ₂)))))
      have h_disj_in : (φ₁ ∨ φ₂) ∈ Δ.val := h_union h_choice_box
      have h_neg₁ : (¬ φ₁) ∈ Δ.val := mcs_complete hφ₁_not
      have h_neg₂ : (¬ φ₂) ∈ Δ.val := mcs_complete hφ₂_not
      have h_conj_neg : neg_conj ∈ Δ.val := mcs_is_closed
        (Deduction.modusPonens (Deduction.premise h_neg₂)
          (Deduction.modusPonens (Deduction.premise h_neg₁)
            (Deduction.axiom' (Axiom.conjIntro (¬ φ₁) (¬ φ₂)))))
      exact absurd h_disj_in (mcs_no_contradiction h_conj_neg)
    · intro h
      cases h with
      | inl hα =>
          intro φ h_box_choice
          have h_conj : (([α] φ) ∧ ([β] φ)) ∈ Γ.val := mcs_is_closed
            (Deduction.modusPonens (Deduction.premise h_box_choice)
              (iff_mp (Deduction.axiom' (Axiom.modalChoice α β φ))))
          have h_left : ([α] φ) ∈ Γ.val := mcs_is_closed
            (Deduction.modusPonens (Deduction.premise h_conj)
              (Deduction.axiom' (Axiom.conjElimL ([α] φ) ([β] φ))))
          exact hα h_left
      | inr hβ =>
          intro φ h_box_choice
          have h_conj : (([α] φ) ∧ ([β] φ)) ∈ Γ.val := mcs_is_closed
            (Deduction.modusPonens (Deduction.premise h_box_choice)
              (iff_mp (Deduction.axiom' (Axiom.modalChoice α β φ))))
          have h_right : ([β] φ) ∈ Γ.val := mcs_is_closed
            (Deduction.modusPonens (Deduction.premise h_conj)
              (Deduction.axiom' (Axiom.conjElimR ([α] φ) ([β] φ))))
          exact hβ h_right

lemma existence_lemma : ∀ {Γ : MaximalConsistentSet} {α : Program} {φ : Formula},
    ((⟨α⟩ φ) ∈ Γ.val) →
    ∃ (Δ : MaximalConsistentSet), canonicalRelation α Γ Δ ∧ φ ∈ Δ.val := by
  intro Γ α φ h_in
  let Γ_α : Set Formula := {ψ | ([α] ψ) ∈ Γ.val}
  have h_cons : IsConsistent (Γ_α ∪ {φ}) := by
    intro h_incons
    obtain ⟨Δ, h_fin, h_sub, h_deriv⟩ := derivation_finite_support h_incons
    let Δ_α := Δ ∩ Γ_α
    have h_sub2 : Δ ⊆ Δ_α ∪ {φ} := by
      intro ψ h_mem
      cases h_sub h_mem with
      | inl h => left; exact ⟨h_mem, h⟩
      | inr h => right; exact h
    have h_delta_phi : Δ_α ∪ {φ} ⊢ ⊥' := weakening h_sub2 h_deriv
    have h_delta_neg : Δ_α ⊢ (¬ φ) := by
      apply Deduction.modusPonens
      . exact deduction_theorem h_delta_phi
      . exact Deduction.axiom' (Axiom.negIntro φ)
    have h_box_neg : Γ.val ⊢ ([α] ¬ φ) :=
      box_of_derivation h_delta_neg (λ ψ h => h.2)
    have h_in_Γ : ([α] ¬ φ) ∈ Γ.val := mcs_is_closed h_box_neg
    have h_incons_Γ : Γ.val ⊢ ⊥' :=
      diamond_box_neg_inconsistent
        (Deduction.premise h_in)
        (Deduction.premise h_in_Γ)
    exact Γ.property.1 h_incons_Γ
  obtain ⟨Δ, h_ext⟩ := lindenbaum h_cons
  exact
    ⟨ Δ
    , λ h_box => h_ext (Set.mem_union_left _ h_box)
    , h_ext (Set.mem_union_right _ rfl)
    ⟩
