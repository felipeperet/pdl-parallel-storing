import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Basic

import PdlParallelStoring.Syntax
import PdlParallelStoring.Semantics
import PdlParallelStoring.AxiomaticSystem

open Program

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

lemma mcs_no_contradiction : ∀ {Γ : MaximalConsistentSet} {φ : Formula},
    (φ ∈ Γ.val) →
    (¬ φ) ∉ Γ.val := by
  intros Γ φ h_phi_in h_not_phi_in
  simp only [MaximalConsistentSet] at Γ
  obtain ⟨h_consistent, _⟩ := Γ.property
  apply h_consistent
  have h_derives_phi : Γ ⊢ φ := Deduction.premise Γ φ h_phi_in
  have h_derives_not_phi : Γ ⊢ ¬ φ := Deduction.premise Γ (¬ φ) h_not_phi_in
  have h_conj : Γ ⊢ (φ ∧ ¬ φ) := by
    have h_conj_intro : Γ ⊢ (φ → (¬ φ) → (φ ∧ ¬ φ)) := by
      apply Deduction.axiom'
      apply Axiom.conjIntro
    have h_step : Γ ⊢ (¬ φ) → (φ ∧ ¬ φ) :=
      Deduction.modusPonens Γ φ ((¬ φ) → (φ ∧ ¬ φ)) h_derives_phi h_conj_intro
    exact Deduction.modusPonens Γ (¬ φ) (φ ∧ ¬ φ) h_derives_not_phi h_step
  have h_contra_intro : Γ ⊢ ((φ ∧ ¬ φ) → ⊥') := by
    apply Deduction.axiom'
    apply Axiom.contradiction
  exact Deduction.modusPonens Γ (φ ∧ ¬ φ) ⊥' h_conj h_contra_intro

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

lemma insert_preserves_consistency : ∀ {opt_φ : Option Formula} {Γ : Set Formula},
    IsConsistent Γ →
    IsConsistent (insert opt_φ Γ) := by
  intros opt_φ Γ h_consistent
  cases opt_φ with
  | none => exact h_consistent
  | some φ =>
      rewrite [insert]
      split_ifs with h
      . exact h
      . have h_either : IsConsistent (Γ ∪ {φ}) ∨ IsConsistent (Γ ∪ {¬ φ}) :=
          consistency_either h_consistent
        cases h_either with
        | inl _ => contradiction
        | inr h_right => exact h_right

lemma delta_preserves_consistency : ∀ {Γ : Set Formula} {n : Nat},
    IsConsistent Γ →
    IsConsistent (delta Γ n) := by
  intros Γ n h_consistent
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

lemma derivation_finite_support : ∀ {Γ : Set Formula} {φ : Formula},
    (Γ ⊢ φ) →
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
  | some _ =>
      simp only [insert]
      split_ifs <;> (left; exact h_in)

lemma delta_monotone : ∀ {Γ : Set Formula} {m n : Nat},
    (m ≤ n) →
    (delta Γ m ⊆ delta Γ n) := by
  intros _ _ _ h_le
  induction h_le with
  | refl => rfl
  | step _ ih => exact subset_trans ih insert_subset

lemma finite_subset_in_some_delta : ∀ {Γ : Set Formula} {Δ : Set Formula},
    Finite Δ →
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
            intros
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
      delta_preserves_consistency h_consistent
    exact h_delta_consistent h_delta_inconsistent
  . intros φ h_not_in h_consistent_with_phi
    have ⟨n, h_decode⟩ : ∃ n, decode n = some φ := by
      use encode φ
      exact countable
    have h_delta_succ : delta Γ (n + 1) = insert (some φ) (delta Γ n) := by rw [delta, h_decode]
    rw [insert] at h_delta_succ
    split_ifs at h_delta_succ with h_cons
    . have h_in_delta : φ ∈ delta Γ (n + 1) := by
        simp only [h_delta_succ, Set.union_singleton, Set.mem_insert_iff, true_or]
      have h_in : φ ∈ max Γ := by
        simp only [max, Set.mem_iUnion]
        exists n + 1
      apply h_not_in h_in
    . have h_delta_sub_max : delta Γ n ⊆ max Γ := by
        simp only [Set.subset_def]
        intros ψ ψ_in
        simp only [max, Set.mem_iUnion]
        exists n
      have h_delta_derives_false : delta Γ n ∪ {φ} ⊢ ⊥' := by
        simp only [IsConsistent, Set.insert_eq, not_not] at h_cons
        exact h_cons
      have h_max_derives_false : max Γ ∪ {φ} ⊢ ⊥' := by
        apply weakening (Γ := delta Γ n ∪ {φ})
        . simp only [Set.subset_def]
          intros ψ ψ_in
          simp only [max, Set.mem_union, Set.mem_singleton_iff] at ψ_in ⊢
          cases ψ_in with
          | inl ψ_in₂ =>
              left
              simp only [Set.mem_iUnion]
              exists n
          | inr ψ_eq =>
              right
              exact ψ_eq
        . exact h_delta_derives_false
      exact h_consistent_with_phi h_max_derives_false

lemma lindenbaum : ∀ {Γ : Set Formula},
    IsConsistent Γ →
    ∃ (Δ : MaximalConsistentSet), Γ ⊆ Δ.val := by
  intros Γ h_consistent
  have h_max : IsMaximalConsistent (max Γ) := max_is_maximal_consistent h_consistent
  exists ⟨max Γ, h_max⟩
  exact max_extends

end Lindenbaum
open Lindenbaum

namespace CanonicalModel

def canonicalRelation (α : Program) (Γ Δ : MaximalConsistentSet) : Prop :=
  ∀ {φ}, (([α] φ) ∈ Γ.val) → φ ∈ Δ.val

def canonicalFrame : Frame where
  W := MaximalConsistentSet
  R := canonicalRelation
  nonempty := sorry

def canonicalValuation (lit : Literal) (Γ : MaximalConsistentSet) : Prop :=
  (Formula.atom lit) ∈ Γ.val

def canonicalModel : Model where
  F := canonicalFrame
  V := canonicalValuation

instance canonicalStandard : Standard canonicalModel := sorry

lemma box_of_derivation :
    ∀ {Γ : MaximalConsistentSet} {α : Program} {Δ : Set Formula} {φ : Formula},
    (Δ ⊢ φ) →
    (∀ ψ ∈ Δ, ([α] ψ) ∈ Γ.val) →
    Γ.val ⊢ ([α] φ) := by
  intros Γ α Δ φ h_deriv h_box
  induction h_deriv with
  | premise Ω ψ h_mem =>
      exact Deduction.premise Γ.val ([α] ψ) (h_box ψ h_mem)
  | axiom' Γ.val ψ h_ax =>
      exact weakening (Set.empty_subset _)
        (Deduction.necessitation ∅ α ψ (Deduction.axiom' ∅ ψ h_ax))
  | modusPonens Ω ψ χ h₁ h₂ ih₁ ih₂ =>
      have h_K : Γ.val ⊢ ([α] ψ → χ) → ([α] ψ) → ([α] χ) :=
        Deduction.axiom' Γ.val (([α] ψ → χ) → ([α] ψ) → ([α] χ)) (Axiom.modalK α ψ χ)
      exact Deduction.modusPonens Γ.val _ _ (ih₁ h_box)
        (Deduction.modusPonens Γ.val _ _ (ih₂ h_box) h_K)
  | necessitation Ω β ψ h_empty ih =>
      exact weakening (Set.empty_subset _)
        (Deduction.necessitation ∅ α ([β] ψ)
          (Deduction.necessitation ∅ β ψ h_empty))

lemma box_neg_diamond_inconsistent : ∀ {Γ : Set Formula} {α : Program} {φ : Formula},
    (Γ ⊢ ⟨α⟩ φ) →
    (Γ ⊢ [α] ¬ φ) →
    Γ ⊢ ⊥' := sorry

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
      apply Deduction.modusPonens Δ_α (φ → ⊥')
      . exact deduction_theorem h_delta_phi
      . exact Deduction.axiom' Δ_α ((φ → ⊥') → ¬ φ) (Axiom.negIntro φ)
    have h_box_neg : Γ.val ⊢ ([α] ¬ φ) :=
      box_of_derivation h_delta_neg (fun ψ h => h.2)
    have h_in_Γ : ([α] ¬ φ) ∈ Γ.val := mcs_is_closed h_box_neg
    have h_incons_Γ : Γ.val ⊢ ⊥' :=
      box_neg_diamond_inconsistent
        (Deduction.premise _ _ h_in)
        (Deduction.premise _ _ h_in_Γ)
    exact Γ.property.1 h_incons_Γ
  obtain ⟨Δ, h_ext⟩ := Lindenbaum.lindenbaum h_cons
  exact
    ⟨ Δ
    , λ h_box => h_ext (Set.mem_union_left _ h_box)
    , h_ext (Set.mem_union_right _ rfl)
    ⟩

lemma truth_lemma : ∀ {φ : Formula} {Γ : canonicalModel.F.W},
    ((canonicalModel, Γ) ⊨ φ) ↔ φ ∈ Γ.val := by
  intro φ
  induction φ using Formula.rec (motive_2 := λ _ => True) with
  | false =>
      intro Γ
      constructor
      . intros h_sat
        simp [satisfies] at h_sat
      . intros false_in
        simp [satisfies]
        have h_deriv_false : Γ.val ⊢ ⊥' := by
          apply Deduction.premise
          exact false_in
        have ⟨h_cons, _⟩ := Γ.property
        have h_incons : ¬ IsConsistent Γ.val := by
          simp [IsConsistent]
          exact h_deriv_false
        exact h_incons h_cons
  | atom p =>
      intro Γ
      constructor
      . intros h_sat
        simp [satisfies, canonicalModel, canonicalValuation] at h_sat
        exact h_sat
      . intros h_in
        simp only [satisfies, canonicalModel, canonicalValuation]
        exact h_in
  | neg φ ih =>
      intro Γ
      constructor
      . intros h_sat
        simp [satisfies] at h_sat
        exact mcs_complete (ih.not.mp h_sat)
      . intros h_neg_phi_in
        simp [satisfies]
        intro h_sat
        exact mcs_no_contradiction (ih.mp h_sat) h_neg_phi_in
  | conj φ ψ ih_φ ih_ψ =>
      intro Γ
      constructor
      . intros h_sat
        simp [satisfies] at h_sat
        have φ_in : φ ∈ Γ.val := ih_φ.mp h_sat.1
        have ψ_in : ψ ∈ Γ.val := ih_ψ.mp h_sat.2
        have h_ax : Γ.val ⊢ (φ → (ψ → (φ ∧ ψ))) := by
          apply Deduction.axiom'
          apply Axiom.conjIntro
        have h_step : Γ.val ⊢ (ψ → (φ ∧ ψ)) := by
          apply Deduction.modusPonens Γ.val φ
          · exact Deduction.premise Γ.val φ φ_in
          · exact h_ax
        have h_conj : Γ.val ⊢ (φ ∧ ψ) := by
          apply Deduction.modusPonens Γ.val ψ
          · exact Deduction.premise Γ.val ψ ψ_in
          · exact h_step
        exact mcs_is_closed h_conj
      . intros h_in
        simp [satisfies]
        have h_deriv_and : Γ.val ⊢ φ ∧ ψ := Deduction.premise Γ.val (φ ∧ ψ) h_in
        constructor
        . have h_deriv : Γ.val ⊢ φ := by
            have step : (Γ.val ⊢ (φ ∧ ψ) → φ) :=
              Deduction.axiom' Γ.val ((φ ∧ ψ) → φ) (Axiom.conjElimL φ ψ)
            exact Deduction.modusPonens Γ.val (φ ∧ ψ) (φ) h_deriv_and step
          have h_phi_in : φ ∈ Γ.val := mcs_is_closed h_deriv
          exact ih_φ.mpr h_phi_in
        . have h_deriv : Γ.val ⊢ ψ := by
            have step : (Γ.val ⊢ (φ ∧ ψ) → ψ) :=
              Deduction.axiom' Γ.val ((φ ∧ ψ) → ψ) (Axiom.conjElimR φ ψ)
            exact Deduction.modusPonens Γ.val (φ ∧ ψ) (ψ) h_deriv_and step
          have h_psi_in : ψ ∈ Γ.val := mcs_is_closed h_deriv
          exact ih_ψ.mpr h_psi_in
  | diamond α φ _ ih =>
      intro Γ
      constructor
      . intros h_sat
        simp [satisfies] at h_sat
        obtain ⟨Δ, h_rel, h_sat'⟩ := h_sat
        have h_phi_in : φ ∈ Δ.val := ih.mp h_sat'
        by_contra h_not_in
        have h_neg_dia : (¬ (⟨α⟩ φ)) ∈ Γ.val := mcs_complete h_not_in
        have h_deriv_box : Γ.val ⊢ ([α] ¬ φ) := by
          apply Deduction.modusPonens Γ.val (¬ (⟨α⟩ φ))
          · exact Deduction.premise Γ.val (¬ (⟨α⟩ φ)) h_neg_dia
          · apply weakening (show ∅ ⊆ Γ.val by simp)
            exact neg_diamond_to_box_neg α φ
        have h_box_in : ([α] ¬ φ) ∈ Γ.val := mcs_is_closed h_deriv_box
        have h_neg_phi_in : (¬ φ) ∈ Δ.val := h_rel h_box_in
        exact mcs_no_contradiction h_phi_in h_neg_phi_in
      . intros h_in
        simp [satisfies]
        obtain ⟨Δ, h_rel, h_phi_in⟩ := existence_lemma h_in
        exact ⟨Δ, h_rel, ih.mpr h_phi_in⟩
  | atomic p => trivial
  | comp α β ih_α ih_β => trivial
  | choice α β ih_α ih_β => trivial
  | iter α ih => trivial
  | parallel α β ih_α ih_β => trivial
  | test φ ih => trivial
  | s₁ => trivial
  | s₂ => trivial
  | r₁ => trivial
  | r₂ => trivial

def reachableWorlds (Γ : MaximalConsistentSet) : Set MaximalConsistentSet :=
  {Δ | ∃ Ω, canonicalRelation r₁ Ω Γ ∧ canonicalRelation r₂ Ω Δ}

lemma gamma_in_reachable : ∀ {Γ : MaximalConsistentSet},
    Γ ∈ reachableWorlds Γ := by
  simp only [reachableWorlds, Set.mem_setOf_eq]
  sorry

def generatedSubmodel (Γ : MaximalConsistentSet) : Model where
  F := {
    W := reachableWorlds Γ
    R := λ α ⟨Δ, _⟩  ⟨Δ', _⟩ => canonicalRelation α Δ Δ'
    nonempty := ⟨Γ, gamma_in_reachable⟩
  }
  V := λ lit ⟨Δ, _⟩ => canonicalValuation lit Δ

def gamma_is_world (Γ : MaximalConsistentSet) : (generatedSubmodel Γ).F.W :=
  ⟨Γ, gamma_in_reachable⟩

instance generatedSubmodelProperStandard (Γ : MaximalConsistentSet) :
    ProperStandard (generatedSubmodel Γ) := sorry

lemma submodel_truth_at_gamma : ∀ {Γ : MaximalConsistentSet} {φ : Formula},
    ((generatedSubmodel Γ, gamma_is_world Γ) ⊨ φ) ↔ φ ∈ Γ.val := sorry

end CanonicalModel
open CanonicalModel

lemma contrapositive_completeness : ∀ {φ : Formula},
    (¬ ⊢ φ) →
    ∃ (M : Model) (_ : ProperStandard M), ¬ (M ⊨ φ) := by
  intros φ h_not_prov
  have h₁ : IsConsistent {¬ φ} := by
    rewrite [deduction_consistency] at h_not_prov
    exact Decidable.not_not.mp h_not_prov
  obtain ⟨Γ, h₂⟩ := Lindenbaum.lindenbaum h₁
  have h₃ : (¬ φ) ∈ Γ.val := h₂ (Set.mem_singleton (¬ φ))
  have h₄ : φ ∉ Γ.val := by
    by_contra h_in
    have h_not_in : (¬ φ) ∉ Γ.val := mcs_no_contradiction h_in
    exact h_not_in h₃
  use generatedSubmodel Γ, generatedSubmodelProperStandard Γ
  intro h_global_sat
  have h_sat : (generatedSubmodel Γ, gamma_is_world Γ) ⊨ φ := h_global_sat
  rw [submodel_truth_at_gamma] at h_sat
  exact h₄ h_sat

theorem completeness : ∀ {φ : Formula},
    (⊨ φ) →
    (⊢ φ) := by
  intros φ h_valid
  by_contra h_not_prov
  obtain ⟨M, _, h_not_global_sat⟩ := contrapositive_completeness h_not_prov
  have h_global_sat : M ⊨ φ := h_valid rfl
  exact h_not_global_sat h_global_sat
