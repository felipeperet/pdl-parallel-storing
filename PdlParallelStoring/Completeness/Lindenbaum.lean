import Mathlib.Data.Finset.Max

import PdlParallelStoring.Completeness.Consistency

open Classical

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
  | @premise _ φ h_mem =>
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
  | axiom' h_ax =>
      use ∅
      constructor
      · exact Set.finite_empty
      constructor
      · simp only [Set.empty_subset]
      · apply Deduction.axiom'
        exact h_ax
  | modusPonens _ _ ih₁ ih₂ =>
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
  | necessitation h_empty _ =>
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
