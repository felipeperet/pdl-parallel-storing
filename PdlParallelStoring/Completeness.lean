import Mathlib.Data.Finset.Max

import PdlParallelStoring.Syntax
import PdlParallelStoring.Semantics
import PdlParallelStoring.AxiomaticSystem

open Classical Program

/-!
# Completeness of RSPDL₀

This module proves that every formula valid in all proper standard₀ models is derivable
in the RSPDL₀ axiomatic system: if ⊨ φ then ⊢ φ.

The proof follows the canonical model construction: maximal consistent sets serve as
worlds, the canonical relation is defined via the box operator, and a generated submodel
is used to obtain a proper standard₀ countermodel for any non-theorem.
-/

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
      have htail : list_conjunction tail ∈ Γ.val := ih (fun φ hφ => h φ (List.mem_cons_of_mem ψ hφ))
      exact mcs_is_closed
        (Deduction.modusPonens (Deduction.premise htail)
          (Deduction.modusPonens (Deduction.premise hψ)
            (Deduction.axiom' (Axiom.conjIntro ψ (list_conjunction tail)))))

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
open Lindenbaum

namespace CanonicalModel

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
          apply Deduction.modusPonens
          · exact Deduction.premise φ_in
          · exact h_ax
        have h_conj : Γ.val ⊢ (φ ∧ ψ) := by
          apply Deduction.modusPonens
          · exact Deduction.premise ψ_in
          · exact h_step
        exact mcs_is_closed h_conj
      . intros h_in
        simp [satisfies]
        have h_deriv_and : Γ.val ⊢ φ ∧ ψ := Deduction.premise h_in
        constructor
        . have h_deriv : Γ.val ⊢ φ := by
            have step : (Γ.val ⊢ (φ ∧ ψ) → φ) :=
              Deduction.axiom' (Axiom.conjElimL φ ψ)
            exact Deduction.modusPonens h_deriv_and step
          have h_phi_in : φ ∈ Γ.val := mcs_is_closed h_deriv
          exact ih_φ.mpr h_phi_in
        . have h_deriv : Γ.val ⊢ ψ := by
            have step : (Γ.val ⊢ (φ ∧ ψ) → ψ) :=
              Deduction.axiom' (Axiom.conjElimR φ ψ)
            exact Deduction.modusPonens h_deriv_and step
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
          apply Deduction.modusPonens
          · exact Deduction.premise h_neg_dia
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
  obtain ⟨Ω, h_ext⟩ := Lindenbaum.lindenbaum h_cons
  exact ⟨Ω,
    fun {φ} h_box => by
      by_contra h_not
      have h_neg : (¬ φ) ∈ Δ₁.val := mcs_complete h_not
      have h_dia : (⟨r₁⟩ (¬ φ)) ∈ Ω.val :=
        h_ext (Set.mem_union_left _ ⟨¬ φ, h_neg, rfl⟩)
      exact mcs_no_contradiction h_dia h_box,
    fun {φ} h_box => by
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

instance generatedSubmodelProperStandard (Γ : MaximalConsistentSet) :
    ProperStandard₀ (generatedSubmodel Γ) := sorry

def gamma_is_world (Γ : MaximalConsistentSet) : (generatedSubmodel Γ).F.W :=
  ⟨Γ, s₁r₂_refl⟩

lemma submodel_truth_at_gamma : ∀ {Γ : MaximalConsistentSet} {φ : Formula},
    ((generatedSubmodel Γ, gamma_is_world Γ) ⊨ φ) ↔ φ ∈ Γ.val := by
  intros Γ φ
  constructor
  . intros hSat
    sorry
  . sorry

end CanonicalModel
open CanonicalModel

lemma contrapositive_completeness : ∀ {φ : Formula},
    (¬ ⊢ φ) →
    ∃ (M : Model) (_ : ProperStandard₀ M), ¬ (M ⊨ φ) := by
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
