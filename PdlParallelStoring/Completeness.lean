import Mathlib.Data.Finset.Basic

import PdlParallelStoring.AxiomaticSystem
import PdlParallelStoring.Properties

-- Predicates for formulae and programs in the RSPDL₀ fragment.
-- In this fragment, we do not allow the use of the operators of:
--   - test (?)
--   - iteration (★)
--   - parallel composition (‖).

inductive RSPDL0Program : π → Prop where
  | atomic α : RSPDL0Program (π.atomic α)
  | comp α β : RSPDL0Program α → RSPDL0Program β → RSPDL0Program (α ; β)
  | choice α β : RSPDL0Program α → RSPDL0Program β → RSPDL0Program (α ∪ β)
  | s₁ : RSPDL0Program π.s₁
  | s₂ : RSPDL0Program π.s₂
  | r₁ : RSPDL0Program π.r₁
  | r₂ : RSPDL0Program π.r₂

inductive RSPDL0Formula : Φ → Prop where
  | false : RSPDL0Formula ⊥'
  | atomic φ : RSPDL0Formula (Φ.atomic φ)
  | neg φ : RSPDL0Formula φ → RSPDL0Formula (¬ φ)
  | conj φ₁ φ₂ : RSPDL0Formula φ₁ → RSPDL0Formula φ₂ → RSPDL0Formula (φ₁ ∧ φ₂)
  | diamond π φ : RSPDL0Program π → RSPDL0Formula φ → RSPDL0Formula (⟨π⟩ φ)

def listToConjunction : List Φ → Φ
  | [] => ⊤'
  | [φ] => φ
  | φ :: φs => φ ∧ listToConjunction φs

noncomputable def finsetToConjunction (φs : Finset Φ) : Φ :=
  listToConjunction φs.toList

def IsConsistent (s : Set Φ) : Prop :=
  (∀ φ ∈ s, RSPDL0Formula φ) ∧
  ¬ ∃ (φs : Finset Φ), (∀ φ ∈ φs, φ ∈ s) ∧ (⊢ (finsetToConjunction φs → ⊥'))

lemma consistent_empty : IsConsistent ∅ := by
  sorry

lemma deduction_consistency (φ : Φ) : RSPDL0Formula φ → ((⊢ φ) ↔ ¬ IsConsistent {¬ φ}) := by
  intro hRSPDL0
  constructor
  · intros hProv
    rewrite [IsConsistent]
    push_neg
    intros _
    use {¬ φ}
    constructor
    · simp
    · have hEq : finsetToConjunction {¬ φ} = ¬ φ := by
        rewrite [finsetToConjunction, Finset.toList_singleton]
        trivial
      rewrite [hEq]
      exact RSPDL₀.consistency φ hProv
  · contrapose
    intro hNotProv
    apply Classical.not_not.mpr
    by_contra hInconsistent
    rewrite [IsConsistent] at hInconsistent
    push_neg at hInconsistent
    obtain ⟨φ₂s, hSubset, hDerivesFalse⟩ := hInconsistent (by
      intros φ₂ hφ₂In
      simp only [Set.mem_singleton_iff] at hφ₂In
      rewrite [hφ₂In]
      exact RSPDL0Formula.neg φ hRSPDL0)
    by_cases hEmpty : φ₂s = ∅
    case pos =>
      rewrite [hEmpty] at hDerivesFalse
      have hEq : finsetToConjunction ∅ = _root_.true := by
        simp [finsetToConjunction, listToConjunction]
      rewrite [hEq] at hDerivesFalse
      have hTrue : ⊢ ⊤' := by
        apply RSPDL₀.tautology
        have hProp : IsPropositional ⊤' := by simp only [IsPropositional]
        use hProp
        simp [eval]
      have hFalse : ⊢ ⊥' := RSPDL₀.modusPonens ⊤' ⊥' hTrue hDerivesFalse
      have hProvPhi : ⊢ φ := RSPDL₀.explosion φ hFalse
      exact hNotProv hProvPhi
    case neg =>
      have hNonempty : φ₂s.Nonempty := Finset.nonempty_of_ne_empty hEmpty
      obtain ⟨φ₂, hφ₂In⟩ := hNonempty
      have hφ₂Eq : φ₂ = ¬ φ := by
        have hφ₂InSet : φ₂ ∈ {¬ φ} := hSubset φ₂ hφ₂In
        simp only [Set.mem_singleton_iff] at hφ₂InSet
        exact hφ₂InSet
      have hSingleton : φ₂s = {¬ φ} := by
        ext φ₃
        simp only [Finset.mem_singleton]
        constructor
        · intro hφ₃In
          have hφ₃InSet := hSubset φ₃ hφ₃In
          simp only [Set.mem_singleton_iff] at hφ₃InSet
          exact hφ₃InSet
        · intro hφ₃Eq
          rewrite [hφ₃Eq, ← hφ₂Eq]
          exact hφ₂In
      rewrite [hSingleton] at hDerivesFalse
      have hEq : finsetToConjunction {¬ φ} = ¬ φ := by
        rewrite [finsetToConjunction, Finset.toList_singleton]
        trivial
      rewrite [hEq] at hDerivesFalse
      have hProv : ⊢ φ := RSPDL₀.classicalNegation φ hDerivesFalse
      exact hNotProv hProv

lemma unprovable_consistent (φ : Φ) : RSPDL0Formula φ → (¬ ⊢ φ) → IsConsistent {¬ φ} := by
  intros hRPSDL0 hNotProv
  rewrite [deduction_consistency φ hRPSDL0] at hNotProv
  exact Classical.not_not.mp hNotProv

def IsMaximal (s : Set Φ) : Prop :=
  IsConsistent s ∧
  ∀ {φ : Φ}, RSPDL0Formula φ → (φ ∉ s) → ¬ IsConsistent (s ∪ {φ})

def MaximalConsistentSet : Type :=
  {s : Set Φ // IsMaximal s}

lemma mcs_complete (Γ : MaximalConsistentSet) (φ : Φ) :
  RSPDL0Formula φ → (φ ∈ Γ.val) ∨ (¬ φ) ∈ Γ.val := by
  sorry

lemma mcs_no_contradiction (Γ : MaximalConsistentSet) (φ : Φ) :
  RSPDL0Formula φ → (φ ∈ Γ.val) → (¬ φ) ∉ Γ.val := by
  sorry

lemma lindenbaum (s : Set Φ) : IsConsistent s → ∃ (Γ : MaximalConsistentSet), s ⊆ Γ.val := by
  sorry

def canonicalRelation (α : π) (Γ Δ : MaximalConsistentSet) : Prop :=
  ∀ φ, (([α] φ) ∈ Γ.val) → φ ∈ Δ.val

def canonicalFrame : Frame where
  W := MaximalConsistentSet
  R := canonicalRelation
  nonempty := sorry

def canonicalValuation (ψ : Ψ) (Γ : MaximalConsistentSet) : Prop :=
  Φ.atomic ψ ∈ Γ.val

def canonicalModel : Model where
  F := canonicalFrame
  V := canonicalValuation

lemma truth_lemma (φ : Φ) (Γ : canonicalModel.F.W) :
  RSPDL0Formula φ → (((canonicalModel, Γ) ⊨ φ) ↔ φ ∈ Γ.val) := by
  sorry

instance canonicalProper : Proper canonicalFrame := by
  sorry

instance canonicalStandard : Standard canonicalModel := by
  sorry

instance : ProperStandard canonicalModel where
  toStandard := canonicalStandard
  toProper := canonicalProper

lemma contrapositive_completeness :
    ∀ {φ : Φ}, RSPDL0Formula φ → (¬ ⊢ φ) →
    ∃ (M : Model) (_ : ProperStandard M), ¬ (M ⊨ φ) := by
  intro φ hRSPDL0 hNotProv
  have h₁ : IsConsistent {¬ φ} := unprovable_consistent φ hRSPDL0 hNotProv
  obtain ⟨Γ, h₂⟩ := lindenbaum {¬ φ} h₁
  have h₃ : (¬ φ) ∈ Γ.val := h₂ (Set.mem_singleton (¬ φ))
  have h₄ : φ ∉ Γ.val := by
    by_contra hIn
    have hNotIn:= mcs_no_contradiction Γ φ hRSPDL0 hIn
    exact hNotIn h₃
  have h₅ : ¬ ((canonicalModel, Γ) ⊨ φ) := by
    rewrite [truth_lemma φ Γ hRSPDL0]
    exact h₄
  use canonicalModel, inferInstance
  intro hGlobalSat
  have hSat : (canonicalModel, Γ) ⊨ φ := hGlobalSat
  exact h₅ hSat

theorem completeness : ∀ {φ : Φ}, (⊨ φ) → (⊢ φ) := by
  intro φ hValid
  by_contra hNotProv
  have hRSPDL0 : RSPDL0Formula φ := sorry
  obtain ⟨M, _, hNotGlobalSat⟩ := contrapositive_completeness hRSPDL0 hNotProv
  have hGlobalSat : M ⊨ φ := hValid rfl
  exact hNotGlobalSat hGlobalSat
