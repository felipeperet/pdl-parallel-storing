import PdlParallelStoring.AxiomaticSystem
import PdlParallelStoring.Properties

open Classical

lemma soundness_composition (α β : π) (φ : Φ) : ⊨ ([α ; β] φ) ↔ ([α] [β] φ) := by
  intros _ _ M _ _ w
  constructor
  . intro hAnd
    obtain ⟨hAll, hEx⟩ := hAnd
    simp only [satisfies, Decidable.not_not] at hAll hEx
    simp only [not_exists, not_and, Decidable.not_not] at hAll
    obtain ⟨s, hRws, t, hRst, hPhiNotHolds⟩ := hEx
    have hReach : M.F.R (α ; β) w t := by
      rewrite [Standard.comp]
      use s
    have hPhiHolds : (M, t) ⊨ φ := hAll t hReach
    exact hPhiNotHolds hPhiHolds
  . intro hSat
    obtain ⟨hAll, hEx⟩ := hSat
    simp only [satisfies, Decidable.not_not] at hAll hEx
    simp only [not_exists, not_and, Decidable.not_not] at hAll
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hEx
    have hComp : Relation.Comp (M.F.R α) (M.F.R β) w s := by
      rewrite [← Standard.comp]
      exact hRws
    obtain ⟨t, hRwt, hRts⟩ := hComp
    have hPhiHolds : (M, s) ⊨ φ := hAll t hRwt s hRts
    exact hPhiNotHolds hPhiHolds

lemma soundness_choice (α β : π) (φ : Φ) : ⊨ ([α ∪ β] φ) ↔ ([α] φ) ∧ ([β] φ) := by
  intros _ _ M _ _ w
  constructor
  . intro hAnd
    obtain ⟨hSat₁, hSat₂⟩ := hAnd
    simp only [satisfies, not_exists, not_and, Decidable.not_not] at hSat₁ hSat₂
    simp only [not_forall] at hSat₂
    have hAlphaBox : ∀ (x : M.F.W), M.F.R α w x → (M, x) ⊨ φ := by
      intros t hRwt
      apply hSat₁
      rewrite [Standard.choice]
      left
      exact hRwt
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hSat₂ hAlphaBox
    have hPhiHolds : (M, s) ⊨ φ := by
      apply hSat₁
      rewrite [Standard.choice]
      right
      exact hRws
    exact hPhiNotHolds hPhiHolds
  . intro hAnd
    obtain ⟨hAll, hEx⟩ := hAnd
    simp only [satisfies, Decidable.not_not] at hAll hEx
    simp only [not_exists, not_and, Decidable.not_not] at hAll
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hEx
    obtain ⟨hAll₁, hAll₂⟩ := hAll
    rewrite [Standard.choice] at hRws
    cases hRws with
    | inl hAlpha =>
        have hPhiHolds : (M, s) ⊨ φ := hAll₁ s hAlpha
        exact hPhiNotHolds hPhiHolds
    | inr hBeta =>
        have hPhiHolds : (M, s) ⊨ φ := hAll₂ s hBeta
        exact hPhiNotHolds hPhiHolds

lemma soundness_k (α : π) (φ₁ φ₂ : Φ) : ⊨ ([α] φ₁ → φ₂) → ([α] φ₁) → ([α] φ₂) := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hSat₁, hSat₂⟩ := hAnd
  simp only [satisfies, Decidable.not_not, not_exists, not_and] at hSat₁ hSat₂
  simp only [not_forall] at hSat₂
  obtain ⟨hAlphaBox, hCounterExample⟩ := hSat₂
  obtain ⟨s, hRws, hPhi₂NotHolds⟩ := hCounterExample
  have hPhi₁Holds : (M, s) ⊨ φ₁ := hAlphaBox s hRws
  have hImp : ((M, s) ⊨ φ₁) → ((M, s) ⊨ φ₂) := hSat₁ s hRws
  have hPhi₂Holds : (M, s) ⊨ φ₂ := hImp hPhi₁Holds
  exact hPhi₂NotHolds hPhi₂Holds

lemma soundness_functional_r₁ (φ : Φ) : ⊨ (⟨π.r₁⟩ φ) → ([π.r₁] φ) := by
  intros _ P M _ hEq w hSat
  subst hEq
  simp only [satisfies, Decidable.not_not] at hSat
  obtain ⟨h₁, h₂⟩ := hSat
  obtain ⟨s, hRws, hSat⟩ := h₁
  rewrite [P.r₁] at hRws
  obtain ⟨s₁, s₂, hEq₁, hEq₂⟩ := hRws
  obtain ⟨s', hRws', hNotSat⟩ := h₂
  rewrite [P.r₁] at hRws'
  obtain ⟨s₁', s₂', hEq₁', hEq₂'⟩ := hRws'
  have hSame : s₁ ⋆ s₂ = s₁'⋆ s₂' := by rw [← hEq₁, hEq₁']
  have ⟨hs₁Eq, hs₂Eq⟩ := State.inject.mp hSame
  have s'Eq : s' = s := by rw [hEq₂', ← hs₁Eq, ← hEq₂]
  rewrite [s'Eq] at hNotSat
  exact hNotSat hSat

lemma soundness_temporal_forward (φ : Φ) : ⊨ φ → ([π.s₁] ⟨π.r₁⟩ φ) := by
  intros _ P M _ hEq w hSat
  subst hEq
  simp only [satisfies, Decidable.not_not, not_exists, not_forall, not_and] at hSat
  obtain ⟨hSat₁, hSat₂⟩ := hSat
  obtain ⟨s, hAnd⟩ := hSat₂
  obtain ⟨hRws, hAll⟩ := hAnd
  have hR₁ : M.F.R π.r₁ s w :=  by
    rewrite [P.s₁] at hRws
    obtain ⟨w', t, hw_eq, hs_eq⟩ := hRws
    rewrite [P.r₁]
    use w', t
  have hNotSat : ¬ (M, w) ⊨ φ := hAll w hR₁
  exact hNotSat hSat₁

lemma soundness_same_domain : ⊨ (⟨π.r₁⟩ ⊤') ↔ (⟨π.r₂⟩ ⊤') := by
  intros _ P M _ hEq w
  subst hEq
  constructor
  . intros hSat₁
    obtain ⟨hSat₂, hAll⟩ := hSat₁
    simp [satisfies] at hAll hSat₂
    obtain ⟨s, hRws⟩ := hSat₂
    simp [P.r₁] at hRws
    obtain ⟨s', hwEq⟩ := hRws
    have hR₂ : M.F.R π.r₂ w s' := by
      rewrite [P.r₂, hwEq]
      use s, s'
    exact hAll s' hR₂
  . intros hSat₁
    obtain ⟨hSat₂, hAll⟩ := hSat₁
    simp only [satisfies, not_false_eq_true, and_true] at hAll hSat₂
    simp only [Decidable.not_not] at hSat₂
    simp only [not_exists] at hAll
    obtain ⟨t, hRwt⟩ := hSat₂
    simp [P.r₂] at hRwt
    obtain ⟨s', ht_eq⟩ := hRwt
    have hR₁ : M.F.R π.r₁ w s' := by
      rewrite [P.r₁, ht_eq]
      use s', t
    exact hAll s' hR₁

lemma soundness_unicity (φ : Φ) : ⊨ (⟨π.s₁ ; π.r₁⟩ φ) ↔ ([π.s₁ ; π.r₁] φ) := by
  intros _ _ M _ _ w
  constructor
  . intros hAnd
    obtain ⟨hSat₁, hSat₂⟩ := hAnd
    simp only [satisfies, Decidable.not_not] at hSat₁ hSat₂
    obtain ⟨s, hRws, hSat₁⟩ := hSat₁
    obtain ⟨x, hRwx, hNotSat⟩ := hSat₂
    have hsEqw : s = w := by
      rewrite [Standard.comp] at hRws
      rewrite [s₁_comp_r₁] at hRws
      exact hRws.symm
    have hxEqw : x = w := by
      rewrite [Standard.comp] at hRwx
      rewrite [s₁_comp_r₁] at hRwx
      exact hRwx.symm
    rewrite [hsEqw] at hSat₁
    rewrite [hxEqw] at hNotSat
    exact hNotSat hSat₁
  . intros hSat
    simp only [satisfies, Decidable.not_not, not_exists, not_and] at hSat
    obtain ⟨hPos, hNeg⟩ := hSat
    have hReach : M.F.R (π.s₁ ; π.r₁) w w := by
      rw [Standard.comp, s₁_comp_r₁]
    have hPhiHolds : (M, w) ⊨ φ := hPos w hReach
    have hPhiNotHolds : ¬ (M, w) ⊨ φ := hNeg w hReach
    exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_id (φ : Φ) : ⊨ ([π.s₁ ; π.r₂] φ) → φ := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hSat, hPhiNotHolds⟩ := hAnd
  simp only
    [satisfies, not_exists, not_and, Decidable.not_not, not_forall, Classical.not_imp] at hSat
  have hReach : M.F.R (π.s₁ ; π.r₂) w w := by
    rewrite [Standard.comp, s₁_comp_r₂]
    simp only [State.equiv.refl]
  have hPhiHolds : (M, w) ⊨ φ := hSat w hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_diamond (φ : Φ) : ⊨ φ → ([π.s₁ ; π.r₂] ⟨π.s₁ ; π.r₂⟩ φ) := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hPhiHolds, hSat₂⟩ := hAnd
  simp only [satisfies, Decidable.not_not] at hPhiHolds hSat₂
  simp only [not_exists, not_and] at hSat₂
  obtain ⟨s, hRws, hAll⟩ := hSat₂
  have hReach : M.F.R (π.s₁ ; π.r₂) s w := by
    rewrite [Standard.comp, s₁_comp_r₂] at *
    exact State.equiv.symm hRws
  have hPhiNotHolds : ¬ (M, w) ⊨ φ := hAll w hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_iterate (φ : Φ) :
    ⊨ ([π.s₁ ; π.r₂] φ) → ([π.s₁ ; π.r₂] [π.s₁ ; π.r₂] φ) := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hAll, hSat⟩ := hAnd
  simp only [satisfies, Decidable.not_not] at hAll hSat
  simp only [not_exists, not_and, Decidable.not_not] at hAll
  obtain ⟨s, hRws, t, hRst, hPhiNotHolds⟩ := hSat
  have hReach : M.F.R (π.s₁ ; π.r₂) w t := by
    rewrite [Standard.comp, s₁_comp_r₂] at *
    simp only [State.equiv.trans hRws hRst]
  have hPhiHolds : (M, t) ⊨ φ := hAll t hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_modus_ponens (φ₁ φ₂ : Φ) (ih₁ : ⊨ φ₁) (ih₂ : ⊨ φ₁ → φ₂) : ⊨ φ₂ := by
  intros _ _ M _ hEq w
  have hSat : (M, w) ⊨ φ₁ := ih₁ hEq
  have hSatInf : (M, w) ⊨ (φ₁ → φ₂) := ih₂ hEq
  by_contra h
  have : (¬¬ (M, w) ⊨ φ₁) ∧ ¬ (M, w) ⊨ φ₂ := by
    constructor
    · intro h_neg
      exact h_neg hSat
    · exact h
  exact hSatInf this

lemma soundness_necessitation (α : π) (φ : Φ) (ih : ⊨ φ) : ⊨ [α] φ := by
  intros _ _ M _ hEq w hSat
  obtain ⟨s, _, hPhiNotHolds⟩ := hSat
  have hPhiHolds : (M, s) ⊨ φ := ih hEq
  exact hPhiNotHolds hPhiHolds

theorem soundness_general : ∀ {Γ : Set Φ} {φ : Φ}, (Γ ⊢ φ) → (∀ ψ ∈ Γ, ⊨ ψ) → ⊨ φ := by
  intros _ _ h
  induction h with
  | premise _ _ hMem =>
      intros hIn
      apply hIn
      exact hMem
  | axiom' _ _ ax =>
      intros
      cases ax with
      | composition => apply soundness_composition
      | choice => apply soundness_choice
      | K => apply soundness_k
      | functionalR₁ => apply soundness_functional_r₁
      | temporalForward => apply soundness_temporal_forward
      | sameDomain => apply soundness_same_domain
      | unicity => apply soundness_unicity
      | storeRestoreId => apply soundness_store_restore_id
      | storeRestoreDiamond => apply soundness_store_restore_diamond
      | storeRestoreIterate => apply soundness_store_restore_iterate
      | _ => sorry
  | modusPonens _ _ _ _ _ ih₁ ih₂ =>
      intros hIn
      apply soundness_modus_ponens
      . exact ih₁ hIn
      . exact ih₂ hIn
  | necessitation _ _ _ _ ih =>
      intros
      apply soundness_necessitation
      apply ih
      simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]

theorem soundness : ∀ {φ : Φ}, (⊢ φ) → (⊨ φ) := by
  intros _ h
  apply soundness_general h
  simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]
