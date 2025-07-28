import PdlParallelStoring.AxiomaticSystem
import PdlParallelStoring.Properties

open Classical

-- Def) For propositional formulas, boolean evaluation corresponds exactly to semantic satisfaction.
lemma eval_iff_satisfies (M : Model) (w : M.F.W) :
  ∀ (φ : Φ) (h : IsPropositional φ),
    (eval (λ ψ => decide (M.V ψ w)) φ h = Bool.true) ↔ ((M, w) ⊨ φ)
  | Φ.false, h => by simp [eval, satisfies]
  | Φ.atomic ψ, h => by simp [eval, satisfies]
  | Φ.neg φ, h => by
      rw [eval, satisfies]
      have ih := eval_iff_satisfies M w φ h
      constructor
      · intros hFalse hSat
        have hTrue := ih.mpr hSat
        rw [hTrue] at hFalse
        simp at hFalse
      · intro hNotSat
        have : eval (λ ψ => decide (M.V ψ w)) φ h ≠ true := by
          intro hTrue
          have hSat := ih.mp hTrue
          exact hNotSat hSat
        cases _ : eval (λ ψ => decide (M.V ψ w)) φ h with
        | false => rfl
        | true => contradiction
  | Φ.conj φ₁ φ₂, h => by
      simp [eval, satisfies]
      have ih₁ := eval_iff_satisfies M w φ₁ h.1
      have ih₂ := eval_iff_satisfies M w φ₂ h.2
      constructor
      · intro ⟨h₁True, h₂True⟩
        exact ⟨ih₁.mp h₁True, ih₂.mp h₂True⟩
      · intro ⟨h₁Sat, h₂Sat⟩
        exact ⟨ih₁.mpr h₁Sat, ih₂.mpr h₂Sat⟩
  | Φ.diamond π φ, h => by
      exfalso
      exact h

lemma soundness_tautology (φ : Φ) : IsTautology φ → ⊨ φ := by
  intros t
  obtain ⟨hProp, hEval⟩ := t
  intros F _ M _ hEq w
  let assign : String → Bool := fun ψ => decide (M.V ψ w)
  have hTrue : eval assign φ hProp = Bool.true := hEval assign
  have hLemma : (eval assign φ hProp = Bool.true) ↔ ((M, w) ⊨ φ) :=
    eval_iff_satisfies M w φ hProp
  rw [← hLemma]
  exact hTrue

lemma soundness_composition (α β : π) (φ : Φ) : ⊨ ([α;β] φ) ↔ ([α] [β] φ) := by
  intros _ _ M _ _ w
  constructor
  . intros hAnd
    obtain ⟨hAll, hEx⟩ := hAnd
    simp [satisfies] at *
    obtain ⟨s, hRws, t, hRst, hPhiNotHolds⟩ := hEx
    have hReach : M.F.R (α ; β) w t := by
      rw [Standard.comp]
      use s
    have hPhiHolds : (M, t) ⊨ φ := hAll t hReach
    exact hPhiNotHolds hPhiHolds
  . intros hSat
    obtain ⟨hAll, hEx⟩ := hSat
    simp [satisfies] at *
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hEx
    have hComp : Relation.Comp (M.F.R α) (M.F.R β) w s := by
      rw [← Standard.comp]
      exact hRws
    obtain ⟨t, hRwt, hRts⟩ := hComp
    have hPhiHolds : (M, s) ⊨ φ := hAll t hRwt s hRts
    exact hPhiNotHolds hPhiHolds

lemma soundness_choice (α β : π) (φ : Φ) : ⊨ ([α ∪ β] φ) ↔ ([α] φ) ∧ ([β] φ) := by
  intros _ _ M _ _ w
  constructor
  . intros hAnd
    obtain ⟨hSat₁, hSat₂⟩ := hAnd
    simp [satisfies] at *
    have hAlphaBox : ∀ (x : M.F.W), M.F.R α w x → (M, x) ⊨ φ := by
      intros t hRwt
      apply hSat₁
      rw [Standard.choice]
      left
      exact hRwt
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hSat₂ hAlphaBox
    have hPhiHolds : (M, s) ⊨ φ := by
      apply hSat₁
      rw [Standard.choice]
      right
      exact hRws
    exact hPhiNotHolds hPhiHolds
  . intros hAnd
    obtain ⟨hAll, hEx⟩ := hAnd
    simp [satisfies] at *
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hEx
    obtain ⟨hAll₁, hAll₂⟩ := hAll
    rw [Standard.choice] at hRws
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
  simp [satisfies] at *
  obtain ⟨hAlphaBox, hCounterExample⟩ := hSat₂
  obtain ⟨s, hRws, hPhi₂NotHolds⟩ := hCounterExample
  have hPhi₁Holds : (M, s) ⊨ φ₁ := hAlphaBox s hRws
  have hImp : ((M, s) ⊨ φ₁) → ((M, s) ⊨ φ₂) := hSat₁ s hRws
  have hPhi₂Holds : (M, s) ⊨ φ₂ := hImp hPhi₁Holds
  exact hPhi₂NotHolds hPhi₂Holds

lemma soundness_functional_r₁ (φ : Φ) : ⊨ (⟨π.r₁⟩ φ) → ([π.r₁] φ) := by
  intros _ P M _ hEq w hSat
  subst hEq
  simp [satisfies] at hSat
  obtain ⟨h₁, h₂⟩ := hSat
  obtain ⟨s, hRws, hSat⟩ := h₁
  rw [P.r₁] at hRws
  obtain ⟨s₁, s₂ , hEq₁, hEq₂⟩ := hRws
  obtain ⟨s', hRws', hNotSat⟩ := h₂
  rw [P.r₁] at hRws'
  obtain ⟨s₁', s₂', hEq₁', hEq₂'⟩ := hRws'
  have hSame : s₁ ⋆ s₂ = s₁'⋆ s₂' := by rw [← hEq₁, hEq₁']
  have ⟨hs₁Eq, hs₂Eq⟩ := State.inject.mp hSame
  have s'Eq : s' = s := by rw [hEq₂', ← hs₁Eq, ← hEq₂]
  rw [s'Eq] at hNotSat
  exact hNotSat hSat

lemma soundness_temporal_forward (φ : Φ) : ⊨ φ → ([π.s₁] ⟨π.r₁⟩ φ) := by
  intros _ P M _ hEq w hSat
  subst hEq
  simp [satisfies] at hSat
  obtain ⟨hSat₁, hSat₂⟩ := hSat
  obtain ⟨s, hAnd⟩ := hSat₂
  obtain ⟨hRws, hAll⟩ := hAnd
  have hR₁ : M.F.R π.r₁ s w :=  by
    rw [P.s₁] at hRws
    obtain ⟨w', t, hw_eq, hs_eq⟩ := hRws
    rw [P.r₁]
    use w', t
  have hNotSat : ¬ (M,w) ⊨ φ := hAll w hR₁
  exact hNotSat hSat₁

lemma soundness_same_domain : ⊨ (⟨π.r₁⟩ _root_.true) ↔ (⟨π.r₂⟩ _root_.true) := by
  intros _ P M _ hEq w
  subst hEq
  constructor
  . intros hSat₁
    obtain ⟨hSat₂, hAll⟩ := hSat₁
    simp [satisfies] at *
    obtain ⟨s, hRws⟩ := hSat₂
    simp [P.r₁] at hRws
    obtain ⟨s', hwEq⟩ := hRws
    have hR₂ : M.F.R π.r₂ w s' := by
      rw [P.r₂, hwEq]
      use s, s'
    exact hAll s' hR₂
  . intros hSat₁
    obtain ⟨hSat₂, hAll⟩ := hSat₁
    simp [satisfies] at *
    obtain ⟨t, hRwt⟩ := hSat₂
    simp [P.r₂] at hRwt
    obtain ⟨s', ht_eq⟩ := hRwt
    have hR₁ : M.F.R π.r₁ w s' := by
      rw [P.r₁, ht_eq]
      use s', t
    exact hAll s' hR₁

lemma soundness_unicity (φ : Φ) : ⊨ (⟨π.s₁ ; π.r₁⟩ φ) ↔ ([π.s₁ ; π.r₁] φ) := by
  intros _ _ M _ _ w
  constructor
  . intros hAnd
    obtain ⟨hSat₁, hSat₂⟩ := hAnd
    simp [satisfies] at *
    obtain ⟨s, hRws, hSat₁⟩ := hSat₁
    obtain ⟨x, hRwx, hNotSat⟩ := hSat₂
    have hsEqw : s = w := by
      rw [Standard.comp] at hRws
      rw [s₁_comp_r₁] at hRws
      exact hRws.symm
    have hxEqw : x = w := by
      rw [Standard.comp] at hRwx
      rw [s₁_comp_r₁] at hRwx
      exact hRwx.symm
    rw [hsEqw] at hSat₁
    rw [hxEqw] at hNotSat
    exact hNotSat hSat₁
  . intros hSat
    simp [satisfies] at *
    obtain ⟨hPos, hNeg⟩ := hSat
    have hReach : M.F.R (π.s₁ ; π.r₁) w w := by
      rw [Standard.comp, s₁_comp_r₁]
    have hPhiHolds : (M, w) ⊨ φ := hPos w hReach
    have hPhiNotHolds : ¬ (M, w) ⊨ φ := hNeg w hReach
    exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_id (φ : Φ) : ⊨ ([π.s₁ ; π.r₂] φ) → φ := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hSat, hPhiNotHolds⟩ := hAnd
  simp [satisfies] at hSat
  have hReach : M.F.R (π.s₁ ; π.r₂) w w := by
    rw [Standard.comp, s₁_comp_r₂]
    simp [State.equiv.refl]
  have hPhiHolds : (M, w) ⊨ φ := hSat w hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_diamond (φ : Φ) : ⊨ φ → ([π.s₁ ; π.r₂] ⟨π.s₁ ; π.r₂⟩ φ) := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hPhiHolds, hSat₂⟩ := hAnd
  simp [satisfies] at *
  obtain ⟨s, hRws, hAll⟩ := hSat₂
  have hReach : M.F.R (π.s₁ ; π.r₂) s w := by
    rw [Standard.comp, s₁_comp_r₂] at *
    exact State.equiv.symm hRws
  have hPhiNotHolds : ¬ (M, w) ⊨ φ := hAll w hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_iterate (φ : Φ) :
    ⊨ ([π.s₁ ; π.r₂] φ) → ([π.s₁ ; π.r₂] [π.s₁ ; π.r₂] φ) := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hAll, hSat⟩ := hAnd
  simp [satisfies] at *
  obtain ⟨s, hRws, t, hRst, hPhiNotHolds⟩ := hSat
  have hReach : M.F.R (π.s₁ ; π.r₂) w t := by
    rw [Standard.comp, s₁_comp_r₂] at *
    simp [State.equiv.trans hRws hRst]
  have hPhiHolds : (M, t) ⊨ φ := hAll t hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_modus_ponens (φ₁ φ₂ : Φ) (ih₁ : ⊨ φ₁) (ih₂ : ⊨ φ₁ → φ₂) : ⊨ φ₂ := by
  intros _ _ M _ hEq w
  have hSat : (M, w) ⊨ φ₁ := ih₁ hEq
  have hSatInf : (M, w) ⊨ (φ₁ → φ₂) := ih₂ hEq
  apply by_contra
  intro h
  have : (¬¬(M,w) ⊨ φ₁) ∧ ¬(M,w) ⊨ φ₂ := by
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

lemma soundness_consistency (φ : Φ) (ih : ⊨ φ) : ⊨ ((¬ φ) → ⊥') := by
  intros _ _ M _ hEq w h
  obtain ⟨h₁, _⟩ := h
  have hPhiNotHolds : ¬ (M, w) ⊨ φ := by
    simp [satisfies] at *
    exact h₁
  have hPhiHolds : (M, w) ⊨ φ := ih hEq
  exact hPhiNotHolds hPhiHolds

lemma soundness_explosion (φ : Φ) (ih : ⊨ ⊥') : ⊨ φ := by
  intros _ _ M _ hEq w
  have hContra : (M, w) ⊨ ⊥' := ih hEq
  simp [satisfies] at hContra

lemma soundness_classical_negation (φ : Φ) (ih : ⊨ ((¬ φ) → Φ.false)) : ⊨ φ := by
  intros _ _ M _ hEq w
  have hNotPhiFalse : (M, w) ⊨ ((¬ φ) → ⊥') := ih hEq
  simp [satisfies] at hNotPhiFalse
  exact hNotPhiFalse

-- Theorem) If φ is derivable in RSPDL₀, then φ is valid in all proper frames.
theorem soundness : ∀ {φ : Φ}, (⊢ φ) → (⊨ φ) := by
  intros _ h
  induction h with
  | tautology φ t => exact soundness_tautology φ t
  | composition α β φ => exact soundness_composition α β φ
  | choice α β φ => exact soundness_choice α β φ
  | K α φ₁ φ₂ => exact soundness_k α φ₁ φ₂
  | functionalR₁ φ => exact soundness_functional_r₁ φ
  | temporalForward φ => exact soundness_temporal_forward φ
  | sameDomain => exact soundness_same_domain
  | unicity φ => exact soundness_unicity φ
  | storeRestoreId φ => exact soundness_store_restore_id φ
  | storeRestoreDiamond φ => exact soundness_store_restore_diamond φ
  | storeRestoreIterate φ => exact soundness_store_restore_iterate φ
  | modusPonens φ₁ φ₂ _ _ ih₁ ih₂  => exact soundness_modus_ponens φ₁ φ₂ ih₁ ih₂
  | necessitation α φ _ ih => exact soundness_necessitation α φ ih
  | consistency φ hProv ih => exact soundness_consistency φ ih
  | explosion φ _ ih => exact soundness_explosion φ ih
  | classicalNegation φ _ ih => exact soundness_classical_negation φ ih
  | _ => sorry
