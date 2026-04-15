import PdlParallelStoring.Semantics
import PdlParallelStoring.AxiomaticSystem

open Classical Program

/-!
# Soundness of RSPDL₀

This module proves that every formula derivable in the RSPDL₀ axiomatic system is valid
in every proper standard₀ model: if ⊢ φ then ⊨ φ.

RSPDL₀ is a fragment of PRSPDL without iteration (*), test (?), and parallel
composition (‖). The axiomatic system includes propositional logic, classical logic,
standard modal axioms for composition and choice, and axioms specific to the
store/retrieve programs (s₁, s₂, r₁, r₂).
-/

lemma soundness_axiom_I (φ : Formula) :
    ⊨ φ → φ := by
  intros _ _ M _ _ w
  simp only [satisfies, Decidable.not_not, and_not_self, not_false_eq_true]

lemma soundness_axiom_K (φ ψ : Formula) :
    ⊨ φ → ψ → φ := by
  intros _ _ M _ _ w
  simp only [satisfies, Decidable.not_not, not_and, Classical.not_imp]
  intros h_sat_phi _
  exact h_sat_phi

lemma soundness_axiom_S (φ ψ χ : Formula) :
    ⊨ (φ → ψ → χ) → (φ → ψ) → φ → χ := by
  intros _ _ M _ _ w
  simp only [satisfies, Decidable.not_not, not_and, Classical.not_imp]
  intros h₁ h₂ h₃
  have h_step₁ := h₁ h₃
  have h_step₂ := h₂ h₃
  exact h_step₁ h_step₂

lemma soundness_conj_intro (φ ψ : Formula) :
    ⊨ φ → ψ → φ ∧ ψ := by
  intros _ _ M _ _ w
  simp only [satisfies, Decidable.not_not, not_and, Classical.not_imp]
  intros h_sat_phi h_sat_psi
  constructor
  . exact h_sat_phi
  . exact h_sat_psi

lemma soundness_conj_elimL (φ ψ : Formula) :
    ⊨ (φ ∧ ψ) → φ := by
  intros _ _ M _ _ w
  simp only [satisfies, not_and, Classical.not_imp, Decidable.not_not, and_imp]
  intros h_sat_phi _
  exact h_sat_phi

lemma soundness_conj_elimR (φ ψ : Formula) :
    ⊨ (φ ∧ ψ) → ψ := by
  intros _ _ M _ _ w
  simp only [satisfies, not_and, Classical.not_imp, Decidable.not_not, and_imp]
  intros _ h_sat_psi
  exact h_sat_psi

lemma soundness_contradiction (φ : Formula) :
    ⊨ (φ ∧ ¬ φ) → ⊥' := by
  intros _ _ M _ _ w
  simp only [satisfies, and_not_self, not_false_eq_true, not_true_eq_false, and_true]

lemma soundness_neg_intro (φ : Formula) :
    ⊨ (φ → ⊥') → ¬ φ := by
  intros _ _ M _ _ w
  simp only [satisfies, Decidable.not_not, not_false_eq_true, and_true, not_and_self]

lemma soundness_neg_elim (φ : Formula) :
    ⊨ (¬ φ) → φ → ⊥' := by
  intros _ _ M _ _ w
  simp only [satisfies, Decidable.not_not, not_false_eq_true, and_true, not_and_self]

lemma soundness_classical_reductio (φ : Formula) :
    ⊨ ((¬ φ) → ⊥') → φ := by
  intros _ _ M _ _ w
  simp only [satisfies, Decidable.not_not, not_false_eq_true, and_true, and_not_self]

lemma soundness_duality (φ : Formula) :
    ⊨ (⟨α⟩ φ) ↔ ¬ ([α] ¬ φ)  := by
  intros _ _ M _ _ w
  simp only
    [ satisfies, not_exists, not_and, not_forall, Classical.not_imp, Decidable.not_not, imp_self
    , and_self ]

lemma soundness_modal_K (α : Program) (φ₁ φ₂ : Formula) :
    ⊨ ([α] φ₁ → φ₂) → ([α] φ₁) → ([α] φ₂) := by
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

lemma soundness_composition (α β : Program) (φ : Formula) :
    ⊨ ([α ; β] φ) ↔ ([α] [β] φ) := by
  intros _ _ M _ _ w
  constructor
  . intro hAnd
    obtain ⟨hAll, hEx⟩ := hAnd
    simp only [satisfies, Decidable.not_not] at hAll hEx
    simp only [not_exists, not_and, Decidable.not_not] at hAll
    obtain ⟨s, hRws, t, hRst, hPhiNotHolds⟩ := hEx
    have hReach : M.F.R (α ; β) w t := by
      rewrite [Standard₀.comp]
      use s
    have hPhiHolds : (M, t) ⊨ φ := hAll t hReach
    exact hPhiNotHolds hPhiHolds
  . intro hSat
    obtain ⟨hAll, hEx⟩ := hSat
    simp only [satisfies, Decidable.not_not] at hAll hEx
    simp only [not_exists, not_and, Decidable.not_not] at hAll
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hEx
    have hComp : Relation.Comp (M.F.R α) (M.F.R β) w s := by
      rewrite [← Standard₀.comp]
      exact hRws
    obtain ⟨t, hRwt, hRts⟩ := hComp
    have hPhiHolds : (M, s) ⊨ φ := hAll t hRwt s hRts
    exact hPhiNotHolds hPhiHolds

lemma soundness_choice (α β : Program) (φ : Formula) :
    ⊨ ([α ∪ β] φ) ↔ ([α] φ) ∧ ([β] φ) := by
  intros _ _ M _ _ w
  constructor
  . intro hAnd
    obtain ⟨hSat₁, hSat₂⟩ := hAnd
    simp only [satisfies, not_exists, not_and, Decidable.not_not] at hSat₁ hSat₂
    simp only [not_forall] at hSat₂
    have hAlphaBox : ∀ (x : M.F.W), M.F.R α w x → (M, x) ⊨ φ := by
      intros t hRwt
      apply hSat₁
      rewrite [Standard₀.choice]
      left
      exact hRwt
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hSat₂ hAlphaBox
    have hPhiHolds : (M, s) ⊨ φ := by
      apply hSat₁
      rewrite [Standard₀.choice]
      right
      exact hRws
    exact hPhiNotHolds hPhiHolds
  . intro hAnd
    obtain ⟨hAll, hEx⟩ := hAnd
    simp only [satisfies, Decidable.not_not] at hAll hEx
    simp only [not_exists, not_and, Decidable.not_not] at hAll
    obtain ⟨s, hRws, hPhiNotHolds⟩ := hEx
    obtain ⟨hAll₁, hAll₂⟩ := hAll
    rewrite [Standard₀.choice] at hRws
    cases hRws with
    | inl hAlpha =>
        have hPhiHolds : (M, s) ⊨ φ := hAll₁ s hAlpha
        exact hPhiNotHolds hPhiHolds
    | inr hBeta =>
        have hPhiHolds : (M, s) ⊨ φ := hAll₂ s hBeta
        exact hPhiNotHolds hPhiHolds

lemma soundness_functional_r₁ (φ : Formula) :
    ⊨ (⟨r₁⟩ φ) → ([r₁] φ) := by
  intros _ P M _ hEq w hSat
  subst hEq
  simp only [satisfies, Decidable.not_not] at hSat
  obtain ⟨h₁, h₂⟩ := hSat
  obtain ⟨s, hRws, hSat⟩ := h₁
  rewrite [P.r₁] at hRws
  obtain ⟨s₁, s₂, hMem₁, hEq₁⟩ := hRws
  obtain ⟨s', hRws', hNotSat⟩ := h₂
  rewrite [P.r₁] at hRws'
  obtain ⟨s₁', s₂', hMem₂, hEq₂⟩ := hRws'
  have ⟨hs₁Eq, _⟩ := State.separated hMem₁ hMem₂
  have s'Eq : s' = s := by rw [hEq₂, ← hs₁Eq, ← hEq₁]
  rewrite [s'Eq] at hNotSat
  exact hNotSat hSat

lemma soundness_functional_r₂ (φ : Formula) :
    ⊨ (⟨r₂⟩ φ) → ([r₂] φ) := by
  intros _ P M _ hEq w hSat
  subst hEq
  simp only [satisfies, Decidable.not_not] at hSat
  obtain ⟨h₁, h₂⟩ := hSat
  obtain ⟨s, hRws, hSat⟩ := h₁
  rewrite [P.r₂] at hRws
  obtain ⟨s₁, s₂, hMem₁, hEq₁⟩ := hRws
  obtain ⟨s', hRws', hNotSat⟩ := h₂
  rewrite [P.r₂] at hRws'
  obtain ⟨s₁', s₂', hMem₂, hEq₂⟩ := hRws'
  have ⟨_, hs₂Eq⟩ := State.separated hMem₁ hMem₂
  have s'Eq : s' = s := by rw [hEq₂, ← hs₂Eq, ← hEq₁]
  rewrite [s'Eq] at hNotSat
  exact hNotSat hSat

lemma soundness_temporal_forward (φ : Formula) :
    ⊨ φ → ([s₁] ⟨r₁⟩ φ) := by
  intros _ P M _ hEq w hSat
  subst hEq
  simp only [satisfies, Decidable.not_not, not_exists, not_forall, not_and] at hSat
  obtain ⟨hSat, hEx⟩ := hSat
  obtain ⟨s, hRws, hAll⟩ := hEx
  have hR : M.F.R r₁ s w := by
    rewrite [P.s₁] at hRws
    obtain ⟨w', t, hw_eq, hs_mem⟩ := hRws
    rewrite [P.r₁]
    exact ⟨w', t, hw_eq ▸ hs_mem, hw_eq⟩
  exact hAll w hR hSat

lemma soundness_temporal_backward (φ : Formula) :
    ⊨ φ → ([r₁] ⟨s₁⟩ φ) := by
  intros F P M PS hEq w hSat
  subst hEq
  simp only
    [satisfies, Decidable.not_not, not_exists, not_and, not_forall, Classical.not_imp ] at hSat
  obtain ⟨hSat, hEx⟩ := hSat
  obtain ⟨s, hRws, hAll⟩ := hEx
  have hR : M.F.R s₁ s w := by
    rewrite [P.r₁] at hRws
    obtain ⟨t, u, hw_mem, hs_eq⟩ := hRws
    rewrite [P.s₁]
    exact ⟨t, u, hs_eq, hw_mem⟩
  exact hAll w hR hSat

lemma soundness_temporal_forward₂ (φ : Formula) :
    ⊨ φ → ([s₂] ⟨r₂⟩ φ) := by
  intros F P M PS hEq w hSat
  subst hEq
  obtain ⟨hSat₁, hSat₂⟩ := hSat
  simp only
    [ satisfies, Decidable.not_not, not_exists, not_and, not_forall
    , Classical.not_imp ] at hSat₁ hSat₂
  obtain ⟨s, hRws, hAll⟩ := hSat₂
  have hRsw : M.F.R r₂ s w := by
    rewrite [P.s₂] at hRws
    obtain ⟨t, u, hw_eq, hs_mem⟩ := hRws
    rewrite [P.r₂]
    exact ⟨t, u, hw_eq ▸ hs_mem, hw_eq⟩
  exact hAll w hRsw hSat₁

lemma soundness_temporal_backward₂ (φ : Formula) :
    ⊨ φ → ([r₂] ⟨s₂⟩ φ) := by
  intros F P M PS hEq w hSat
  subst hEq
  obtain ⟨hSat₁, hSat₂⟩ := hSat
  simp only
    [ satisfies, Decidable.not_not, not_exists, not_and, not_forall
    , Classical.not_imp ] at hSat₁ hSat₂
  obtain ⟨s, hRws, hAll⟩ := hSat₂
  have hRsw : M.F.R s₂ s w := by
    rewrite [P.r₂] at hRws
    obtain ⟨t, u, hw_mem, hs_eq⟩ := hRws
    rewrite [P.s₂]
    exact ⟨t, u, hs_eq, hw_mem⟩
  exact hAll w hRsw hSat₁

lemma soundness_same_domain :
    ⊨ (⟨r₁⟩ ⊤') ↔ (⟨r₂⟩ ⊤') := by
  intros _ P M _ hEq w
  subst hEq
  constructor
  . intros hSat₁
    obtain ⟨hSat₂, hAll⟩ := hSat₁
    simp only
      [ satisfies, not_false_eq_true, and_true, not_exists, not_forall
      , Decidable.not_not ] at hAll hSat₂
    obtain ⟨s, hRws⟩ := hSat₂
    rewrite [P.r₁] at hRws
    obtain ⟨a, b, hw_mem, rfl⟩ := hRws
    have hR₂ : M.F.R r₂ w b := P.r₂.mpr ⟨s, b, hw_mem, rfl⟩
    exact hAll b hR₂
  . intros hSat₁
    obtain ⟨hSat₂, hAll⟩ := hSat₁
    simp only
      [ satisfies, not_false_eq_true, and_true, not_exists, not_forall
      , Decidable.not_not ] at hAll hSat₂
    obtain ⟨t, hRwt⟩ := hSat₂
    rewrite [P.r₂] at hRwt
    obtain ⟨a, b, hw_mem, rfl⟩ := hRwt
    have hR₁ : M.F.R r₁ w a := P.r₁.mpr ⟨a, t, hw_mem, rfl⟩
    exact hAll a hR₁

lemma soundness_same_domain₂ :
    ⊨ (⟨s₁⟩ ⊤') ↔ (⟨s₂⟩ ⊤') := by
  intros _ P M _ hEq w
  subst hEq
  constructor
  . intros hSat₁
    obtain ⟨hSat₂, hAll⟩ := hSat₁
    simp only
      [ satisfies, not_false_eq_true, and_true, not_exists, not_forall
      , Decidable.not_not ] at hAll hSat₂
    obtain ⟨z, hz⟩ := State.serial w w
    exact hAll z (P.s₂.mpr ⟨w, w, rfl, hz⟩)
  . intros hSat₁
    obtain ⟨hSat₂, hAll⟩ := hSat₁
    simp only
      [ satisfies, not_false_eq_true, and_true, not_exists, not_forall
      , Decidable.not_not ] at hAll hSat₂
    obtain ⟨z, hz⟩ := State.serial w w
    exact hAll z (P.s₁.mpr ⟨w, w, rfl, hz⟩)

lemma soundness_unicity (φ : Formula) :
    ⊨ (⟨s₁ ; r₁⟩ φ) ↔ ([s₁ ; r₁] φ) := by
  intros _ _ M _ _ w
  constructor
  . intros hAnd
    obtain ⟨hSat₁, hSat₂⟩ := hAnd
    simp only [satisfies, Decidable.not_not] at hSat₁ hSat₂
    obtain ⟨s, hRws, hSat₁⟩ := hSat₁
    obtain ⟨x, hRwx, hNotSat⟩ := hSat₂
    have hsEqw : s = w := by
      rewrite [Standard₀.comp] at hRws
      rewrite [s₁_comp_r₁] at hRws
      exact hRws.symm
    have hxEqw : x = w := by
      rewrite [Standard₀.comp, s₁_comp_r₁] at hRwx
      exact hRwx.symm
    rewrite [hsEqw] at hSat₁
    rewrite [hxEqw] at hNotSat
    exact hNotSat hSat₁
  . intros hSat
    simp only [satisfies, Decidable.not_not, not_exists, not_and] at hSat
    obtain ⟨hPos, hNeg⟩ := hSat
    have hReach : M.F.R (s₁ ; r₁) w w := by rw [Standard₀.comp, s₁_comp_r₁]
    have hPhiHolds : (M, w) ⊨ φ := hPos w hReach
    have hPhiNotHolds : ¬ (M, w) ⊨ φ := hNeg w hReach
    exact hPhiNotHolds hPhiHolds

lemma soundness_unicity₂ (φ : Formula) :
    ⊨ (⟨s₂ ; r₂⟩ φ) ↔ ([s₂ ; r₂] φ) := by
  intros _ _ M _ _ w
  constructor
  . intros hAnd
    obtain ⟨hSat₁, hSat₂⟩ := hAnd
    simp only [satisfies, Decidable.not_not] at hSat₁ hSat₂
    obtain ⟨s, hRws, hSat₁⟩ := hSat₁
    obtain ⟨x, hRwx, hNotSat⟩ := hSat₂
    have hsEqw : s = w := by
      rewrite [Standard₀.comp] at hRws
      rewrite [s₂_comp_r₂] at hRws
      exact hRws.symm
    have hxEqw : x = w := by
      rewrite [Standard₀.comp, s₂_comp_r₂] at hRwx
      exact hRwx.symm
    rewrite [hsEqw] at hSat₁
    rewrite [hxEqw] at hNotSat
    exact hNotSat hSat₁
  . intros hSat
    simp only [satisfies, Decidable.not_not, not_exists, not_and] at hSat
    obtain ⟨hPos, hNeg⟩ := hSat
    have hReach : M.F.R (s₂ ; r₂) w w := by rw [Standard₀.comp, s₂_comp_r₂]
    have hPhiHolds : (M, w) ⊨ φ := hPos w hReach
    have hPhiNotHolds : ¬ (M, w) ⊨ φ := hNeg w hReach
    exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_id (φ : Formula) :
    ⊨ ([s₁ ; r₂] φ) → φ := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hSat, hPhiNotHolds⟩ := hAnd
  simp only
    [satisfies, not_exists, not_and, Decidable.not_not, not_forall, Classical.not_imp] at hSat
  have hReach : M.F.R (s₁ ; r₂) w w := by
    rewrite [Standard₀.comp, s₁_comp_r₂]
    exact State.equiv.refl w
  have hPhiHolds : (M, w) ⊨ φ := hSat w hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_diamond (φ : Formula) :
    ⊨ φ → ([s₁ ; r₂] ⟨s₁ ; r₂⟩ φ) := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hPhiHolds, hSat₂⟩ := hAnd
  simp only [satisfies, Decidable.not_not] at hPhiHolds hSat₂
  simp only [not_exists, not_and] at hSat₂
  obtain ⟨s, hRws, hAll⟩ := hSat₂
  have hReach : M.F.R (s₁ ; r₂) s w := by
    rewrite [Standard₀.comp, s₁_comp_r₂] at *
    exact State.equiv.symm hRws
  have hPhiNotHolds : ¬ (M, w) ⊨ φ := hAll w hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_store_restore_iterate (φ : Formula) :
    ⊨ ([s₁ ; r₂] φ) → ([s₁ ; r₂] [s₁ ; r₂] φ) := by
  intros _ _ M _ _ w hAnd
  obtain ⟨hAll, hSat⟩ := hAnd
  simp only [satisfies, Decidable.not_not] at hAll hSat
  simp only [not_exists, not_and, Decidable.not_not] at hAll
  obtain ⟨s, hRws, t, hRst, hPhiNotHolds⟩ := hSat
  have hReach : M.F.R (s₁ ; r₂) w t := by
    rewrite [Standard₀.comp, s₁_comp_r₂] at *
    exact State.equiv.trans hRws hRst
  have hPhiHolds : (M, t) ⊨ φ := hAll t hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_equiv_subsume (α : Program) (φ : Formula) :
    ⊨ (([s₁ ; r₂] φ) → ([α] φ)) := by
  intros F PF M PS hEq w hAnd
  subst hEq
  obtain ⟨hAll, hEx⟩ := hAnd
  simp only
    [satisfies, not_exists, not_and, Decidable.not_not, not_forall, Classical.not_imp]
      at hAll hEx
  obtain ⟨s, hRel, hPhiNotHolds⟩ := hEx
  have hReach : M.F.R (s₁ ; r₂) w s := by
    rewrite [Standard₀.comp]
    obtain ⟨z, hz⟩ := State.serial w s
    exact ⟨z, PF.s₁.mpr ⟨w, s, rfl, hz⟩, PF.r₂.mpr ⟨w, s, hz, rfl⟩⟩
  have hPhiHolds : (M, s) ⊨ φ := hAll s hReach
  exact hPhiNotHolds hPhiHolds

lemma soundness_modus_ponens (φ₁ φ₂ : Formula) (ih₁ : ⊨ φ₁) (ih₂ : ⊨ φ₁ → φ₂) :
    ⊨ φ₂ := by
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

lemma soundness_necessitation (α : Program) (φ : Formula) (ih : ⊨ φ) :
    ⊨ [α] φ := by
  intros _ _ M _ hEq w hSat
  obtain ⟨s, _, hPhiNotHolds⟩ := hSat
  have hPhiHolds : (M, s) ⊨ φ := ih hEq
  exact hPhiNotHolds hPhiHolds

theorem soundness_general :
    ∀ {Γ : Set Formula} {φ : Formula}, (Γ ⊢ φ) →
    (∀ ψ ∈ Γ, ⊨ ψ) → ⊨ φ := by
  intros _ _ h
  induction h with
  | premise hMem =>
      intros hIn
      apply hIn
      exact hMem
  | axiom' ax =>
      intros
      cases ax with
      -- Propositional Logic Axioms
      | axiomI => apply soundness_axiom_I
      | axiomK => apply soundness_axiom_K
      | axiomS => apply soundness_axiom_S
      | conjIntro => apply soundness_conj_intro
      | conjElimL => apply soundness_conj_elimL
      | conjElimR => apply soundness_conj_elimR
      | contradiction => apply soundness_contradiction
      | negIntro => apply soundness_neg_intro
      | negElim => apply soundness_neg_elim
      -- Classical Logic Axiom
      | classicalReductio => apply soundness_classical_reductio
      -- Modal Axioms
      | duality => apply soundness_duality
      | modalK => apply soundness_modal_K
      | modalComposition => apply soundness_composition
      | modalChoice => apply soundness_choice
      -- RSPDL₀ Specific Axioms
      | functionalR₁ => apply soundness_functional_r₁
      | functionalR₂ => apply soundness_functional_r₂
      | temporalForward => apply soundness_temporal_forward
      | temporalBackward => apply soundness_temporal_backward
      | temporalForward₂ => apply soundness_temporal_forward₂
      | temporalBackward₂ => apply soundness_temporal_backward₂
      | sameDomain => apply soundness_same_domain
      | sameDomain₂ => apply soundness_same_domain₂
      | unicity => apply soundness_unicity
      | unicity₂ => apply soundness_unicity₂
      | storeRestoreId => apply soundness_store_restore_id
      | storeRestoreDiamond => apply soundness_store_restore_diamond
      | storeRestoreIterate => apply soundness_store_restore_iterate
      | equivSubsume => apply soundness_equiv_subsume
  | modusPonens _ _ ih₁ ih₂ =>
      intros hIn
      apply soundness_modus_ponens
      . exact ih₁ hIn
      . exact ih₂ hIn
  | necessitation _ ih =>
      intros
      apply soundness_necessitation
      apply ih
      simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]

theorem soundness : ∀ {φ : Formula},
    (⊢ φ) →
    (⊨ φ) := by
  intros _ h
  apply soundness_general h
  simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true]
