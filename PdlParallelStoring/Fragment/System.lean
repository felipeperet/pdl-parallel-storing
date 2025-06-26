import Mathlib.Logic.Basic

import PdlParallelStoring.Semantics
import PdlParallelStoring.Properties

open Classical

----------------------------------------------------------------------------------------------------
-- Axiomatic System for RSPDL₀
----------------------------------------------------------------------------------------------------
-- This is a fragment called RSPDL₀. In this fragment, we do not allow the use of the operators of
-- test (?), iteration (★) and parallel composition (‖).

-- Def) Provability in RSPDL₀: ⊢ φ means φ is derivable from the axioms and inference rules.
inductive RSPDL₀ : Φ → Prop where
  -- Axioms
  | tautology φ : φ.isTautology → RSPDL₀ φ
  | composition α β φ : RSPDL₀ (([α ; β] φ) ↔ ([α] [β] φ))
  | choice α β φ : RSPDL₀ (([α ∪ β] φ) ↔ (([α] φ) ∧ ([β] φ)))
  | K α ψ φ : RSPDL₀ (([α] (φ → ψ)) → (([α] φ) → ([α] ψ)))
  | functional φ : RSPDL₀ ((⟨π.r₁⟩ φ) → ([π.r₁] φ))
  | temporal φ : RSPDL₀ (φ → ([π.s₁] ⟨π.r₁⟩ φ))
  | sameDomain : RSPDL₀ ((⟨π.r₁⟩ ⊤) ↔ (⟨π.r₂⟩ ⊤))
  | unicity φ : RSPDL₀ ((⟨π.s₁ ; π.r₁⟩ φ) ↔ ([π.s₁ ; π.r₁] φ))
  | storeRestoreId φ : RSPDL₀ ([π.s₁ ; π.r₂] φ → φ)
  | storeRestoreDiamond φ : RSPDL₀ (φ → ([π.s₁ ; π.r₂] ⟨π.s₁ ; π.r₂⟩ φ))
  | storeRestoreIterate φ : RSPDL₀ (([π.s₁ ; π.r₂] φ) → ([π.s₁ ; π.r₂] [π.s₁ ; π.r₂] φ))
  -- Inference Rules
  | modusPonens ψ φ : RSPDL₀ φ → RSPDL₀ (φ → ψ) → RSPDL₀ ψ
  | necessitation α φ : RSPDL₀ φ → RSPDL₀ ([α] φ)

notation:40 "⊢ " φ => RSPDL₀ φ

lemma eval_iff_satisfies (M : Model) (w : M.F.W) :
  ∀ (φ : Φ) (h : φ.isPropositional),
    (eval (λ ψ => decide (M.V ψ w)) φ h = Bool.true) ↔ ((M, w) ⊨ φ)
  | Φ.false, h => by simp [eval, satisfies]
  | Φ.atomic ψ, h => by simp [eval, satisfies]
  | Φ.neg φ, h => by
      simp [eval, satisfies]
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

theorem soundness : ∀ {φ : Φ}, (⊢ φ) → (⊨ φ) := by
  intros φ h
  cases h with
  | tautology _ t =>
      obtain ⟨hProp, hEval⟩ := t
      intros _ _ M _ _ w
      let assign := λ ψ => decide (M.V ψ w)
      have hTrue : eval assign φ hProp = Bool.true := hEval assign
      have hLemma : (eval assign φ hProp = Bool.true) ↔ ((M, w) ⊨ φ) :=
        eval_iff_satisfies M w φ hProp
      rw [← hLemma]
      exact hTrue
  | functional =>
      intros _ P M _ hEq w hSat
      simp [satisfies] at hSat
      obtain ⟨h₁, h₂⟩ := hSat
      obtain ⟨s, hRws, hSat⟩ := h₁
      subst hEq
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
  | temporal φ =>
      intros _ P M _ hEq w hSat
      simp [satisfies] at hSat
      obtain ⟨hSat₁, hSat₂⟩ := hSat
      obtain ⟨s, hAnd⟩ := hSat₂
      obtain ⟨hRws, hAll⟩ := hAnd
      have hR₁ : M.F.R π.r₁ s w :=  by
        subst hEq
        rw [P.s₁] at hRws
        obtain ⟨w', t, hw_eq, hs_eq⟩ := hRws
        rw [P.r₁]
        use w', t
      have hNotSat : ¬ (M,w) ⊨ φ := hAll w hR₁
      exact hNotSat hSat₁
  | _ => sorry
