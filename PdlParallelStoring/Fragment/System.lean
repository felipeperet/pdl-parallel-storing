import Mathlib.Logic.Basic

import PdlParallelStoring.Semantics

open Classical

----------------------------------------------------------------------------------------------------
-- Axiomatic System for RSPDL₀
----------------------------------------------------------------------------------------------------
-- This is a fragment called RSPDL₀. In this fragment, we do not allow the use of the operators of
-- test (?), iteration (★) and parallel composition (‖).

-- Def) Provability in RSPDL₀: ⊢ φ means φ is derivable from the axioms and inference rules.
inductive Provable : Φ → Prop where
  -- Axioms
  | tautology φ : isTautology φ → Provable φ
  | composition α β φ : Provable (([α ; β] φ) ↔ ([α] [β] φ))
  | choice α β φ : Provable (([α ∪ β] φ) ↔ (([α] φ) ∧ ([β] φ)))
  | K α ψ φ : Provable (([α] (φ → ψ)) → (([α] φ) → ([α] ψ)))
  | functional φ : Provable ((⟨π.r₁⟩ φ) → ([π.r₁] φ))
  | temporal φ : Provable (φ → ([π.s₁] ⟨π.r₁⟩ φ))
  | sameDomain : Provable ((⟨π.r₁⟩ ⊤) ↔ (⟨π.r₂⟩ ⊤))
  | unicity φ : Provable ((⟨π.s₁ ; π.r₁⟩ φ) ↔ ([π.s₁ ; π.r₁] φ))
  | storeRestoreId φ : Provable ([π.s₁ ; π.r₂] φ → φ)
  | storeRestoreDiamond φ : Provable (φ → ([π.s₁ ; π.r₂] ⟨π.s₁ ; π.r₂⟩ φ))
  | storeRestoreIterate φ : Provable (([π.s₁ ; π.r₂] φ) → ([π.s₁ ; π.r₂] [π.s₁ ; π.r₂] φ))
  -- Inference Rules
  | modusPonens ψ φ : Provable φ → Provable (φ → ψ) → Provable ψ
  | necessitation α φ : Provable φ → Provable ([α] φ)

notation:40 "⊢ " φ => Provable φ

lemma evalMatchesSatisfies (M : Model) (w : M.F.W) :
  ∀ (φ : Φ) (h : isPropositional φ),
    (eval (λ ψ => decide (M.V ψ w)) φ h = Bool.true) ↔ ((M, w) ⊨ φ)
  | Φ.false, h => by simp [eval, satisfies]
  | Φ.atomic ψ, h => by simp [eval, satisfies]
  | Φ.neg φ, h => by
      simp [eval, satisfies]
      have ih := evalMatchesSatisfies M w φ h
      constructor
      · intros hFalse hSat
        have hTrue := ih.mpr hSat
        rw [hTrue] at hFalse
        simp at hFalse
      · intro hNotSat
        have _ : eval (λ ψ => decide (M.V ψ w)) φ h ≠ true := by
          intro hTrue
          have hSat := ih.mp hTrue
          exact hNotSat hSat
        cases hEval : eval (λ ψ => decide (M.V ψ w)) φ h with
        | false => rfl
        | true => contradiction
  | Φ.conj φ₁ φ₂, h => by
      simp [eval, satisfies]
      have ih₁ := evalMatchesSatisfies M w φ₁ h.1
      have ih₂ := evalMatchesSatisfies M w φ₂ h.2
      constructor
      · intro ⟨h₁True, h₂True⟩
        exact ⟨ih₁.mp h₁True, ih₂.mp h₂True⟩
      · intro ⟨h₁Sat, h₂Sat⟩
        exact ⟨ih₁.mpr h₁Sat, ih₂.mpr h₂Sat⟩
  | Φ.diamond π φ, h => by
      exfalso
      exact h

lemma tautologySound : ∀ {φ}, isTautology φ → (⊨ φ) := by
  intro φ hTaut
  obtain ⟨hProp, hEval⟩ := hTaut
  intros _ _ M _ _ w
  let assign := λ ψ => decide (M.V ψ w)
  have hTrue : eval assign φ hProp = Bool.true := hEval assign
  have hLemma : (eval assign φ hProp = Bool.true) ↔ ((M, w) ⊨ φ) :=
    evalMatchesSatisfies M w φ hProp
  rw [← hLemma]
  exact hTrue

theorem soundness : ∀ {φ : Φ}, (⊢ φ) → (⊨ φ) := by
  intros φ h
  cases h with
  | tautology _ t => exact tautologySound t
  | functional φ₁ =>
      intros _ _ _ _ _ _ hSat
      simp [satisfies] at hSat
      obtain ⟨h₁, h₂⟩ := hSat
      obtain ⟨s, h₁₁⟩ := h₁
      obtain ⟨hRws, hSat⟩ := h₁₁
      sorry
  | _ => sorry
