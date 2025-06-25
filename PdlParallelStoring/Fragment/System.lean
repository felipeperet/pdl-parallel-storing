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
  | tautology : isTautology φ → Provable φ
  | composition α β : Provable (([α ; β] φ) ↔ ([α] [β] φ))
  | choice α β : Provable (([α ∪ β] φ) ↔ (([α] φ) ∧ ([β] φ)))
  | K α ψ : Provable (([α] (φ → ψ)) → (([α] φ) → ([α] ψ)))
  | functional : Provable ((⟨π.r₁⟩ φ) → ([π.r₁] φ))
  | temporal : Provable (φ → ([π.s₁] ⟨π.r₁⟩ φ))
  | sameDomain : Provable ((⟨π.r₁⟩ ⊤) ↔ (⟨π.r₂⟩ ⊤))
  | unicity : Provable ((⟨π.s₁ ; π.r₁⟩ φ) ↔ ([π.s₁ ; π.r₁] φ))
  | storeRestoreId : Provable ([s₁ ; r₂] φ → φ)
  | storeRestoreDiamond : Provable (φ → ([s₁ ; r₂] ⟨s₁ ; r₂⟩ φ))
  | storeRestoreIterate : Provable (([s₁ ; r₂] φ) → ([s₁ ; r₂] [s₁ ; r₂] φ))
  -- Inference Rules
  | modusPonens ψ : Provable φ → Provable (φ → ψ) → Provable ψ
  | necessitation π : Provable φ → Provable ([π] φ)

notation:40 "⊢ " φ => Provable φ

lemma evalMatchesSatisfies (M : Model) (w : M.F.W) :
  ∀ (φ : Φ) (h : isPropositional φ),
    (eval (fun ψ => decide (M.V ψ w)) φ h = Bool.true) ↔ ((M, w) ⊨ φ)
  | Φ.false, h => by simp [eval, satisfies]
  | Φ.atomic ψ, h => by simp [eval, satisfies]
  | Φ.neg φ, h => by
      simp [eval, satisfies]
      have ih := evalMatchesSatisfies M w φ h
      constructor
      · intro hFalse
        intro hSat
        have hTrue := ih.mpr hSat
        rw [hTrue] at hFalse
        simp at hFalse
      · intro hNotSat
        have hNotTrue : eval (fun ψ => decide (M.V ψ w)) φ h ≠ true := by
          intro hTrue
          have hSat := ih.mp hTrue
          exact hNotSat hSat
        cases hEval : eval (fun ψ => decide (M.V ψ w)) φ h with
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
  intros F M MF w
  let assign := fun ψ => decide (M.V ψ w)
  have hTrue : eval assign φ hProp = Bool.true := hEval assign
  have hLemma : (eval assign φ hProp = Bool.true) ↔ ((M, w) ⊨ φ) :=
    evalMatchesSatisfies M w φ hProp
  rw [← hLemma]
  exact hTrue

theorem soundness : ∀ {φ : Φ}, (⊢ φ) → (⊨ φ) := by
  intros φ h
  cases h with
  | tautology t => exact tautologySound t
  | _ => sorry
