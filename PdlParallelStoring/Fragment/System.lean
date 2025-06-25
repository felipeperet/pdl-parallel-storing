import Mathlib.Logic.Basic

import PdlParallelStoring.Semantics

open Classical

----------------------------------------------------------------------------------------------------
-- Axiomatic System for RSPDL₀
----------------------------------------------------------------------------------------------------
-- This is a fragment called RSPDL₀. In this fragment, we do not allow the use of the operators of
-- test (?), iteration (★) and parallel composition (‖).

inductive Provable : Φ → Prop where
  | taut φ : isTautology φ → Provable φ
  -- ...

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

lemma tautSound : ∀ {φ}, isTautology φ → (⊨ φ) := by
  intro φ hTaut
  obtain ⟨hProp, hEval⟩ := hTaut
  intros F M MF w
  let assign := fun ψ => decide (M.V ψ w)
  have h_true : eval assign φ hProp = Bool.true := hEval assign
  have key_lemma : (eval assign φ hProp = Bool.true) ↔ ((M, w) ⊨ φ) :=
    evalMatchesSatisfies M w φ hProp
  rw [← key_lemma]
  exact h_true

theorem soundness : ∀ {φ : Φ}, (⊢ φ) → (⊨ φ) := by
  intros φ h
  cases h with
  | taut t => exact tautSound t
