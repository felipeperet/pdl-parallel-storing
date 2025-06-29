import Mathlib.Logic.Basic

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
  | K α φ₁ φ₂ : RSPDL₀ (([α] (φ₁ → φ₂)) → (([α] φ₁) → ([α] φ₂)))
  | functional φ : RSPDL₀ ((⟨π.r₁⟩ φ) → ([π.r₁] φ))
  | temporal φ : RSPDL₀ (φ → ([π.s₁] ⟨π.r₁⟩ φ))
  | sameDomain : RSPDL₀ ((⟨π.r₁⟩ ⊤) ↔ (⟨π.r₂⟩ ⊤))
  | unicity φ : RSPDL₀ ((⟨π.s₁ ; π.r₁⟩ φ) ↔ ([π.s₁ ; π.r₁] φ))
  | storeRestoreId φ : RSPDL₀ (([π.s₁ ; π.r₂] φ) → φ)
  | storeRestoreDiamond φ : RSPDL₀ (φ → ([π.s₁ ; π.r₂] ⟨π.s₁ ; π.r₂⟩ φ))
  | storeRestoreIterate φ : RSPDL₀ (([π.s₁ ; π.r₂] φ) → ([π.s₁ ; π.r₂] [π.s₁ ; π.r₂] φ))
  -- Inference Rules
  | modusPonens φ₁ φ₂ : RSPDL₀ φ₁ → RSPDL₀ (φ₁ → φ₂) → RSPDL₀ φ₂
  | necessitation α φ : RSPDL₀ φ → RSPDL₀ ([α] φ)

notation:40 "⊢ " φ => RSPDL₀ φ
