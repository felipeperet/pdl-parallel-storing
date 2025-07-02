import Mathlib.Logic.Basic

import PdlParallelStoring.Syntax

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
  | functionalR₁ φ : RSPDL₀ ((⟨π.r₁⟩ φ) → ([π.r₁] φ))
  | functionalR₂ φ : RSPDL₀ ((⟨π.r₂⟩ φ) → ([π.r₂] φ))
  | temporalForward φ : RSPDL₀ (φ → ([π.s₁] ⟨π.r₁⟩ φ))
  | temporalBackward φ : RSPDL₀ (⟨π.s₁⟩ ⟨π.r₁⟩ φ → φ)
  | s₁r₁Converse φ : RSPDL₀ ((⟨π.s₁⟩ φ) → (⟨π.r₁⟩ φ))
  | r₁s₁Converse φ : RSPDL₀ ((⟨π.r₁⟩ φ) → (⟨π.s₁⟩ φ))
  | temporalForward₂ φ : RSPDL₀ (φ → ([π.s₂] ⟨π.r₂⟩ φ))
  | temporalBackward₂ φ : RSPDL₀ (⟨π.s₂⟩ ⟨π.r₂⟩ φ → φ)
  | s₂r₂Converse φ : RSPDL₀ ((⟨π.s₂⟩ φ) → (⟨π.r₂⟩ φ))
  | r₂s₂Converse φ : RSPDL₀ (⟨π.r₂⟩ φ → (⟨π.s₂⟩ φ))
  | sameDomain : RSPDL₀ ((⟨π.r₁⟩ ⊤') ↔ (⟨π.r₂⟩ ⊤'))
  | unicity φ : RSPDL₀ ((⟨π.s₁ ; π.r₁⟩ φ) ↔ ([π.s₁ ; π.r₁] φ))
  | storeRestoreId φ : RSPDL₀ (([π.s₁ ; π.r₂] φ) → φ)
  | storeRestoreDiamond φ : RSPDL₀ (φ → ([π.s₁ ; π.r₂] ⟨π.s₁ ; π.r₂⟩ φ))
  | storeRestoreIterate φ : RSPDL₀ (([π.s₁ ; π.r₂] φ) → ([π.s₁ ; π.r₂] [π.s₁ ; π.r₂] φ))
  -- Inference Rules
  | modusPonens φ₁ φ₂ : RSPDL₀ φ₁ → RSPDL₀ (φ₁ → φ₂) → RSPDL₀ φ₂
  | necessitation α φ : RSPDL₀ φ → RSPDL₀ ([α] φ)

notation:40 "⊢ " φ => RSPDL₀ φ
