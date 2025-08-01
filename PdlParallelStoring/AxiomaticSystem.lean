import Mathlib.Data.Set.Basic

import PdlParallelStoring.Syntax

-- TODO: Call this module DeductiveSystem (?)

----------------------------------------------------------------------------------------------------
-- Axiomatic System for RSPDL₀ (Hilbert-style with context)
----------------------------------------------------------------------------------------------------

-- This is a fragment called RSPDL₀. In this fragment, we do not allow the use of the operators of
-- test (?), iteration (★) and parallel composition (‖).

inductive Axiom : Φ → Prop where
  -- Modal Axioms
  | composition α β φ : Axiom (([α ; β] φ) ↔ ([α] [β] φ))
  | choice α β φ : Axiom (([α ∪ β] φ) ↔ (([α] φ) ∧ ([β] φ)))
  | K α φ₁ φ₂ : Axiom (([α] (φ₁ → φ₂)) → (([α] φ₁) → ([α] φ₂)))
  -- RSPDL₀ Specific Axioms
  | functionalR₁ φ : Axiom ((⟨π.r₁⟩ φ) → ([π.r₁] φ))
  | functionalR₂ φ : Axiom ((⟨π.r₂⟩ φ) → ([π.r₂] φ))
  | temporalForward φ : Axiom (φ → ([π.s₁] ⟨π.r₁⟩ φ))
  | temporalBackward φ : Axiom (⟨π.s₁⟩ ⟨π.r₁⟩ φ → φ)
  | s₁r₁Converse φ : Axiom ((⟨π.s₁⟩ φ) → (⟨π.r₁⟩ φ))
  | r₁s₁Converse φ : Axiom ((⟨π.r₁⟩ φ) → (⟨π.s₁⟩ φ))
  | temporalForward₂ φ : Axiom (φ → ([π.s₂] ⟨π.r₂⟩ φ))
  | temporalBackward₂ φ : Axiom (⟨π.s₂⟩ ⟨π.r₂⟩ φ → φ)
  | s₂r₂Converse φ : Axiom ((⟨π.s₂⟩ φ) → (⟨π.r₂⟩ φ))
  | r₂s₂Converse φ : Axiom (⟨π.r₂⟩ φ → (⟨π.s₂⟩ φ))
  | sameDomain : Axiom ((⟨π.r₁⟩ ⊤') ↔ (⟨π.r₂⟩ ⊤'))
  | unicity φ : Axiom ((⟨π.s₁ ; π.r₁⟩ φ) ↔ ([π.s₁ ; π.r₁] φ))
  | storeRestoreId φ : Axiom (([π.s₁ ; π.r₂] φ) → φ)
  | storeRestoreDiamond φ : Axiom (φ → ([π.s₁ ; π.r₂] ⟨π.s₁ ; π.r₂⟩ φ))
  | storeRestoreIterate φ : Axiom (([π.s₁ ; π.r₂] φ) → ([π.s₁ ; π.r₂] [π.s₁ ; π.r₂] φ))

-- Deduction system with context.
inductive Deduction : Set Φ → Φ → Prop where
  | premise (Γ : Set Φ) (φ : Φ) : (φ ∈ Γ) → Deduction Γ φ
  | axiom' (Γ : Set Φ) (φ : Φ) : Axiom φ → Deduction Γ φ
  | modusPonens (Γ : Set Φ) (φ ψ : Φ) : Deduction Γ φ → Deduction Γ (φ → ψ) → Deduction Γ ψ
  | necessitation (Γ : Set Φ) (α : π) (φ : Φ) : Deduction ∅ φ → Deduction Γ ([α] φ)
  | consistency (Γ : Set Φ) (φ : Φ) : Deduction Γ φ → Deduction Γ ((¬ φ) → ⊥')
  | explosion (Γ : Set Φ) (φ : Φ) : Deduction Γ ⊥' → Deduction Γ φ
  | classicalNegation (Γ : Set Φ) (φ : Φ) : Deduction Γ ((¬ φ) → ⊥') → Deduction Γ φ

notation:40 Γ " ⊢ " φ => Deduction Γ φ

notation:40 "⊢ " φ => ∅ ⊢ φ
