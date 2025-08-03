import Mathlib.Data.Set.Basic

import PdlParallelStoring.Syntax

open Program

----------------------------------------------------------------------------------------------------
-- Axiomatic System for RSPDL₀ (Hilbert-style with context)
----------------------------------------------------------------------------------------------------
-- This is a fragment called RSPDL₀. In this fragment, we do not allow the use of the operators of
-- test (?), iteration (★) and parallel composition (‖).

inductive Axiom : Formula → Prop where
  -- Classical Logic Axioms
  | contradiction φ : Axiom ((φ ∧ (¬ φ)) → ⊥')
  | reductio φ : Axiom (((¬ φ) → ⊥') → φ)
  | conjIntro φ ψ : Axiom (φ → (ψ → (φ ∧ ψ)))
  | conjElimL φ ψ : Axiom ((φ ∧ ψ) → φ)
  | conjElimR φ ψ : Axiom ((φ ∧ ψ) → ψ)
  -- Modal Axioms
  | composition α β φ : Axiom (([α ; β] φ) ↔ ([α] [β] φ))
  | choice α β φ : Axiom (([α ∪ β] φ) ↔ (([α] φ) ∧ ([β] φ)))
  | K α φ₁ φ₂ : Axiom (([α] (φ₁ → φ₂)) → (([α] φ₁) → ([α] φ₂)))
  -- RSPDL₀ Specific Axioms
  | functionalR₁ φ : Axiom ((⟨r₁⟩ φ) → ([r₁] φ))
  | functionalR₂ φ : Axiom ((⟨r₂⟩ φ) → ([r₂] φ))
  | temporalForward φ : Axiom (φ → ([s₁] ⟨r₁⟩ φ))
  | temporalBackward φ : Axiom (⟨s₁⟩ ⟨r₁⟩ φ → φ)
  | s₁r₁Converse φ : Axiom ((⟨s₁⟩ φ) → (⟨r₁⟩ φ))
  | r₁s₁Converse φ : Axiom ((⟨r₁⟩ φ) → (⟨s₁⟩ φ))
  | temporalForward₂ φ : Axiom (φ → ([s₂] ⟨r₂⟩ φ))
  | temporalBackward₂ φ : Axiom (⟨s₂⟩ ⟨r₂⟩ φ → φ)
  | s₂r₂Converse φ : Axiom ((⟨s₂⟩ φ) → (⟨r₂⟩ φ))
  | r₂s₂Converse φ : Axiom (⟨r₂⟩ φ → (⟨s₂⟩ φ))
  | sameDomain : Axiom ((⟨r₁⟩ ⊤') ↔ (⟨r₂⟩ ⊤'))
  | unicity φ : Axiom ((⟨s₁ ; r₁⟩ φ) ↔ ([s₁ ; r₁] φ))
  | storeRestoreId φ : Axiom (([s₁ ; r₂] φ) → φ)
  | storeRestoreDiamond φ : Axiom (φ → ([s₁ ; r₂] ⟨s₁ ; r₂⟩ φ))
  | storeRestoreIterate φ : Axiom (([s₁ ; r₂] φ) → ([s₁ ; r₂] [s₁ ; r₂] φ))

-- Deduction system with context.
inductive Deduction : Set Formula → Formula → Prop where
  | premise (Γ : Set Formula) (φ : Formula) : (φ ∈ Γ) → Deduction Γ φ
  | axiom' (Γ : Set Formula) (φ : Formula) : Axiom φ → Deduction Γ φ
  | modusPonens (Γ : Set Formula) (φ ψ : Formula) :
      Deduction Γ φ →
      Deduction Γ (φ → ψ) →
      Deduction Γ ψ
  | necessitation (Γ : Set Formula) (α : Program) (φ : Formula) :
      Deduction ∅ φ →
      Deduction Γ ([α] φ)

notation:40 Γ " ⊢ " φ => Deduction Γ φ

notation:40 "⊢ " φ => ∅ ⊢ φ
