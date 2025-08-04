----------------------------------------------------------------------------------------------------
-- PRSPDL Syntax
----------------------------------------------------------------------------------------------------
abbrev Literal := String

mutual
  inductive Formula where
    | false : Formula
    | atomic : Literal → Formula
    | neg : Formula → Formula
    | conj : Formula → Formula → Formula
    | diamond : Program → Formula → Formula
    deriving BEq
  inductive Program where
    | atomic : Literal → Program
    | comp : Program → Program → Program
    | choice : Program → Program → Program
    | iter : Program → Program
    | parallel : Program → Program → Program
    | test : Formula → Program
    | s₁ : Program
    | s₂ : Program
    | r₁ : Program
    | r₂ : Program
    deriving BEq
end
open Formula Program

notation "⊥'" => false
prefix:max "¬ " => neg
infixr:70 " ∧ " => conj
notation:50 "⟨" α "⟩ " φ => diamond α φ

infixl:80 " ; " => comp
infixr:70 " ∪ " => choice
postfix:max " ★" => iter
infixr:60 " ‖ " => parallel
postfix:max " ?" => test

-- Formulae enumeration.
axiom encode : Formula → Nat
axiom decode : Nat → Option Formula
axiom countable : ∀ {φ}, decode (encode φ) = some φ

----------------------------------------------------------------------------------------------------
-- Derived Logical Operators
----------------------------------------------------------------------------------------------------
-- Def) ⊤ ≡ ¬⊥
abbrev true : Formula :=
  ¬ ⊥'
notation "⊤'" => true

-- Def) φ₁ ∨ φ₂ ≡ ¬ (¬φ₁ ∧ ¬φ₂)
abbrev disj (φ₁ φ₂ : Formula) : Formula :=
  ¬ ((¬ φ₁) ∧ (¬ φ₂))
infixr:60 " ∨ " => disj

-- Def) φ₁ → φ₂ ≡ ¬ φ₁ ∨ φ₂
abbrev impl (φ₁ φ₂ : Formula) : Formula :=
  (¬ φ₁) ∨ φ₂
infixr:55 " → " => impl

-- Def) φ₁ ↔ φ₂ ≡ (φ₁ → φ₂) ∧ (φ₂ → φ₁)
abbrev bicond (φ₁ φ₂ : Formula) : Formula :=
  (φ₁ → φ₂) ∧ (φ₂ → φ₁)
infixr:55 " ↔ " => bicond

-- Def) [α] φ ≡ ¬ ⟨α⟩ ¬φ
abbrev box (α : Program) (φ : Formula) : Formula :=
  ¬ (⟨α⟩ (¬ φ))
notation:50 "[" α "] " φ => box α φ

----------------------------------------------------------------------------------------------------
-- Derived Control Structures
----------------------------------------------------------------------------------------------------
-- Def)   skip α
--      ≡ ⊤?
abbrev skip : Program :=
  ⊤' ?

-- Def)   fail α
--      ≡ ⊥?
abbrev fail : Program :=
  ⊥' ?
