----------------------------------------------------------------------------------------------------
-- PRSPDL Syntax
----------------------------------------------------------------------------------------------------
-- We define propositions and instructions as aliases for strings.
abbrev Ψ := String
-- Mutual recursive syntax for formulae and programs.
mutual
  -- Abstract syntax tree for Formulae.
  inductive Φ where
    | false : Φ
    | atomic : Ψ → Φ
    | neg : Φ → Φ
    | conj : Φ → Φ → Φ
    | diamond : π → Φ → Φ
    deriving BEq
  -- Abstract syntax tree for Programs.
  inductive π where
    | atomic : Ψ → π
    | comp : π → π → π
    | choice : π → π → π
    | iter : π → π
    | parallel : π → π → π
    | test : Φ → π
    | s₁ : π
    | s₂ : π
    | r₁ : π
    | r₂ : π
    deriving BEq
end
open Φ π

-- Sugar syntax for primitive formulae.
notation "⊥" => false
prefix:max "¬" => neg
infixr:70 "∧" => conj
notation:50 "⟨" α "⟩" φ => diamond α φ

-- Sugar syntax for primitive programs.
infixl:80 ";" => comp
infixr:60 "∪" => choice
postfix:max "*" => iter
infixr:75 "‖" => parallel
prefix:max "?" => test

----------------------------------------------------------------------------------------------------
-- Derived Operators
----------------------------------------------------------------------------------------------------
-- Def) ⊤ ≡ ¬ ⊥
def true : Φ := ¬ ⊥
notation "⊤" => true

-- Def) φ₁ ∨ φ₂ ≡ ¬ (¬φ₁ ∧ ¬ φ₂)
def disj (φ₁ φ₂ : Φ) : Φ := ¬ ((¬ φ₁) ∧ (¬ φ₂))
infixr:60 "∨" => disj

-- Def) φ₁ → φ₂ ≡ ¬ φ₁ ∨ φ₂
def impl (φ₁ φ₂ : Φ) : Φ := (¬ φ₁) ∨ φ₂
infixr:50 "→" => impl

-- Def) [α] φ ≡ ¬ ⟨α⟩ ¬ φ
def box (α : π) (φ : Φ) : Φ := ¬ (⟨α⟩ (¬ φ))
notation:50 "[" α "]" φ => box α φ
