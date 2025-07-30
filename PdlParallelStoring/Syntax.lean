----------------------------------------------------------------------------------------------------
-- PRSPDL Syntax
----------------------------------------------------------------------------------------------------
-- We define propositions and instructions as aliases for strings.
abbrev Ψ := String

-- Mutual recursive syntax for formulae and programs.
mutual
  inductive Φ where
    | false : Φ
    | atomic : Ψ → Φ
    | neg : Φ → Φ
    | conj : Φ → Φ → Φ
    | diamond : π → Φ → Φ
    deriving BEq
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

notation "⊥'" => false
prefix:max "¬ " => neg
infixr:70 " ∧ " => conj
notation:50 "⟨" α "⟩ " φ => diamond α φ

infixl:80 " ; " => comp
infixr:70 " ∪ " => choice
postfix:max " ★" => iter
infixr:60 " ‖ " => parallel
postfix:max " ?" => test

def IsPropositional : Φ → Prop
  | Φ.false => True
  | Φ.atomic _ => True
  | Φ.neg φ => IsPropositional φ
  | Φ.conj φ₁ φ₂ => IsPropositional φ₁ ∧ IsPropositional φ₂
  | Φ.diamond _ _ => False

def eval (assign : Ψ → Bool) : (φ : Φ) → IsPropositional φ → Bool
  | Φ.false, _ => false
  | Φ.atomic ψ, _ => assign ψ
  | Φ.neg φ, h => !(eval assign φ h)
  | Φ.conj φ₁ φ₂, h =>
      let h₁ : IsPropositional φ₁ := h.1
      let h₂ : IsPropositional φ₂ := h.2
      (eval assign φ₁ h₁) && (eval assign φ₂ h₂)
  | Φ.diamond _ _, h => False.elim h

def IsTautology (φ : Φ) : Prop :=
  ∃ (h : IsPropositional φ), ∀ assign, eval assign φ h = Bool.true

-- Formulae enumeration.
axiom encode : Φ → Nat
axiom decode : Nat → Option Φ
axiom countable : ∀ {φ}, decode (encode φ) = some φ

----------------------------------------------------------------------------------------------------
-- Derived Logical Operators
----------------------------------------------------------------------------------------------------
-- Def) ⊤ ≡ ¬⊥
abbrev true : Φ :=
  ¬ ⊥'
notation "⊤'" => true

-- Def) φ₁ ∨ φ₂ ≡ ¬ (¬φ₁ ∧ ¬φ₂)
abbrev disj (φ₁ φ₂ : Φ) : Φ :=
  ¬ ((¬ φ₁) ∧ (¬ φ₂))
infixr:60 " ∨ " => disj

-- Def) φ₁ → φ₂ ≡ ¬ φ₁ ∨ φ₂
abbrev impl (φ₁ φ₂ : Φ) : Φ :=
  (¬ φ₁) ∨ φ₂
infixr:55 " → " => impl

-- Def) φ₁ ↔ φ₂ ≡ (φ₁ → φ₂) ∧ (φ₂ → φ₁)
abbrev bicond (φ₁ φ₂ : Φ) : Φ :=
  (φ₁ → φ₂) ∧ (φ₂ → φ₁)
infixr:55 " ↔ " => bicond

-- Def) [α] φ ≡ ¬ ⟨α⟩ ¬φ
abbrev box (α : π) (φ : Φ) : Φ :=
  ¬ (⟨α⟩ (¬ φ))
notation:50 "[" α "] " φ => box α φ

----------------------------------------------------------------------------------------------------
-- Derived Control Structures
----------------------------------------------------------------------------------------------------
-- Def)   skip α
--      ≡ ⊤?
abbrev skip : π :=
  ⊤' ?

-- Def)   fail α
--      ≡ ⊥?
abbrev fail : π :=
  ⊥' ?

-- Def)   if φ₁ → φ₂ | ... | φₙ → αₙ fi
--      ≡  φ₁? ; α₁ ∪ ... ∪ φₙ? ; αₙ
def pdlIf (branches : List (Φ × π)) : π :=
  branches.foldr
    (λ (pair : Φ × π) (acc : π) =>
      let (φ, α) := pair
      ((φ ?) ; α) ∪ acc)
    skip

-- Def)   do φ₁ → α₁ | ... | φₙ → α₂ od
--      ≡ (φ₁? ; α₁ ∪ ... ∪ φₙ? ; αₙ)★ ; (¬φ₁ ∧ ... ∧ ¬φₙ)?
def pdlDo (branches : List (Φ × π)) : π :=
  let loop : π := (pdlIf branches) ★
  let exit : Φ :=
    branches.foldr
      (λ (pair : Φ × π) (acc : Φ) =>
        let (φ, _) := pair
        (¬ φ) ∧ acc)
      ⊤'
  loop ; (exit ?)

-- Def)   if φ then α else β
--      ≡ φ? ; α ∪ ¬φ? ; β
abbrev ifThenElse (φ : Φ) (α β : π) : π :=
  pdlIf [(φ, α), (¬ φ, β)]

notation "If" c:arg "{" t "}" => ifThenElse c t skip
notation "If" c:arg "{" t "}" "Else" "{" f "}" => ifThenElse c t f

-- Def)   while φ do α
--      ≡ (φ? ; α)★ ; ¬φ?
abbrev whileDo (φ : Φ) (α : π) : π :=
  pdlDo [(φ, α)]

notation "While" c:arg "{" b "}" => whileDo c b

-- Def)   repeat α until φ
--      ≡ α ; (¬φ? ; α)★ ; φ?
abbrev repeatUntil (α : π) (φ : Φ) : π :=
  α ; whileDo (¬ φ) α
