import PdlParallelStoring.Syntax

open Program

/- Example 1)
   When start to run on input u, stores the initial state u at the second coordinate of an ordered
   pair, then executes actions α and β over the first coordinate of the pair, successively and,
   after that, returns the initial state by restoring the second coordinate. -/
def π₁ (α β : Program) : Program :=
  s₂ ;
  (α ‖ skip) ;
  (β ‖ skip) ;
  r₂

/- Example 2)
   When start to run on input u, stores the initial state u at the second coordinate of an ordered
   pair, then executes action α on the first coordinate of the current pair, until property φ is
   true in the first coordinate of the current pair, then after that, returns to the initial state
   by restoring the second coordinate of the current pair. -/
def π₂ (α : Program) (φ : Formula) : Program :=
  s₂ ;
  ((((¬ φ) ?) ‖ skip) ; (α ‖ skip))★ ;
  (φ ? ‖ skip) ;
  r₂

/-  Example 3)
    When start to run on input u, stores the initial state u at second coordinate of an ordered
    pair, then executes action α over the first coordinate of the pair and, after that, if property
    φ is true at the initial state then it performs action β over the first coordinate of the
    current pair, else it performs action γ over it. -/
def π₃ (α β γ : Program) (φ : Formula) : Program :=
  s₂ ;
  (α ‖ skip) ;
  (((⟨r₂ ; φ ?⟩ ⊤') ? ; (β ‖ skip)) ∪ ((⟨r₂ ; (¬ φ) ?⟩ ⊤') ? ; (γ ‖ skip)))

/-  Example 4)
    When start to run on input u, stores the initial state u at second coordinate of an ordered
    pair, then executes action α over the first coordinate of the pair and, after that, it either
    stores the current state as the second coordinate of an ordered pair, executes action α over
    the new first coordinate, and returns to the second pair obtained in the computation; or
    executes action β over the first coordinate of the pair and returns to the initial state. -/
def π₄ (α β : Program ) : Program :=
  s₂ ;
  (α ‖ skip) ;
  (s₂ ; (α ‖ skip) ; r₂) ∪ ((β ‖ skip) ; r₂)
