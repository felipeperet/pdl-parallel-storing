import PdlParallelStoring.Syntax

/- Example 1)
   When start to run on input u, stores the initial state u at the second coordinate of an ordered
   pair, then executes actions α and β over the first coordinate of the pair, successively and,
   after that, returns the initial state by restoring the second coordinate. -/
def π₁ (α β : π) : π :=
  π.s₂ ;
  (α ‖ skip) ;
  (β ‖ skip) ;
  π.r₂

/- Example 2)
   When start to run on input u, stores the initial state u at the second coordinate of an ordered
   pair, then executes action α on the first coordinate of the current pair, until property φ is
   true in the first coordinate of the current pair, then after that, returns to the initial state
   by restoring the second coordinate of the current pair. -/
def π₂ (α : π) (φ : Φ) : π :=
  π.s₂ ;
  ((((¬ φ) ?) ‖ skip) ; (α ‖ skip))★ ;
  (φ ? ‖ skip) ;
  π.r₂

/-  Example 3)
    When start to run on input u, stores the initial state u at second coordinate of an ordered
    pair, then executes action α over the first coordinate of the pair and, after that, if property
    φ is true at the initial state then it performs action β over the first coordinate of the
    current pair, else it performs action γ over it. -/
def π₃ (α β γ : π) (φ : Φ) : π :=
  π.s₂ ;
  (α ‖ skip) ;
  (((⟨π.r₂ ; φ ?⟩ ⊤) ? ; (β ‖ skip)) ∪ ((⟨π.r₂ ; (¬ φ) ?⟩ ⊤) ? ; (γ ‖ skip)))

/-  Example 4)
    When start to run on input u, stores the initial state u at second coordinate of an ordered
    pair, then executes action α over the first coordinate of the pair and, after that, it either
    stores the current state as the second coordinate of an ordered pair, executes action α over
    the new first coordinate, and returns to the second pair obtained in the computation; or
    executes action β over the first coordinate of the pair and returns to the initial state. -/
def π₄ (α β : π) : π :=
  π.s₂ ;
  (α ‖ skip) ;
  (π.s₂ ; (α ‖ skip) ; π.r₂) ∪ ((β ‖ skip) ; π.r₂)
