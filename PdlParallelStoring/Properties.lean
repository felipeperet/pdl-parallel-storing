import PdlParallelStoring.Semantics

-- Property I) Rs₁ ; Rr₁ = Id
def s₁_comp_r₁ (F : Frame) [Structured F] [P : Proper F] :
    ∀ {s u}, Relation.Comp (F.R π.s₁) (F.R π.r₁) s u ↔ (s = u) := by
  intros s u
  constructor
  case mp =>
    intro hcomp
    unfold Relation.Comp at hcomp
    obtain ⟨t, hs₁, hr₁⟩ := hcomp
    rw [P.s₁] at hs₁
    rw [P.r₁] at hr₁
    obtain ⟨s₁, t₁, hs_eq, ht_eq⟩ := hs₁
    obtain ⟨s₂, t₂, ht_eq₂, hu_eq⟩ := hr₁
    have h_eq : s₁ ⋆ t₁ = s₂ ⋆ t₂ := by
      rw [← ht_eq]
      rw [ht_eq₂]
    have s₁_eq_s₂ : s₁ = s₂ := (State.inject.mp h_eq).1
    rw [hs_eq]
    rw [hu_eq]
    exact s₁_eq_s₂
  case mpr => sorry
