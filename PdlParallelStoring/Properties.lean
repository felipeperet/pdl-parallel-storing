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
    have h_eq : s₁ ⋆ t₁ = s₂ ⋆ t₂ := by rw [← ht_eq, ht_eq₂]
    have s₁_eq_s₂ : s₁ = s₂ := (State.inject.mp h_eq).1
    rw [hs_eq, hu_eq]
    exact s₁_eq_s₂
  case mpr =>
    intro h_eq
    unfold Relation.Comp
    use s ⋆ s
    simp [P.s₁, P.r₁]
    use u
    rw [h_eq]

-- Property II) Rs₂ ; Rr₂ = Id
def s₂_comp_r₂ (F : Frame) [Structured F] [P : Proper F] :
    ∀ {s u}, Relation.Comp (F.R π.s₂) (F.R π.r₂) s u ↔ (s = u) := by
  intros s u
  constructor
  case mp =>
    intro hcomp
    unfold Relation.Comp at hcomp
    obtain ⟨t, hs₂, hr₂⟩ := hcomp
    rw [P.s₂] at hs₂
    rw [P.r₂] at hr₂
    obtain ⟨s₁, t₁, hs_eq, ht_eq⟩ := hs₂
    obtain ⟨s₂, t₂, ht_eq₂, hu_eq⟩ := hr₂
    have h_eq : s₁ ⋆ t₁ = s₂ ⋆ t₂ := by rw [← ht_eq, ht_eq₂]
    have t₁_eq_t₂ : t₁ = t₂ := (State.inject.mp h_eq).2
    rw [hs_eq, hu_eq]
    exact t₁_eq_t₂
  case mpr =>
    intro h_eq
    unfold Relation.Comp
    use s ⋆ s
    simp [P.s₂, P.r₂]
    constructor <;> use u <;> rw [h_eq]
