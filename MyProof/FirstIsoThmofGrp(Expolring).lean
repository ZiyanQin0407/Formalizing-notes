import Mathlib
open Group

/- 定义 -/
variable {G H : Type} [Group G] [Group H] (φ : G →* H)

/- 定理 -/
theorem first_isomorphism_thm : (G ⧸ ker φ) ≃* φ.range := by
  let f : G ⧸ ker φ → φ.range :=
    QuotientGroup.lift (ker φ) (φ.codRestrict φ.range (fun _ => ⟨_, rfl⟩))
    (by
      intro g h h_in_ker
      simp only [ker, MonoidHom.mem_ker] at h_in_ker
      apply Subtype.ext
      rw [MonoidHom.codRestrict_apply, MonoidHom.codRestrict_apply]
      dsimp [φ] at *
      rw [← φ.map_mul, ← φ.map_mul, mul_assoc, mul_inv_cancel_left]
      simp [h_in_ker]
    )

  /- hom -/
  have f_mul : ∀ x y, f (x * y) = f x * f y := by
    rintro ⟨x⟩ ⟨y⟩
    simp only [f, QuotientGroup.lift_mk, MonoidHom.codRestrict_apply, Subtype.ext_iff, coe_mul]
    rfl

  refine MonoidHom.ofBijective (⟨f, f_mul⟩ : (G ⧸ ker φ) →* φ.range) ?_
  constructor
  /- inj -/
  · rw [MonoidHom.injective_iff]
    intro x hx
    obtain ⟨g, hg⟩ := QuotientGroup.out_eq x
    rw [← hg] at hx ⊢
    simp only [f, QuotientGroup.lift_mk, MonoidHom.codRestrict_apply, Subtype.mk_eq_mk, Subtype.ext_iff] at hx
    change φ g = 1 at hx
    rw [MonoidHom.mem_ker] at hx
    exact QuotientGroup.eq_one_iff.mpr hx
  /- surj -/
  · rintro ⟨h, h_in_range⟩
    obtain ⟨g, rfl⟩ := h_in_range
    exact ⟨g, by simp [f]⟩


/-有待解决的错误qwq-/
