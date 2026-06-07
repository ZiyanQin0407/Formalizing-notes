import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open Set Filter

variable {X : Type*}

/- 定义：给定每个点 x 的一个滤子 G_x（包含于主滤子 {x} 中），
   定义 F 为所有满足“对任意 x ∈ U，有 U ∈ G_x”的集合 U 的集合 -/
def 𝒢 (G : X → Filter X) (hG : ∀ x, G x ≤ 𝓟 {x}) :=
  {U : Set X | ∀ x ∈ U, U ∈ G x}

/- 定理 -/
theorem topology_from_filters
    (G : X → Filter X)
    (hG : ∀ x, G x ≤ 𝓟 {x}) :  -- 每个 G_x 包含于 {x} 的主滤子
    let ℱ := 𝒢 G hG
    (∅ ∈ ℱ ∧ univ ∈ ℱ) ∧
    (∀ U V, U ∈ ℱ → V ∈ ℱ → U ∩ V ∈ ℱ) ∧
    (∀ {I : Type} (U : I → Set X), (∀ i, U i ∈ ℱ) → ⋃ i, U i ∈ ℱ) ∧
    ∀ x, let Bx := {U ∈ ℱ | x ∈ U}
         (∀ U ∈ Bx , U ∈ G x) ∧ Filter.IsBasis Bx (G x) ∧
         (∀ U ∈ G x, ∃ V ∈ G x, V ⊆ U ∧ ∀ y ∈ V, V ∈ G y) → (G x = (Bx).filter)
:= by
  intro ℱ
  have mem_ℱ_iff : ∀ U, U ∈ ℱ ↔ ∀ x ∈ U, U ∈ G x := by
    intro U
    rfl

  -- (1) ∅ ∈ ℱ 且 X ∈ ℱ
  have h₁ : ∅ ∈ ℱ ∧ univ ∈ ℱ := by
    constructor
    · rw [mem_ℱ_iff]
      intro x hx
      exfalso; exact Set.not_mem_empty x hx
    · rw [mem_ℱ_iff]
      intro x hx
      have := hG x
      simp only [le_principal_iff, Set.mem_singleton_iff] at this
      exact this rfl

  -- (2) 交集封闭性
  have h₂ : ∀ U V, U ∈ ℱ → V ∈ ℱ → U ∩ V ∈ ℱ := by
    intro U V hU hV
    rw [mem_ℱ_iff] at *
    intro x hx
    have hxU : x ∈ U := hx.1
    have hxV : x ∈ V := hx.2
    specialize hU x hxU
    specialize hV x hxV
    exact inter_mem hU hV

  -- (3) 并集封闭性
  have h₃ : ∀ {I : Type} (U : I → Set X), (∀ i, U i ∈ ℱ) → ⋃ i, U i ∈ ℱ := by
    intro I U hU
    rw [mem_ℱ_iff]
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have := hU i
    rw [mem_ℱ_iff] at this
    have := this x hi
    exact mem_of_superset this (subset_iUnion U i)

  -- 现在证明关于 Bx 的性质
  have hBx : ∀ x, let Bx := {U ∈ ℱ | x ∈ U}
       (∀ U ∈ Bx, U ∈ G x) ∧ Filter.IsBasis Bx (G x) := by
    intro x
    let Bx := {U ∈ ℱ | x ∈ U}
    constructor
    · -- Bx ⊆ G x
      intro U hU
      obtain ⟨hU_ℱ, hx⟩ := hU
      rw [mem_ℱ_iff] at hU_ℱ
      exact hU_ℱ x hx
    · -- Filter.IsBasis Bx (G x)
      refine ⟨⟨univ, ?_⟩, ?_⟩
      · show univ ∈ Bx
        constructor
        · rw [mem_ℱ_iff]; intro y hy; exact hG y (mem_principal_self univ)
        · exact mem_univ x
      · intro U V hU hV
        obtain ⟨hU_ℱ, hxU⟩ := hU
        obtain ⟨hV_ℱ, hxV⟩ := hV
        refine ⟨U ∩ V, ⟨h₂ U V hU_ℱ hV_ℱ, ⟨hxU, hxV⟩⟩, ?_, ?_⟩
        · exact inter_subset_left U V
        · exact inter_subset_right U V

  -- 条件成立时 G_x = Filter.ofBasis Bx
  have h_cond : ∀ x,
      (∀ U ∈ G x, ∃ V ∈ G x, V ⊆ U ∧ ∀ y ∈ V, V ∈ G y) →
      G x = Filter.ofBasis {U ∈ ℱ | x ∈ U} id := by
    intro x cond
    apply Filter.ext
    intro U
    constructor
    · -- 如果 U ∈ G x，则 U ∈ filter of Bx
      intro hU
      obtain ⟨V, hV_G, hVU, hV_prop⟩ := cond U hU
      -- 需要证明 V ∈ Bx
      have hV_ℱ : V ∈ ℱ := by
        rw [mem_ℱ_iff]
        intro y hy
        exact hV_prop y hy
      have hxV : x ∈ V := by
        have := hG x
        simp [le_principal_iff] at this
        exact this hV_G
      let Bx := {W ∈ ℱ | x ∈ W}
      have hV_Bx : V ∈ Bx := ⟨hV_ℱ, hxV⟩
      exact Filter.mem_of_superset (Filter.ofBasis_mem_iff.mpr ⟨V, hV_Bx, rfl.subset⟩) hVU
    · -- 如果 U ∈ filter of Bx，则 U ∈ G x
      intro hU
      simp only [Filter.ofBasis, Filter.mem_mk, mem_setOf_eq, id.def] at hU
      obtain ⟨V, ⟨hV_ℱ, hxV⟩, hVU⟩ := hU
      rw [mem_ℱ_iff] at hV_ℱ
      exact mem_of_superset (hV_ℱ x hxV) hVU

  exact ⟨h₁, h₂, h₃, λ x, ⟨(hBx x).1, (hBx x).2, h_cond x⟩⟩

/-有待解决的错误qwq-/
