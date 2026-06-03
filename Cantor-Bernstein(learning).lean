import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Tactic.ApplyFun

def C {α β : Type} (f : α → β) (g : β → α) (k : ℕ) : Set α :=
  match k with
  | 0 => {x | x ∉ Set.range g}
  | k + 1 => g '' (f '' (C f g k))

lemma inv_g {α β : Type} {f : α → β} {g : β → α}
{a : α} (ha : ¬ ∃ n : ℕ, a ∈ C f g n) :
∃ y, g y = a := by
   push_neg at ha
  have ha := ha 0
  simp [C] at ha
  exact ha

noncomputable def h {α β : Type} (f : α → β) (g : β → α) : α → β := by
  intro a
  by_cases hn: ∃ n : ℕ, a ∈ C f g n
  · exact f a
  · exact (inv_g hn).choose  --lean不清楚我们取出集合中元素的操作（noncomputable，且所有使用此定义的地方都noncomputable），要用.choose
lemma hinj {α β : Type} {f : α → β} (hf : Function.Injective f) {g : β → α} :
Function.Injective (h f g) := by
  intro x y hxy
  by_cases h₁ : ∃ n : ℕ, x ∈ C f g n
  · by_cases h₂ : ∃ n : ℕ, y ∈ C f g n
    · simp [h, dif_pos h₁, dif_pos h₂] at hxy--dif:dependent if_then_else
      exact hf hxy
    · simp [h, dif_pos h₁, dif_neg h₂] at hxy
      rcases h₁ with ⟨n, hx⟩
      have : ∃ m, y ∈ C f g m := by
        use n + 1
        simp only [C,Set.mem_image,exists_exists_and_eq_and]
        use x
        constructor
        · exact hx
        · rw[hxy]
          exact (inv_g h₂).choose_spec
          /- h:∃ x:α,P x
          #check h.choose      --h.choose:α
          #check h.choose_spec      --h.choose_spec:P(h.choose)
          -/
      exact False.elim <| h₂ this
  · by_cases h₂ : ∃ n : ℕ, y ∈ C f g n
    · simp [h, dif_pos h₂, dif_neg h₁] at hxy
      rcases h₂ with ⟨n, hx⟩
      have : ∃ m, x ∈ C f g m := by
        use n + 1
        simp [C]
        exact ⟨y, ⟨hx, hxy ▸ (inv_g h₁).choose_spec⟩⟩
      exact False.elim <| h₁ this
    · simp [h, dif_neg h₂,dif_neg h₁] at hxy
      rw [← (inv_g h₁).choose_spec, ← (inv_g h₂).choose_spec, hxy]

lemma hsurj {α β : Type} {f : α → β} {g : β → α} (hg : Function.Injective g) :
Function.Surjective (h f g) := by
  intro b
  by_cases hb : ∃ n, g b ∈ C f g n
  · rcases hb with ⟨n, hn⟩
    by_cases hn' : n = 0
    · simp [hn', C] at hn
      exact False.elim <| (hn b) rfl
    · rw [← Nat.succ_pred_eq_of_ne_zero hn'] at hn
      simp [C] at hn
      rcases hn with ⟨a, ha⟩
      use a
      unfold h
      rw [dif_pos ⟨n - 1, ha.1⟩]
      exact hg ha.2
  · use g b
    apply_fun g
    simp [h, dif_neg hb, (inv_g hb).choose_spec]

theorem CantorBernstein {α β : Type} {f : α → β} (hf : Function.Injective f) {g : β → α} (hg : Function.Injective g) :
∃ h : α → β, Function.Bijective h := by
  use (h f g)
  exact ⟨hinj hf, hsurj hg⟩
