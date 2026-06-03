import Mathlib

variable (α : Type) (s t u : Set α)

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  · intro h
    exact h.left
  · intro h
    constructor
    · exact h
    · left
      exact h

example : s ∪ s ∩ t = s := by
  ext x
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact h.left
  · intro h
    left
    exact h

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  · intro h
    rcases h with h | h
    · left
      exact h.left
    · right
      exact h
  · intro h
    rcases h with h | h
    · by_cases h' : x ∈ t
      · right
        exact h'
      · left
        exact ⟨h, h'⟩
    · right
      exact h

example (h : s ⊆ t) : s \ u ⊆ t \ u := by
  intro x hsu
  constructor
  · apply h
    exact hsu.left
  · exact hsu.right

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  · intro h
    rcases h with h | h
    · constructor
      · left
        exact h.left
      · intro h'
        apply h.right
        exact h'.right
    · constructor
      · right
        exact h.left
      · intro h'
        apply h.right
        exact h'.left
  · intro h
    rcases h with ⟨hs | ht, hst⟩
    · left
      constructor
      · exact hs
      · intro ht
        apply hst
        exact ⟨hs, ht⟩
    · right
      constructor
      · exact ht
      · intro hs
        apply hst
        exact ⟨hs, ht⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x h
  rcases h with ⟨hs, ht⟩ | ⟨hs, hu⟩
  · constructor
    · exact hs
    · left
      exact ht
  · constructor
    · exact hs
    · right
      exact hu

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  intro x h
  rcases h with ⟨hs, htu⟩
  constructor
  · constructor
    · exact hs
    · intro ht
      apply htu
      left
      exact ht
  · intro hu
    apply htu
    right
    exact hu

variable (β : Type) (f : α → β) (v : Set β)
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x hx
    apply h
    use x
  · intro h x hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [← hxy]
    apply h
    exact hy
