import Mathlib


section True_and_False

#check True
#check False
#check trivial --Same as True.intro


theorem example1 : True := by trivial

theorem example1' : True := True.intro

theorem example2 (P : Prop) (h : False) : P := by contradiction

theorem example2' (P : Prop) (h : False) : P := False.elim h

end True_and_False

section Implication

variable (P Q : Prop)

#check P → Q    -- P → Q : Prop

example (q : Q)  : P → Q := by
  intro x
  exact q

example (p : P) (h : P → Q) : Q := by
  apply h
  exact p


example (h : 3 < 5) (i : 3 < 5 → 2 < 3) : 2 < 3 := by
  apply i
  exact h

example (P Q R : Prop) (p : P) (h : Q → R) (j : P → Q) : R := by
  apply h
  apply j
  exact p


end Implication


section Not

variable (P : Prop)
#check ¬P   -- ¬P : Prop

example : (¬P) = (P → False) := rfl

def ex : Nat → Nat  := by
  intro x
  exact 2 * x


example (h : P → False) : ¬P := by
  intro p
  apply h
  exact p

example (p : P) (h : ¬P) : False := by
  contradiction

example (Q R : Prop) (p : P) (q : Q) (r : R) (h : ¬P) : 5 < 3 := by
  contradiction

example (p : 2 < 3) (q : 2 ≥ 3) : 5 < 3 := by contradiction
-- to print ≥ : \ge

-- import Mathlib at the beginning of the document
#check by_contradiction

example (p : ¬¬P) : P := by
  apply by_contradiction
  exact p

end Not


section Forall

-- to print ∀ : \forall
#check ∀ (n : Nat), n > 100
#check ∀ n : Nat, n > 100
#check ∀ n, n > 100
#check (n : Nat) → n > 100
#check 120 > 110 → 120 > 100
#check (n : Nat) → Nat


example (p : ∀ (n : Nat), n > 100) : 5 > 100 := by
  apply p

end Forall

section Exist

-- to print ∃ : \exist or \ex
example : ∃ (n : Nat), n > 100 := by
  use 120
  trivial

example (n m : Nat) (p : n > m) : ∃ (x : Nat), x > m := by sorry

-- to print ⟨ : \<
example (P : Prop) (h : ∃ (x : Nat), P) : P := by
  rcases h with ⟨w, p⟩
  exact p


example (n m : Nat) (h : m = n) (p : ∃(x : Nat), x > n) : ∃(x : Nat), x > m := by     sorry


end Exist


import Mathlib.Tactic

example : ∀ n : ℕ, n ≥ 0 := fun n ↦ Nat.zero_le n

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp,hq⟩

example (p q : Prop) (hpq : p → q) (hqp : q → p) : p ↔ q := ⟨hpq,hqp⟩

example (n : ℕ) : n ≥ 0 ∨ False := Or.inl (Nat.zero_le n)

example (n : ℕ) : n < 0 ∨ 1 = 1 := Or.inr rfl

example (p q r : Prop) (hpq : p ∧ q) (hr : r) : p ∧ r := ⟨hpq.1,hr⟩

example (p q : Prop) (h : p ↔ q) (hp : p) : q := h.1 hp

example (p q r : Prop) (hpq : p ∨ q) (h : q → r) : p ∨ r := by
  rcases hpq with hp | hq
  · left
    exact hp
  · right
    exact h hq

example {α : Type} (q : Prop) (p : α → Prop) (h₁ : ∃ a, p a) (h₂ : ∀ a, p a → q) : q := by
  rcases h₁ with ⟨a, pa⟩
  exact h₂ a pa

example (p q r s : Prop) (h₁ : p ∧ q ∧ r) (h₂ : r → s) : s := h₂ h₁.2.2

example (p q r : Prop) (h : q → r) : p ∨ q → p ∨ r := by
  intro x
  rcases x with x1 | x2
  · left
    exact x1
  · right
    exact h x2

example (p q : Prop) : ¬ (p ∨ q) ↔ (¬ p) ∧ (¬ q) := or_imp
