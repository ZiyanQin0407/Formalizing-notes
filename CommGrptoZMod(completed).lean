import Mathlib.Algebra.Group.Basic
variable (M : Type*) [AddCommGroup M]
structure MyZModule where
  smul : ℤ → M → M
  one_smul : ∀ m : M, smul 1 m = m
  mul_smul : ∀ (n k : ℤ) (m : M), smul (n * k) m = smul n (smul k m)
  smul_add : ∀ (n : ℤ) (m1 m2 : M), smul n (m1 + m2) = smul n m1 + smul n m2
  add_smul : ∀ (n k : ℤ) (m : M), smul (n + k) m = smul n m + smul k m
def abelianGroupAsZModule : MyZModule M :=
  { smul := fun n m => n • m
    one_smul := fun m => by
      simp
    mul_smul := fun n k m => by
      rw [mul_zsmul]
    smul_add := fun n m1 m2 => by
      rw [zsmul_add]
    add_smul := fun n k m => by
      rw [add_zsmul]}
