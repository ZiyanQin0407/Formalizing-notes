import Mathlib
def curry {α β γ : Type} : (α × β → γ) → (α → β → γ) :=
  fun f a b => f (a, b)
def uncurry {α β γ : Type} : (α → β → γ) → (α × β → γ) :=
  fun g ⟨a, b⟩ => g a b
example (f : α × β → γ) : uncurry (curry f) = f := by
  funext ⟨a, b⟩
  show uncurry (curry f) (a, b) = f (a, b)
  simp [uncurry, curry]
/-发现集合论中的Currying Isomorphism和模论中的Adjoint Isomorphism似乎有某种联系-/
variable (R M N P : Type*)
variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]
-- 给定一个双线性映射 f，把它转化为一个柯里化映射 (m ↦ (n ↦ f m n))
def forwardMap (f : M →ₗ[R] N →ₗ[R] P) : M →ₗ[R] (N →ₗ[R] P) :=
  { toFun := fun m =>
      { toFun := fun n => f m n
        map_add' := fun n1 n2 => by
          rw [LinearMap.map_add]
        map_smul' := fun r n => by
          rw [LinearMap.map_smul]
          trivial }
    map_add' := fun m1 m2 => by
      ext n
      simp only [LinearMap.add_apply]
      sorry
    map_smul' := fun r m => by
      ext n
      simp only [LinearMap.smul_apply]
      sorry}
-- 给定一个柯里化映射 g，把它还原为一个完整的双线性映射
def backwardMap (g : M →ₗ[R] (N →ₗ[R] P)) : M →ₗ[R] N →ₗ[R] P :=
  { toFun := fun m =>
      { toFun := fun n => g m n
        map_add' := fun n1 n2 => by
          rw [LinearMap.map_add]
        map_smul' := fun r n => by
          rw [LinearMap.map_smul]
          trivial}
    map_add' := fun m1 m2 => by
      ext n
      simp only [LinearMap.add_apply]
      sorry
    map_smul' := fun r m => by
      ext n
      simp only [LinearMap.smul_apply]
      sorry}
-- 证明先 forward 再 backward 仍为原映射
lemma forward_backward_id (g : M →ₗ[R] (N →ₗ[R] P)) :
    forwardMap R M N P (backwardMap R M N P g) = g := by
  ext m n
  dsimp [forwardMap, backwardMap]
-- 证明先 backward 再 forward 仍为原映射
lemma backward_forward_id (f : M →ₗ[R] N →ₗ[R] P) :
    backwardMap R M N P (forwardMap R M N P f) = f := by
  ext m n
  dsimp [forwardMap, backwardMap]
def AdjointIso: (M →ₗ[R] N →ₗ[R] P) ≃ₗ[R] (M →ₗ[R] (N →ₗ[R] P)) :=
  { toFun := forwardMap R M N P
    invFun := backwardMap R M N P
    left_inv := backward_forward_id R M N P
    right_inv := forward_backward_id R M N P
    map_add' := fun f1 f2 => by sorry
    map_smul' := fun r f => by sorry }
/-有待补充的细节-/
