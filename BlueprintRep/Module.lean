import Mathlib.Algebra.Module.Hom --Homomorphisme de module

/-! Montre que Ae est un AddCommMonoid -/
instance Ae' (A : Type) [Ring A] (e : A) : AddCommMonoid {a' : A | ∃ a : A, a'= a * e} where
  add := fun a b => ⟨a.1 + b.1, by
    obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    use (a' + b')
    rw [ha, hb, add_mul]⟩
  zero := ⟨0, by use 0; rw[zero_mul]⟩
  add_assoc := by
    intros _ _ _
    apply Subtype.ext
    apply add_assoc
  zero_add := by
    intro _
    apply Subtype.ext
    apply zero_add
  add_zero := by
    intro _
    apply Subtype.ext
    apply add_zero
  add_comm := by
    intro _ _
    apply Subtype.ext
    apply add_comm
  --Why do I need to do this?
  nsmul := fun n a => ⟨n • a.1, by
    obtain ⟨a', ha⟩ := a.2
    use n • a'
    rw [ha, smul_mul_assoc]⟩
  nsmul_zero := by
    intro a
    apply Subtype.ext
    simp [nsmul_zero]
    rfl
  nsmul_succ := by
    intro n a
    apply Subtype.ext
    simp
    rw[add_mul, one_mul]
    rfl

/-! Définit Ae comme un A-module -/
def Ae (A : Type) [Ring A] (e : A) : Module A {a' : A | ∃ a : A, a'= a * e} where
  smul := fun r a => ⟨r * a.1, by
    obtain ⟨a', ha⟩ := a.2
    use r * a'
    rw [ha, mul_assoc]⟩
  one_smul := by
    intro a
    apply Subtype.ext
    apply one_mul
  mul_smul := by
    intros r s a
    apply Subtype.ext
    apply mul_assoc
  smul_zero := by
    intro r
    apply Subtype.ext
    apply mul_zero
  smul_add := by
    intros r a b
    apply Subtype.ext
    apply mul_add
  add_smul := by
    intros r s a
    apply Subtype.ext
    apply add_mul
  zero_smul := by
    intro a
    apply Subtype.ext
    apply zero_mul

-- (1er théorème isomorphisme)
--Mathlib.RingTheory.Ideal.Quotient.Operations
--quotientKerEquivOfSujective
--Probablement pas utile pour les modules, mais pourrait aider lors d'une recherche de mot clée

--HomAeM TODO

--HomAeMisoeM TODO
