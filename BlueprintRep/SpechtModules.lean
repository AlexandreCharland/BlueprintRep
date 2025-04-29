import BlueprintRep.Young
import Mathlib.Algebra.MonoidAlgebra.Basic --Utilisé pour MonoidAlgebra
import Mathlib.Data.Complex.Basic --Utilisé pour ℂ
import Mathlib.GroupTheory.Perm.Sign --Utilisé pour sign

/-! Définition d'une inégalité entre YoungDiagram -/
def IneqYoungDiagram (μ1 : YoungDiagram) (μ2 : YoungDiagram) :=
  ∃ i : ℕ, (μ1.colLen i) > (μ2.colLen i) ∧ (∀ j : ℕ, (μ1.colLen j) = (μ2.colLen j))

/-! Définition de notre groupe anneau -/
def PermComplex (μ : YoungDiagram) := MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))

/-! Nécessaire pour indiqué que l'ensemble des éléments de Pᵤ est fini -/
noncomputable instance PuElementFinite {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Fintype (Pu Yᵤ).carrier := Fintype.ofFinite ↑(Pu Yᵤ).carrier

/-! Nécessaire pour indiqué que l'ensemble des éléments de Qᵤ est fini -/
noncomputable instance QuElementFinite {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Fintype (Qu Yᵤ).carrier := Fintype.ofFinite ↑(Qu Yᵤ).carrier

/-! Nécessaire pour utilisé Finset.sum -/
noncomputable instance Addition (μ : YoungDiagram) : AddCommMonoid (PermComplex μ) :=
  MonoidAlgebra.addCommMonoid ℂ (Equiv.Perm (Fin μ.card))

/-! Nécessaire pour multiplier deux éléments -/
noncomputable instance Multiplication (μ : YoungDiagram) : Mul (PermComplex μ) :=
  ⟨fun a b => MonoidAlgebra.mul' a b⟩

/-! Définition de aᵤ -/
noncomputable def au {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : PermComplex μ :=
  Finset.sum ((Pu Yᵤ).carrier.toFinset) (fun σ => MonoidAlgebra.single σ ((↑1 / ↑(PuCard Yᵤ)) : ℂ))

/-! Définition de bᵤ -/
noncomputable def bu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : PermComplex μ :=
  Finset.sum ((Qu Yᵤ).carrier.toFinset) (fun σ => MonoidAlgebra.single σ ((↑(Equiv.Perm.sign σ)  / ↑(PuCard Yᵤ)) : ℂ))

/-! Définition de cᵤ -/
noncomputable def cu {μ : YoungDiagram} (Yᵤ :  YoungTableau μ) : PermComplex μ :=
  (au Yᵤ) * (bu Yᵤ)

--SpechtModules TODO

/-
lemma LinearTransformation {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  ∀x : (PermComplex μ), ∃ y : (PermComplex μ), (au Yᵤ) * x * (bu Yᵤ) = y * (cu Yᵤ) := by
  sorry --TODO
-/

--SmallerImpZero TODO

/-! Meilleure solution trouvé au problème suivant.
Lean ne me laisse pas multiplier un MonoidAlgebra.single avec un MonoidAlgebra -/
noncomputable def ComplexToComplexPerm (μ : YoungDiagram) (c : ℂ) : PermComplex μ :=
  Finset.sum {1} (fun σ => MonoidAlgebra.single σ c)

/-
lemma CuPropIdempotent {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  ∃ c : ℂ, (cu Yᵤ) * (cu Yᵤ) = (ComplexToComplexPerm μ c) * (cu Yᵤ) := by
  sorry --TODO
-/

--IrreductibleRepresentationSn TODO
