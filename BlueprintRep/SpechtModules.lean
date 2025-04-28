import BlueprintRep.Young
import Mathlib.Algebra.MonoidAlgebra.Defs --Utilisé pour MonoidAlgebra
import Mathlib.Data.Complex.Basic --Utilisé pour ℂ
import Mathlib.GroupTheory.Perm.Sign --Utilisé pour sign

def IneqYoungDiagram (μ1 : YoungDiagram) (μ2 : YoungDiagram) :=
  ∃ i : ℕ, (μ1.colLen i) > (μ2.colLen i) ∧ (∀ j : ℕ, (μ1.colLen j) = (μ2.colLen j))

def PermComplex (μ : YoungDiagram) := MonoidAlgebra ℂ (Equiv.Perm (Fin μ.card))

noncomputable instance PuCardFinite' {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Fintype (Pu Yᵤ).carrier := Fintype.ofFinite ↑(Pu Yᵤ).carrier

noncomputable instance (μ : YoungDiagram) : AddCommMonoid (PermComplex μ) :=
  MonoidAlgebra.addCommMonoid ℂ (Equiv.Perm (Fin μ.card))

noncomputable instance (μ : YoungDiagram) : Mul (PermComplex μ) :=
  ⟨fun a b => MonoidAlgebra.mul' a b⟩

noncomputable def au {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : PermComplex μ :=
  Finset.sum ((Pu Yᵤ).carrier.toFinset) (fun σ => MonoidAlgebra.single σ ((↑1 / ↑(PuCard Yᵤ)) : ℂ) )

noncomputable def bu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : PermComplex μ :=
  Finset.sum ((Pu Yᵤ).carrier.toFinset) (fun σ => MonoidAlgebra.single σ ((↑(Equiv.Perm.sign σ)  / ↑(PuCard Yᵤ)) : ℂ) )

noncomputable def cu {μ : YoungDiagram} (Yᵤ :  YoungTableau μ) : PermComplex μ :=
  (au Yᵤ) * (bu Yᵤ)
