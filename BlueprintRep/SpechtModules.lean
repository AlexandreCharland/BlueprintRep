import BlueprintRep.Young
import Mathlib.Algebra.MonoidAlgebra.Defs --Utilisé pour MonoidAlgebra
import Mathlib.Data.Complex.Basic --Utilisé pour ℂ

def IneqYoungDiagram (μ1 : YoungDiagram) (μ2 : YoungDiagram) :=
  ∃ i : ℕ, (μ1.colLen i) > (μ2.colLen i) ∧ (∀ j : ℕ, (μ1.colLen j) = (μ2.colLen j))

def PermComplex (n : ℕ) := MonoidAlgebra ℂ (Equiv.Perm (Fin n))
