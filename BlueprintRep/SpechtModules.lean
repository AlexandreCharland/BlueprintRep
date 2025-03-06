import BlueprintRep.Young
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Complex.Basic

def IneqYoungDiagram (μ1 : YoungDiagram) (μ2 : YoungDiagram) :=
  ∃ i : ℕ, (μ1.colLen i) > (μ2.colLen i) ∧ (∀ j : ℕ, (μ1.colLen j) = (μ2.colLen j))
