import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs

structure YoungTableau (μ : YoungDiagram) where
  entry : μ.cells → (Fin μ.card)
  inj : ∀ {i j : μ.cells}, entry i = entry j → i = j

lemma injYu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Function.Injective Yᵤ.entry := by
  rw [Function.Injective]
  intros _ _ h
  exact Yᵤ.inj h

theorem bijYu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Function.Bijective Yᵤ.entry := by
  rw[Fintype.bijective_iff_injective_and_card]
  simp
  exact injYu Yᵤ

/-
def S (μ : YoungDiagram) (T : YoungTableau μ) : Set (Equiv.Perm (Fin μ.card)) :=
  {x : (Equiv.Perm (Fin μ.card)) | ∀ {i1 i2 j1 j2}, (((i1, j1) ∈ μ) ∧ ((i2, j2) ∈ μ)) → (x (T.entry i1 j1) ≠ T.entry i2 j2 ↔ i1 = i2)}

def PLambda (μ : YoungDiagram) (T : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) where
  carrier := {x : (Equiv.Perm (Fin μ.card)) | ∀ {i1 i2 j1 j2}, (((i1, j1) ∈ μ) ∧ ((i2, j2) ∈ μ)) → (x (T.entry i1 j1) ≠ T.entry i2 j2 ↔ i1 = i2)}
  mul_mem :=
-/
