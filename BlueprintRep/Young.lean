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

def Pu (μ : YoungDiagram) (Yᵤ : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) where
  carrier := {x : (Equiv.Perm (Fin μ.card)) | ∀ {i j : μ.cells}, (x (Yᵤ.entry i) = Yᵤ.entry j) → i.val.snd = j.val.snd}
  mul_mem' := by
    intros α β a b i j αβ
    rw[Equiv.Perm.coe_mul, Function.comp_apply] at αβ
    have h : ∃! (k : μ.cells), Yᵤ.entry k = β (Yᵤ.entry i) := by
      have h1 : ∀ (j' : Fin μ.card), ∃! i', Yᵤ.entry i' = j' := by
        rw[← Function.bijective_iff_existsUnique (Yᵤ.entry)]
        exact bijYu Yᵤ
      exact h1 (β (Yᵤ.entry i))
    obtain ⟨k, hk, _⟩ := h
    rw[Eq.comm] at hk
    have ik : i.val.snd = k.val.snd := by exact b hk
    rw[hk] at αβ
    have jk : k.val.snd = j.val.snd := by exact a αβ
    rw[ik,jk]
  one_mem' := by
    intros _ _ h
    rw[Equiv.Perm.coe_one, id_eq, Function.Injective.eq_iff] at h
    rw[h]
    exact injYu Yᵤ
  inv_mem' := by
    intros _ h1 _ _ h2
    rw[Eq.comm, Equiv.Perm.eq_inv_iff_eq] at h2
    rw[Eq.comm]
    exact h1 h2

def Qu (μ : YoungDiagram) (Yᵤ : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) where
  carrier := {x : (Equiv.Perm (Fin μ.card)) | ∀ {i j : μ.cells}, (x (Yᵤ.entry i) = Yᵤ.entry j) → i.val.fst = j.val.fst}
  mul_mem' := by
    intros α β a b i j αβ
    rw[Equiv.Perm.coe_mul, Function.comp_apply] at αβ
    have h : ∃! (k : μ.cells), Yᵤ.entry k = β (Yᵤ.entry i) := by
      have h1 : ∀ (j' : Fin μ.card), ∃! i', Yᵤ.entry i' = j' := by
        rw[← Function.bijective_iff_existsUnique (Yᵤ.entry)]
        exact bijYu Yᵤ
      exact h1 (β (Yᵤ.entry i))
    obtain ⟨k, hk, _⟩ := h
    rw[Eq.comm] at hk
    have ik : i.val.fst = k.val.fst := by exact b hk
    rw[hk] at αβ
    have jk : k.val.fst = j.val.fst := by exact a αβ
    rw[ik,jk]
  one_mem' := by
    intros _ _ h
    rw[Equiv.Perm.coe_one, id_eq, Function.Injective.eq_iff] at h
    rw[h]
    exact injYu Yᵤ
  inv_mem' := by
    intros _ h1 _ _ h2
    rw[Eq.comm, Equiv.Perm.eq_inv_iff_eq] at h2
    rw[Eq.comm]
    exact h1 h2
