import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.GroupTheory.Perm.Basic

structure YoungTableau (μ : YoungDiagram) where
  entry : ℕ → ℕ → ℕ
  card' := μ.card
  injEntry' : ∀ {i1 j1 i2 j2}, (i1, j1) ∈ μ ∧ (i2, j2) ∈ μ → entry i1 j1 ≠ entry i2 j2
  zeros' : ∀ {i j}, (i, j) ∉ μ → entry i j = 0

--J'ai copié de Mathlib.Combinatorics.Young.SemistandardTableau
--et modifier pour ce que j'ai besoin

instance instFunLike {μ : YoungDiagram} : FunLike (YoungTableau μ) ℕ (ℕ → ℕ) where
  coe := YoungTableau.entry
  coe_injective' T T' h := by
    cases T
    cases T'
    congr
    sorry

-- Aucune idée à quoi il peuvent servir

/-theorem to_fun_eq_coe {μ : YoungDiagram} {T : YoungTableau μ} :
    T.entry = (T : ℕ → ℕ → ℕ) :=
  rfl-/

/-theorem ext {μ : YoungDiagram} {T T' : YoungTableau μ} (h : ∀ i j, T i j = T' i j) :
    T = T' :=
  DFunLike.ext T T' fun _ ↦ by
    funext
    apply h-/

/-protected def copy {μ : YoungDiagram} (T : YoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : YoungTableau μ where
  entry := entry'
  injEntry' := h.symm ▸ T.injEntry'
  zeros' := h.symm ▸ T.zeros'-/

/-theorem coe_copy {μ : YoungDiagram} (T : YoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : ⇑(T.copy entry' h) = entry' :=
  rfl-/

/-theorem copy_eq {μ : YoungDiagram} (T : YoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : T.copy entry' h = T :=
  DFunLike.ext' h-/

theorem injEntry {μ : YoungDiagram} (T : YoungTableau μ) {i1 i2 j1 j2 : ℕ}
    (h1 : (i1, j1) ∈ μ) (h2 : (i2, j2) ∈ μ) : T i1 j1 ≠ T i2 j2 :=
  T.injEntry' ⟨h1 , h2⟩

theorem zeros {μ : YoungDiagram} (T : YoungTableau μ) {i j : ℕ}
    (not_cell : (i, j) ∉ μ) : T i j = 0 :=
  T.zeros' not_cell

namespace YoungProjector

--structure PLambda (μ : YoungDiagram) ( p : YoungTableau μ) : Subgroup (Perm p.card):=
  --elem : Group (Perm α)

end YoungProjector
