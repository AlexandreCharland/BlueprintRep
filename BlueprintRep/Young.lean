import Mathlib.Combinatorics.Young.YoungDiagram --Utilisé pour le YoungDiagram
import Mathlib.GroupTheory.Perm.Basic --Utilisé pour le groupe de permutation
import Mathlib.Algebra.Group.Subgroup.Defs --Utilisé pour les sous groupes
import Mathlib.Data.ZMod.Basic --Utilisé pour définir la cardinalité

structure YoungTableau (μ : YoungDiagram) where
  entry : μ.cells → (Fin μ.card)
  inj : ∀ {i j : μ.cells}, entry i = entry j → i = j

lemma injYu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Function.Injective Yᵤ.entry := by
  rw [Function.Injective]
  intros _ _ h
  exact Yᵤ.inj h

lemma bijYu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Function.Bijective Yᵤ.entry := by
  rw[Fintype.bijective_iff_injective_and_card]
  simp
  exact injYu Yᵤ

lemma preImYu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) (n : Fin μ.card) :
  ∃! (i : μ.cells), Yᵤ.entry i = n := by
  have h : ∀ (j' : Fin μ.card), ∃! i', Yᵤ.entry i' = j' := by
    rw[← Function.bijective_iff_existsUnique _]
    exact (bijYu Yᵤ)
  exact h n

def Pu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) where
  carrier := {x : (Equiv.Perm (Fin μ.card)) | ∀ {i j : μ}, (x (Yᵤ.entry i) = Yᵤ.entry j) → i.val.snd = j.val.snd}
  mul_mem' := by
    intros α β a b i j αβ
    rw[Equiv.Perm.coe_mul, Function.comp_apply] at αβ
    obtain ⟨k, hk, _⟩ := preImYu Yᵤ (β (Yᵤ.entry i))
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

noncomputable instance PuCardFinite {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : Fintype ↥(Pu Yᵤ) := by
  exact Fintype.ofFinite ↥(Pu Yᵤ)

noncomputable def PuCard {μ : YoungDiagram} (Yᵤ : YoungTableau μ) := Fintype.card ↥(Pu Yᵤ)

def Qu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) where
  carrier := {x : (Equiv.Perm (Fin μ.card)) | ∀ {i j : μ}, (x (Yᵤ.entry i) = Yᵤ.entry j) → i.val.fst = j.val.fst}
  mul_mem' := by
    intros α β a b i j αβ
    rw[Equiv.Perm.coe_mul, Function.comp_apply] at αβ
    obtain ⟨k, hk, _⟩ := preImYu Yᵤ (β (Yᵤ.entry i))
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

noncomputable instance QuCardFinite {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : Fintype ↥(Qu Yᵤ) := by
  exact Fintype.ofFinite ↥(Qu Yᵤ)

noncomputable def QuCard {μ : YoungDiagram} (Yᵤ : YoungTableau μ) := Fintype.card ↥(Qu Yᵤ)

lemma sectPuQu {μ : YoungDiagram} (Yᵤ : YoungTableau μ):
  (Pu Yᵤ).carrier ∩ (Qu Yᵤ).carrier = {↑1} := by
  rw[Set.eq_singleton_iff_unique_mem, Set.mem_inter_iff]
  constructor
  exact ⟨Subgroup.one_mem (Pu Yᵤ), Subgroup.one_mem (Qu Yᵤ)⟩
  simp
  intro f p q
  rw[Equiv.Perm.ext_iff]
  intro x
  obtain ⟨j, hj, a⟩ := preImYu Yᵤ x
  obtain ⟨k, hk, b⟩ := preImYu Yᵤ (f (Yᵤ.entry j))
  rw[Eq.comm] at hk
  rw[Pu] at p
  rw[Qu] at q
  have h : (j: μ) = (k : μ) := by
    ext
    exact q hk
    exact p hk
  rw[← h] at hk
  rw[Equiv.Perm.coe_one, id_eq, ← hj, hk]

def PuQu (μ : YoungDiagram) (Yᵤ : YoungTableau μ) := {g : (Equiv.Perm (Fin μ.card)) | ∃ p ∈ (Pu Yᵤ), ∃ q ∈ (Qu Yᵤ), g = p ∘ q}

structure Gu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) where
  g : (Fin μ.card) → (Fin μ.card)
  inj : ∀ {i j : (Fin μ.card)}, g i = g j → i = j
  rowToCol : ∀ {i j k l : μ}, ((i ≠ j) ∧ (g (Yᵤ.entry i) = (Yᵤ.entry k)) ∧ (g (Yᵤ.entry j) = (Yᵤ.entry l))) → ((i.val.fst ≠ j.val.fst) ∨ (k.val.snd ≠ l.val.snd))

lemma injGu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) :
  Function.Injective Gᵤ.g := by
  rw [Function.Injective]
  intros _ _ h
  exact Gᵤ.inj h

lemma bijGu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) :
  Function.Bijective Gᵤ.g := by
  rw[Fintype.bijective_iff_injective_and_card]
  simp
  exact injGu Gᵤ

lemma preImGu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) (n : Fin μ.card) :
  ∃! (i : μ.cells), Gᵤ.g (Yᵤ.entry i) = n := by
  have h : ∀ (j' : Fin μ.card), ∃! i', Gᵤ.g (Yᵤ.entry i') = j' := by
    rw[← Function.bijective_iff_existsUnique _]
    exact Function.Bijective.comp (bijGu Gᵤ) (bijYu Yᵤ)
  exact h n

lemma preImGu' {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) (n : Fin μ.card) :
  ∃! (i : Fin μ.card), Gᵤ.g i = n := by
  have h : ∀ (j' : Fin μ.card), ∃! i', Gᵤ.g i' = j' := by
    rw[← Function.bijective_iff_existsUnique _]
    exact (bijGu Gᵤ)
  exact h n

structure YuInv {μ : YoungDiagram} (Yᵤ : YoungTableau μ) where
  entry : (Fin μ.card) → μ.cells
  inv : ∀ {i : μ.cells}, entry (Yᵤ.entry i) = i
  inv' : ∀ {n : (Fin μ.card)}, Yᵤ.entry (entry n) = n

lemma bijYuInv {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (YᵤInv : YuInv Yᵤ) :
  Function.Bijective YᵤInv.entry := by
  rw[Function.bijective_iff_has_inverse]
  exists Yᵤ.entry
  rw[Function.leftInverse_iff_comp, Function.rightInverse_iff_comp, funext_iff, funext_iff]
  constructor
  intro _
  rw[Function.comp_apply, YᵤInv.inv', id_eq]
  intro _
  rw[Function.comp_apply, YᵤInv.inv, id_eq]

lemma preImYuInv {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (YᵤInv : YuInv Yᵤ) (i : μ) :
  ∃! (n : Fin μ.card), YᵤInv.entry n = i := by
  have h : ∀ (i' : μ), ∃! n', YᵤInv.entry n' = i' := by
    rw[← Function.bijective_iff_existsUnique _]
    exact (bijYuInv YᵤInv)
  exact h i

lemma staysInY {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) {YᵤInv : YuInv Yᵤ} (n : Fin μ.card) :
  ((YᵤInv.entry n).val.fst, ((YᵤInv.entry) (Gᵤ.g n)).val.snd) ∈ μ := by
  --Aucune idée pourquoi c'est vrai, autre que ça doit l'être sinon la preuve fonctionne pas
  sorry

def qu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) (YᵤInv : YuInv Yᵤ) (n : Fin μ.card) := Yᵤ.entry ⟨((YᵤInv.entry n).val.fst, (YᵤInv.entry (Gᵤ.g n)).val.snd), staysInY Gᵤ n⟩

lemma bijqu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) {YᵤInv : YuInv Yᵤ} :
  Function.Bijective (qu Gᵤ YᵤInv) := by
  rw [Fintype.bijective_iff_injective_and_card, Function.Injective]
  by_contra contra
  simp only [not_forall, and_true] at contra
  obtain ⟨a, b, h, contra⟩:= contra
  obtain ⟨a', ha, _⟩:= preImYu Yᵤ a
  obtain ⟨b', hb, _⟩:= preImYu Yᵤ b
  rw [← ha, ← hb, Function.Injective.eq_iff, ← ne_eq] at contra
  rw[qu, qu, Function.Injective.eq_iff, ← ha, ← hb] at h
  simp only [YᵤInv.inv, YᵤInv.inv, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨hx, hy⟩:=h
  obtain ⟨a'', ha', _⟩:= preImYu Yᵤ (Gᵤ.g (Yᵤ.entry a'))
  obtain ⟨b'', hb', _⟩:= preImYu Yᵤ (Gᵤ.g (Yᵤ.entry b'))
  rw[eq_comm] at ha'
  rw[eq_comm] at hb'
  rw[ha', hb'] at hy
  simp only [YᵤInv.inv, YᵤInv.inv] at hy
  have k : ((a'.val.fst ≠ b'.val.fst) ∨ (a''.val.snd ≠ b''.val.snd)) := by exact Gᵤ.rowToCol ⟨ contra, ha', hb'⟩
  rw[hx, hy] at k
  simp only [ne_eq, not_true_eq_false, or_self] at k
  exact injYu Yᵤ
  exact injYu Yᵤ

lemma quPerm' {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {Gᵤ : Gu Yᵤ} {YᵤInv : YuInv Yᵤ} :
  ∃ (perm : Equiv.Perm (Fin μ.card)), ∀ n, perm n = qu Gᵤ YᵤInv n := by
  have l : Function.Bijective (qu Gᵤ YᵤInv) := bijqu Gᵤ
  rw[Function.bijective_iff_has_inverse] at l
  obtain ⟨a, b, c⟩ := l
  use Equiv.mk (qu Gᵤ YᵤInv) a b c
  intro n
  rfl

noncomputable def quPerm {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) (YᵤInv : YuInv Yᵤ) : (Equiv.Perm (Fin μ.card)) := by
  exact Equiv.ofBijective (qu Gᵤ YᵤInv) (bijqu Gᵤ)

lemma qu_in_Qu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (Gᵤ : Gu Yᵤ) (YᵤInv : YuInv Yᵤ) :
  (quPerm Gᵤ YᵤInv ) ∈ (Qu Yᵤ) := by
  rw[quPerm,Qu]
  simp only [Subtype.forall, Prod.forall, Subgroup.mem_mk, Set.mem_setOf_eq, Equiv.ofBijective_apply]
  intros _ _ _ _ _ _ h
  rw[qu, Function.Injective.eq_iff] at h
  simp only [YuInv.inv, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h, _⟩ := h
  exact h
  exact injYu Yᵤ
