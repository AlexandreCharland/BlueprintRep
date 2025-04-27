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

noncomputable instance PuCardFinite {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Fintype ↥(Pu Yᵤ) := by
  exact Fintype.ofFinite ↥(Pu Yᵤ)

noncomputable def PuCard {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :=
  Fintype.card ↥(Pu Yᵤ)

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

noncomputable instance QuCardFinite {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Fintype ↥(Qu Yᵤ) := by
  exact Fintype.ofFinite ↥(Qu Yᵤ)

noncomputable def QuCard {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :=
  Fintype.card ↥(Qu Yᵤ)

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

def PuQu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :=
  {g : (Equiv.Perm (Fin μ.card)) | ∃ p ∈ (Pu Yᵤ), ∃ q ∈ (Qu Yᵤ), g = p ∘ q}

def rowToCol {μ : YoungDiagram} (Yᵤ : YoungTableau μ) (g : (Equiv.Perm (Fin μ.card))) :=
  ∀ {i j k l : μ}, ((i ≠ j) ∧ (g (Yᵤ.entry i) = (Yᵤ.entry k)) ∧ (g (Yᵤ.entry j) = (Yᵤ.entry l))) → ((i.val.fst ≠ j.val.fst) ∨ (k.val.snd ≠ l.val.snd))

def YuInv {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :=
  Fintype.bijInv (bijYu Yᵤ)

lemma leftInv {α β : Type} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) (hf : Function.Bijective f) :
  ∀ (i : α), ((Fintype.bijInv hf) ∘ f) i = i := by
  sorry

lemma YuInvYu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (i : μ) :
  (YuInv Yᵤ) (Yᵤ.entry i) = i := by
  exact leftInv _ _ _

lemma staysInY {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :
  ((YuInv Yᵤ n).val.fst, ((YuInv Yᵤ) (g n)).val.snd) ∈ μ := by
  --Aucune idée pourquoi c'est vrai, autre que ça doit l'être sinon la preuve fonctionne pas
  sorry

def qu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :=
  Yᵤ.entry ⟨((YuInv Yᵤ n).val.fst, (YuInv Yᵤ (g n)).val.snd), staysInY rtc n⟩

lemma bijqu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  Function.Bijective (qu rtc) := by
  rw [Fintype.bijective_iff_injective_and_card, Function.Injective]
  by_contra contra
  simp only [not_forall, and_true] at contra
  obtain ⟨m, m', h, contra⟩:= contra
  obtain ⟨i, hi, _⟩:= preImYu Yᵤ m
  obtain ⟨j, hj, _⟩:= preImYu Yᵤ m'
  rw [← hi, ← hj, Function.Injective.eq_iff, ← ne_eq] at contra
  rw[qu, qu, Function.Injective.eq_iff (injYu Yᵤ), ← hi, ← hj] at h
  simp only [YuInvYu, YuInvYu, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨hx, hy⟩:=h
  obtain ⟨k, hk, _⟩:= preImYu Yᵤ (g (Yᵤ.entry i))
  obtain ⟨l, hl, _⟩:= preImYu Yᵤ (g (Yᵤ.entry j))
  rw[eq_comm] at hk
  rw[eq_comm] at hl
  rw[hk, hl] at hy
  simp only [YuInvYu, YuInvYu] at hy
  have k : ((i.val.fst ≠ j.val.fst) ∨ (k.val.snd ≠ l.val.snd)) := by exact rtc ⟨contra, hk, hl⟩
  rw[hx, hy] at k
  simp only [ne_eq, not_true_eq_false, or_self] at k
  exact injYu Yᵤ

noncomputable def quPerm {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (Equiv.Perm (Fin μ.card)) := by
  exact Equiv.ofBijective (qu rtc) (bijqu rtc)

lemma quPermInQu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (quPerm rtc) ∈ (Qu Yᵤ) := by
  rw[quPerm, Qu]
  simp only [Subtype.forall, Prod.forall, Subgroup.mem_mk, Set.mem_setOf_eq, Equiv.ofBijective_apply]
  intros _ _ _ _ _ _ h
  rw[qu, Function.Injective.eq_iff (injYu Yᵤ)] at h
  simp only [YuInvYu, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h, _⟩ := h
  exact h

def quInv {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :=
  Fintype.bijInv (bijqu rtc)

lemma quInvqu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :
  (quInv rtc) ((qu rtc) n) = n := by
  exact leftInv _ _ _

lemma staysInX {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :
  ((YuInv Yᵤ (g (quInv rtc n))).val.fst,(YuInv Yᵤ n).val.snd ) ∈ μ := by
  --Aucune idée pourquoi c'est vrai, autre que ça doit l'être sinon la preuve fonctionne pas
  sorry

def pu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :=
  Yᵤ.entry ⟨((YuInv Yᵤ (g (quInv rtc n))).val.fst,(YuInv Yᵤ n).val.snd ), staysInX rtc n⟩

lemma puqug {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (pu rtc) ∘ (qu rtc) = g := by
  ext n
  obtain ⟨i, hi, _⟩ := preImYu Yᵤ n
  obtain ⟨j, hj, _⟩ := preImYu Yᵤ (g (Yᵤ.entry i))
  rw[← hi, ← hj, Function.comp_apply]
  have hq : (qu rtc (Yᵤ.entry i)) = (qu rtc (Yᵤ.entry i)) := by rfl
  nth_rewrite 2 [qu] at hq
  simp only [YuInvYu, ← hj] at hq
  simp only [pu, quInvqu, hq, YuInvYu]
  have hq' : (quInv rtc) (qu rtc (Yᵤ.entry i)) = (quInv rtc) (qu rtc (Yᵤ.entry i)) := by rfl
  nth_rewrite 1 [quInvqu, hq] at hq'
  simp only[← hq', ← hj, YuInvYu]

lemma bijpu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  Function.Bijective (pu rtc) := by
  have h : g ∘ (quInv rtc) = g ∘ (quInv rtc) := by rfl
  nth_rewrite 1 [← puqug rtc, Function.comp_assoc] at h
  have h' : (qu rtc) ∘ (quInv rtc) = id := by
    ext n
    have j : ((quInv rtc) ((qu rtc) ((quInv rtc) n))) = ((quInv rtc) ((qu rtc) ((quInv rtc) n))) := by rfl
    nth_rewrite 2 [quInvqu] at j
    rw[Function.Injective.eq_iff] at j
    rw[Function.comp_apply, id_eq, j]
    rw[quInv]
    exact (Fintype.bijective_bijInv (bijqu rtc)).injective
  rw[h', Function.comp_id] at h
  rw[h, quInv]
  refine Function.Bijective.comp ?_ ?_
  exact Equiv.bijective g
  exact (Fintype.bijective_bijInv (bijqu rtc))

noncomputable def puPerm {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (Equiv.Perm (Fin μ.card)) := by
  exact Equiv.ofBijective (pu rtc) (bijpu rtc)

lemma puPermInPu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (puPerm rtc) ∈ (Pu Yᵤ) := by
  rw[puPerm, Pu]
  simp only [Subtype.forall, Prod.forall, Subgroup.mem_mk, Set.mem_setOf_eq, Equiv.ofBijective_apply]
  intros _ _ _ _ _ _ h
  rw[pu, Function.Injective.eq_iff (injYu Yᵤ)] at h
  simp only [YuInvYu, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨_, h⟩ := h
  exact h

lemma gInPuQu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  g ∈ (PuQu Yᵤ) := by
  rw[PuQu, Set.mem_setOf_eq]
  exists (puPerm rtc)
  constructor
  exact puPermInPu rtc
  exists (quPerm rtc)
  constructor
  exact quPermInQu rtc
  rw[puPerm,quPerm, ← puqug]
  rfl
  exact rtc
