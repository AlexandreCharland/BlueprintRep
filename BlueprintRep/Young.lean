import Mathlib.Combinatorics.Young.YoungDiagram --Utilisé pour le YoungDiagram
import Mathlib.GroupTheory.Perm.Basic --Utilisé pour le groupe de permutation
import Mathlib.Algebra.Group.Subgroup.Defs --Utilisé pour les sous groupes
import Mathlib.Data.ZMod.Basic --Utilisé pour définir la cardinalité

/-! Définition d'un YoungTableau, qui n'est rien de plus qu'une fonction bijective -/
structure YoungTableau (μ : YoungDiagram) where
  entry : μ.cells → (Fin μ.card)
  inj : ∀ {i j : μ.cells}, entry i = entry j → i = j

/-! Démonstration que la fonction est injective -/
lemma injYu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Function.Injective Yᵤ.entry := by
  rw [Function.Injective]
  intros i j h
  exact Yᵤ.inj h

/-! Démonstration que la fonction est bijective -/
lemma bijYu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Function.Bijective Yᵤ.entry := by
  rw[Fintype.bijective_iff_injective_and_card]
  simp
  exact injYu Yᵤ

/-! Lemme pratique pour simplifier future démonstration -/
lemma preImYu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) (n : Fin μ.card) :
  ∃! (i : μ.cells), Yᵤ.entry i = n := by
  have h : ∀ (j' : Fin μ.card), ∃! i', Yᵤ.entry i' = j' := by
    rw[← Function.bijective_iff_existsUnique _]
    exact (bijYu Yᵤ)
  exact h n

/-! Définition du sous-groupe des permutations qui permute que les rangés (Pᵤ) -/
def Pu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) where
  carrier := {x : (Equiv.Perm (Fin μ.card)) | ∀ {i j : μ}, (x (Yᵤ.entry i) = Yᵤ.entry j) → i.val.snd = j.val.snd}
  mul_mem' := by
    intros α β a b i j αβ
    rw[Equiv.Perm.coe_mul, Function.comp_apply] at αβ
    obtain ⟨k, hk, _⟩ := preImYu Yᵤ (β (Yᵤ.entry i))
    rw[Eq.comm] at hk
    rw[hk] at αβ
    rw[b hk, a αβ]
  one_mem' := by
    intros i j h
    rw[Equiv.Perm.coe_one, id_eq, Function.Injective.eq_iff] at h
    rw[h]
    exact injYu Yᵤ
  inv_mem' := by
    intros f h1 i j h2
    rw[Eq.comm, Equiv.Perm.eq_inv_iff_eq] at h2
    rw[Eq.comm]
    exact h1 h2

/-! Nécessaire pour utiliser la cardinalité -/
noncomputable instance PuCardFinite {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Fintype ↥(Pu Yᵤ) := by
  exact Fintype.ofFinite ↥(Pu Yᵤ)

/-! Cardinalité de Pᵤ -/
noncomputable def PuCard {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :=
  Fintype.card ↥(Pu Yᵤ)

/-! Définition du sous-groupe des permutations qui permute que les colonnes (Qᵤ) -/
def Qu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) : Subgroup (Equiv.Perm (Fin μ.card)) where
  carrier := {x : (Equiv.Perm (Fin μ.card)) | ∀ {i j : μ}, (x (Yᵤ.entry i) = Yᵤ.entry j) → i.val.fst = j.val.fst}
  mul_mem' := by
    intros α β a b i j αβ
    rw[Equiv.Perm.coe_mul, Function.comp_apply] at αβ
    obtain ⟨k, hk, _⟩ := preImYu Yᵤ (β (Yᵤ.entry i))
    rw[Eq.comm] at hk
    rw[hk] at αβ
    rw[b hk, a αβ]
  one_mem' := by
    intros i j h
    rw[Equiv.Perm.coe_one, id_eq, Function.Injective.eq_iff] at h
    rw[h]
    exact injYu Yᵤ
  inv_mem' := by
    intros f h1 i j h2
    rw[Eq.comm, Equiv.Perm.eq_inv_iff_eq] at h2
    rw[Eq.comm]
    exact h1 h2

/-! Nécessaire pour utiliser la cardinalité -/
noncomputable instance QuCardFinite {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :
  Fintype ↥(Qu Yᵤ) := by
  exact Fintype.ofFinite ↥(Qu Yᵤ)

/-! Cardinalité de Qᵤ -/
noncomputable def QuCard {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :=
  Fintype.card ↥(Qu Yᵤ)

/-! Démonstration que Pᵤ ∩ Qᵤ = {id} -/
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

/-! Définission de l'ensemble PᵤQᵤ -/
def PuQu {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :=
  {g : (Equiv.Perm (Fin μ.card)) | ∃ p ∈ (Pu Yᵤ), ∃ q ∈ (Qu Yᵤ), g = p ∘ q}

/-! Définission de la condition rowToCol.
Une permutation est rowToCol si tout entré de la même colonne seront envoyés sur une différente rangé.
L'identité à cette propriété. L'existence de d'autre permutation dépend du YoungDiagram. -/
def rowToCol {μ : YoungDiagram} (Yᵤ : YoungTableau μ) (g : (Equiv.Perm (Fin μ.card))) :=
  ∀ {i j k l : μ}, ((i ≠ j) ∧ (g (Yᵤ.entry i) = (Yᵤ.entry k)) ∧ (g (Yᵤ.entry j) = (Yᵤ.entry l))) → ((i.val.fst ≠ j.val.fst) ∨ (k.val.snd ≠ l.val.snd))

/-! Définition de Yᵤ⁻¹ -/
def YuInv {μ : YoungDiagram} (Yᵤ : YoungTableau μ) :=
  Fintype.bijInv (bijYu Yᵤ)

/-! Lemme pratique pour simplifier future démonstration -/
lemma YuInvYu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} (i : μ) :
  (YuInv Yᵤ) (Yᵤ.entry i) = i := by
  exact (Fintype.leftInverse_bijInv (bijYu Yᵤ)) i

/-! TODO -/
lemma staysInY {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :
  ((YuInv Yᵤ n).val.fst, ((YuInv Yᵤ) (g n)).val.snd) ∈ μ := by
  sorry --TODO

/-! Définition de la fonction qᵤ. À noter que la fonction dépend de Yᵤ et g une permutation rowToCol -/
def qu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :=
  Yᵤ.entry ⟨((YuInv Yᵤ n).val.fst, (YuInv Yᵤ (g n)).val.snd), staysInY rtc n⟩

/-! Preuve que la fonction qᵤ est bijective -/
lemma bijqu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  Function.Bijective (qu rtc) := by
  rw[Fintype.bijective_iff_injective_and_card, Function.Injective]
  by_contra contra
  simp only [not_forall, and_true] at contra
  obtain ⟨m, m', h, contra⟩:= contra
  obtain ⟨i, hi, _⟩:= preImYu Yᵤ m
  obtain ⟨j, hj, _⟩:= preImYu Yᵤ m'
  rw[← hi, ← hj, Function.Injective.eq_iff, ← ne_eq] at contra
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

/-! Pour une raison que j'ignore, une fonction bijective de A à A n'est pas la même chose qu'une bijection.
Au lieu de recommencer et définir des permutations dès le début, j'ai décidé d'utiliser Equiv.ofBijective.
Ça introduit une autre variable, mais c'est la meilleure solution que j'ai trouvé. -/
noncomputable def quPerm {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (Equiv.Perm (Fin μ.card)) := by
  exact Equiv.ofBijective (qu rtc) (bijqu rtc)

/-! Preuve que qᵤ ∈ Qᵤ -/
lemma quPermInQu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (quPerm rtc) ∈ (Qu Yᵤ) := by
  rw[quPerm, Qu]
  simp only [Subtype.forall, Prod.forall, Subgroup.mem_mk, Set.mem_setOf_eq, Equiv.ofBijective_apply]
  intros ix iy _ jx jy _ h
  rw[qu, Function.Injective.eq_iff (injYu Yᵤ)] at h
  simp only [YuInvYu, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨h, _⟩ := h
  exact h

/-! Définition de l'inverse -/
def quInv {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :=
  Fintype.bijInv (bijqu rtc)

/-! Lemme pratique pour simplifier future démonstration -/
lemma quInvqu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :
  (quInv rtc) ((qu rtc) n) = n := by
  exact (Fintype.leftInverse_bijInv (bijqu rtc)) n

/-! Preuve que la fonction pᵤ (qui sera définit après) est bien définit -/
lemma staysInX {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :
  ((YuInv Yᵤ (g (quInv rtc n))).val.fst,(YuInv Yᵤ n).val.snd ) ∈ μ := by
  have h : ∀ (n' : Fin μ.card), ∃! m', (qu rtc) m' = n' := by
    rw[← Function.bijective_iff_existsUnique _]
    exact (bijqu rtc)
  obtain ⟨m, hm, _⟩ := h n
  obtain ⟨i, hi, _⟩ := preImYu Yᵤ m
  obtain ⟨j, hj, _⟩ := preImYu Yᵤ (g (Yᵤ.entry i))
  rw[← hm, ← hi]
  simp only [quInvqu]
  rw[← hj, qu]
  simp only [YuInvYu, ← hj, Prod.mk.eta, SetLike.coe_mem]

/-! Définition de pᵤ -/
def pu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) (n : Fin μ.card) :=
  Yᵤ.entry ⟨((YuInv Yᵤ (g (quInv rtc n))).val.fst,(YuInv Yᵤ n).val.snd ), staysInX rtc n⟩

/-! Preuve que pᵤ ∘ qᵤ = g -/
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

/-! Preuve que pᵤ est une bijection -/
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
  exact Function.Bijective.comp (Equiv.bijective g) (Fintype.bijective_bijInv (bijqu rtc))

/-! Ajout du cast permutation à pᵤ -/
noncomputable def puPerm {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (Equiv.Perm (Fin μ.card)) := by
  exact Equiv.ofBijective (pu rtc) (bijpu rtc)

/-! Preuve que pᵤ ∈ Pᵤ -/
lemma puPermInPu {μ : YoungDiagram} {Yᵤ : YoungTableau μ} {g : (Equiv.Perm (Fin μ.card))} (rtc : rowToCol Yᵤ g) :
  (puPerm rtc) ∈ (Pu Yᵤ) := by
  rw[puPerm, Pu]
  simp only [Subtype.forall, Prod.forall, Subgroup.mem_mk, Set.mem_setOf_eq, Equiv.ofBijective_apply]
  intros ix iy _ jx jy _ h
  rw[pu, Function.Injective.eq_iff (injYu Yᵤ)] at h
  simp only [YuInvYu, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨_, h⟩ := h
  exact h

/-! Le résultat important. Toute permutation avec la propriété rowToCol est dans PᵤQᵤ -/
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
