import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Parity
import Mathlib.Data.ENat.Basic
import Mathlib.Logic.Encodable.Basic

namespace SimpleGraph

open Finset
section degreeLT
variable {α : Type*} [LT α] (G : SimpleGraph α)

/-- The set of neighbors less than a vertex -/
def neighborSetLT (b : α) : Set α := {a | a < b ∧ G.Adj a b}

lemma mem_neighborSetLT  {a b : α} :
    a ∈ G.neighborSetLT b ↔ a < b ∧ G.Adj a b := Iff.rfl

/-- The set of neighbors less than a vertex as a Finset -/
def neighborFinsetLT (b : α) [Fintype (G.neighborSetLT b)] : Finset α :=
    (G.neighborSetLT b).toFinset

/-- The number of neighbors less than a vertex (when finite) -/
abbrev degreeLT (b : α) [Fintype (G.neighborSetLT b)] : ℕ := #(G.neighborFinsetLT b)

lemma mem_neighborFinsetLT  {a b : α} [Fintype (G.neighborSetLT b)] :
    a ∈ G.neighborFinsetLT b ↔ a < b ∧ G.Adj a b := Set.mem_toFinset

/-- A graph is LocallyFiniteLT if every vertex has a finitely many neighbors less than it. -/
abbrev LocallyFiniteLT := ∀ v, Fintype (G.neighborSetLT v)

lemma degreeLT_le_degree (a : α) [Fintype (G.neighborSetLT a)] [Fintype (G.neighborSet a)] :
    G.degreeLT a ≤ G.degree a := by
  apply card_le_card
  intro m hm
  simp only [mem_neighborFinsetLT, mem_neighborFinset] at *
  exact hm.2.symm

lemma unused (c : α → ℕ) (a : α) [Fintype (G.neighborSetLT a)] :
    (range (G.degreeLT a + 1) \ ((G.neighborFinsetLT a).image c)).Nonempty := by
  apply card_pos.1 <| (Nat.sub_pos_of_lt _).trans_le <| le_card_sdiff _ _
  apply card_image_le.trans_lt
  rw [← degreeLT, card_range]
  exact Nat.lt_succ_self _

end degreeLT

/- Do greedy coloring of `SimpleGraph ℕ` first. -/
section withN

variable (H : SimpleGraph ℕ) [DecidableRel H.Adj]

/-- Any SimpleGraph ℕ with Decidable Adj is LocallyFiniteLT -/
instance instFintypeNeighborLTN : LocallyFiniteLT H := by
  intro n
  apply Fintype.ofFinset ((range n).filter (H.Adj n))
  intro m; rw [mem_filter, mem_range, adj_comm]
  rfl

/-- The function defining a greedy `ℕ`- coloring of a `SimpleGraph ℕ` -/
def greedy (n : ℕ) : ℕ := min' _ <| H.unused (fun m ↦ ite (m < n) (greedy m) 0) n

lemma greedy_def (n : ℕ) : H.greedy n = min' _
    (H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n) := by
  rw [greedy]

lemma greedy_valid {m n : ℕ} (hadj : H.Adj m n) : H.greedy m ≠ H.greedy n := by
  intro heq
  wlog h : m < n
  · exact this H hadj.symm heq.symm <| hadj.ne.symm.lt_of_le <| not_lt.1 h
  apply H.greedy_def n ▸
    (mem_sdiff.mp <| min'_mem _ (H.unused (fun k ↦ ite (k < n) (H.greedy k) 0) n)).2
  simp_rw [mem_image, neighborFinsetLT, Set.mem_toFinset]
  use m, ⟨h, hadj⟩, if_pos h ▸ heq

lemma greedy_le (n : ℕ) : H.greedy n ≤ H.degreeLT n := by
  rw [greedy_def]
  have h := min'_mem _ <| H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n
  rw [mem_sdiff, mem_range] at h
  exact Nat.succ_le_succ_iff.1 h.1

lemma greedy_bdd_degLT {Δ : ℕ} (h : ∀ v, H.degreeLT v ≤ Δ) (m : ℕ):  H.greedy m < Δ + 1 :=
  (H.greedy_le m).trans_lt <| Nat.succ_le_succ (h m)

abbrev GreedyColoring'  : H.Coloring ℕ :=
  Coloring.mk H.greedy H.greedy_valid

def GreedyColoringDegreeLT' {Δ : ℕ} (h : ∀ v, H.degreeLT v ≤ Δ) : H.Coloring (Fin (Δ + 1)) :=
  Coloring.mk
    (fun v ↦ ⟨(H.greedy v), H.greedy_bdd_degLT h v⟩)
    (fun h h' ↦ (H.greedy_valid h (by simpa using h')))

def GreedyColoringDegree' [LocallyFinite H] {Δ : ℕ} (h : ∀ v, H.degree v ≤ Δ) :
    H.Coloring (Fin (Δ + 1)) :=
  Coloring.mk
    (fun v ↦ ⟨H.greedy v, H.greedy_bdd_degLT (fun w ↦ H.degreeLT_le_degree w|>.trans (h w)) v⟩)
    (fun h h' ↦ H.greedy_valid h (by simpa using h'))

--------------- Encodable + Greedy vs regular colorings below ------------------


abbrev ColorOrderN (C : H.Coloring ℕ) (π : ℕ ≃ ℕ) : Prop :=
  ∀ a b, C a < C b → (π a) < (π b)
open Classical

open scoped ENat

abbrev colLE (C : ℕ → ℕ) : ℕ → ℕ  → Prop := fun a b ↦ (C a < C b) ∨ (C a = C b ∧ a ≤ b)


instance (C : ℕ → ℕ) : Ord ℕ where
  compare a b := (compare (C a) (C b)).then (compare a b)


def colLinearOrder (C : ℕ → ℕ) : PartialOrder ℕ where
  le := colLE C
  lt := fun a b ↦ (colLE C a b) ∧ ¬ (colLE C b a)
  le_refl := fun a ↦ by right; simp
  le_trans := fun a b c hab hbc ↦ by
    cases hab with
    | inl h =>
      cases hbc with
      | inl h1 => left; exact h.trans h1
      | inr h1 => left; exact h.trans_le h1.1.le
    | inr h =>
      cases hbc with
      | inl h1 => left; exact lt_of_le_of_lt h.1.le h1
      | inr h1 => right; exact ⟨h.1 ▸ h1.1,h.2.trans h1.2⟩
  le_antisymm := fun a b hab hba => by
    cases hab with
    | inl h =>
      cases hba with
      | inl h1 => exact False.elim <| h.not_lt h1
      | inr h1 => exact False.elim <| lt_irrefl _ (h1.1 ▸ h)
    | inr h =>
      cases hba with
      | inl h1 => exact False.elim <| lt_irrefl _ (h.1 ▸ h1)
      | inr h1 => exact le_antisymm h.2 h1.2
  lt_iff_le_not_le := fun a b ↦ Iff.rfl
  -- le_total := fun a b ↦ by
  --   cases lt_trichotomy (C a) (C b) with
  --   | inl h => left; left; exact h
  --   | inr h =>
  --     cases h with
  --     | inl h1 =>
  --       cases lt_trichotomy a b with
  --       | inl h2 => left; right; exact ⟨h1, h2.le⟩
  --       | inr h2 =>
  --         cases h2 with
  --         | inl h3 => left; right; exact ⟨h1, h3.le⟩
  --         | inr h3 => right; right; exact ⟨h1.symm, h3.le⟩
  --     | inr h1 => right; left; exact h1
  -- decidableLE := fun a b ↦ instDecidableOr
  -- min := fun a b => if (colLE C a b) then a else b
  -- max := fun a b => if (colLE C a b) then b else a
  -- compare_eq_compareOfLessAndEq := sorry

abbrev colLT (C : ℕ → ℕ) : ℕ → ℕ  → Prop := fun a b ↦ (C a < C b) ∨ (C a = C b ∧ a < b)

instance colWellOrder (C : ℕ → ℕ) : IsWellOrder ℕ (colLT C) where
  trichotomous := by
    intro a b
    cases lt_trichotomy (C a) (C b) with
    | inl h => left; left; exact h
    | inr h =>
      cases h with
      | inl h1 =>
        cases lt_trichotomy a b with
        | inl h2 => left; right; exact ⟨h1, h2⟩
        | inr h2 =>
          cases h2 with
          | inl h3 => right; left; exact h3
          | inr h3 => right; right; right; exact ⟨h1.symm, h3⟩
      | inr h1 => right; right; left; exact h1
  trans := fun a b c hab hbc ↦ by
    cases hab with
    | inl h =>
      cases hbc with
      | inl h1 => left; exact h.trans h1
      | inr h1 => left; exact h.trans_le h1.1.le
    | inr h =>
      cases hbc with
      | inl h1 => left; exact lt_of_le_of_lt h.1.le h1
      | inr h1 => right; exact ⟨h.1 ▸ h1.1,h.2.trans h1.2⟩
  wf := by
    
    sorry


noncomputable def next (c : ℕ∞ → ℕ∞) : ℕ∞ := sInf (c ⁻¹' {sInf (Set.range c)})
noncomputable def next_col (c : ℕ∞ → ℕ∞) : ℕ∞ → ℕ∞ :=
  fun n ↦ if (n = next c) then ⊤ else (c n)



noncomputable def ColortoFun (c : ℕ → ℕ) (n : ℕ) : ℕ :=
  sInf (c ⁻¹' {sInf (c '' (Set.univ \ (Set.Iio n).image
    (fun m ↦ ite (m < n) (ColortoFun c m) 0)))})

lemma ColortoFun_def (c : ℕ → ℕ) (n : ℕ) : ColortoFun c n =
      sInf (c ⁻¹' {sInf (c '' (Set.univ \ (Set.Iio n).image
        (fun m ↦ ite (m < n) (ColortoFun c m) 0)))}) := by
  rw [ColortoFun]

lemma exists_color_orderN  (C : H.Coloring ℕ) : Nonempty ({π : ℕ ≃ ℕ // H.ColorOrderN C π}) := by

  sorry


/-- If we used a color larger than c at vertex n then n must have an earlier neighbor that
was already colored with c -/
lemma greedy_witness {c n : ℕ} (h : c < H.greedy n) : ∃ m < n, H.Adj m n ∧ H.greedy m = c := by
  by_contra! hc
  have h2 : c ∉ ((H.neighborFinsetLT n).image (fun m ↦ ite (m < n) (H.greedy m) 0) ):= by
    intro hf
    obtain ⟨a,ha⟩ := mem_image.mp hf
    rw [mem_neighborFinsetLT, if_pos ha.1.1] at ha
    exact hc _ ha.1.1 ha.1.2 ha.2
  have := min'_le _ c <| mem_sdiff.mpr ⟨mem_range_succ_iff.2 <| h.le.trans <| H.greedy_le n, h2⟩
  exact not_lt.2 this <| H.greedy_def _ ▸ h

end withN
section withEncodable
open Encodable

/-- The `SimpleGraph ℕ` formed from a `SimpleGraph β` given by permuting `β` by `π` and then
    encoding in `ℕ` -/
abbrev label {β : Type*} [Encodable β] (H : SimpleGraph β) (π : β ≃ β) : SimpleGraph ℕ :=
    H.map (π.toEmbedding.trans (encode' β))

@[simp]
lemma label_adj {β : Type*} [Encodable β] {H : SimpleGraph β} {π : β ≃ β} {a b : β} :
    (H.label π).Adj (encode (π a)) (encode (π b)) ↔ H.Adj a b :=
  ⟨fun _ ↦ by simp_all [encode'], fun h ↦ by use a, b, h; simp [encode']⟩

variable {β : Type*} [Encodable β] (H : SimpleGraph β)
/- If H is graph on an Encodable type β with Decidable Adj and π : β ≃ β is a permutation of β
then the graph on ℕ given by permuting β with π and then applying the encoding of β also
has Decidable Adj -/
instance instDecidableRelMapEncodableEquiv [DecidableRel H.Adj] (π : β ≃ β) :
    DecidableRel (H.label π).Adj := by
  intro a b
  set u := decode₂ β a with hu
  set v := decode₂ β b with hv
  match u, v with
  | none, _ =>
    exact isFalse <| fun ⟨_, _, _, ha, _⟩ ↦ decode₂_ne_none_iff.2 ⟨_, ha⟩ hu.symm
  | _ , none =>
    exact isFalse <| fun ⟨_,_,_,_, hb⟩ ↦ decode₂_ne_none_iff.2 ⟨_, hb⟩ hv.symm
  | some u, some v =>
    exact if hadj : (H.Adj (π.symm u) (π.symm v)) then isTrue (by
      use (π.symm u), (π.symm v), hadj
      simpa [encode', ← mem_decode₂] using ⟨hu.symm, hv.symm⟩)
    else isFalse (by
      intro ⟨_, _, h, ha, hb⟩
      apply hadj
      rw [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, encode',
            Function.Embedding.coeFn_mk, ← mem_decode₂] at *
      simpa [decode₂_inj hu.symm ha, decode₂_inj hv.symm hb] using h)

/-- Any SimpleGraph β with Encodable β and DecidableRel Adj is LocallyFiniteLT -/
instance instFintypeNeighborLTEquiv [DecidableRel H.Adj] (π : β ≃ β) (b : β) :
    Fintype ((H.label π).neighborSetLT (encode (π b))) := by
  let s := @filter _ (fun x ↦ x ∈ Set.range encode) (decidableRangeEncode β) (range (encode (π b)))
  apply Fintype.ofFinset <| @filter _
    (fun n ↦ (H.label π).Adj n (encode (π b))) _ s
  intro a
  rw [@mem_filter, @mem_filter, mem_neighborSetLT, mem_range, map_adj, encode']
  simp only [Set.mem_range, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    Function.Embedding.coeFn_mk, encode_inj, and_congr_left_iff, and_iff_left_iff_imp,
    forall_exists_index, and_imp]
  intro x y h1 hlt heq h2
  use (π x)

/-- Given a graph on an encodable type β and a permutation of β this is the corresponding
greedy ℕ-coloring -/
abbrev GreedyColoring [DecidableRel H.Adj] (π : β ≃ β) : H.Coloring ℕ :=
  Coloring.mk (fun v ↦ (H.label π).greedy (encode (π v)))
    (fun h h' ↦ (H.label π).greedy_valid (label_adj.mpr h) h')

/-- Given a graph on an encodable type β and a permutation of β for which degreeLT is bounded above
by Δ this is the corresponding greedy Fin (Δ + 1)-coloring -/
def GreedyColoringDegreeLT {Δ : ℕ} [DecidableRel H.Adj] (π : β ≃ β)
    (h : ∀ v, (H.label π).degreeLT v ≤ Δ) : H.Coloring (Fin (Δ + 1)) :=
  Coloring.mk
    (fun v ↦ ⟨(H.label π).greedy (encode (π v)), (H.label π).greedy_bdd_degLT h (encode (π v))⟩)
    (fun h h' ↦ (H.label π).greedy_valid (label_adj.mpr h) (by simpa using h'))

abbrev GreedyColorable [DecidableRel H.Adj] (n : ℕ) : Prop :=
    Nonempty ({π : β ≃ β // ∀ v, H.GreedyColoring π v < n})

abbrev ColorOrder (C : H.Coloring ℕ) (π : β ≃ β) : Prop :=
  ∀ a b, C a < C b → encode (π a) < encode (π b)

abbrev ColEncode (c : ℕ → ℕ) : ℕ → ℕ × ℕ := fun b ↦ (c b, b)



lemma exists_color_order  (C : H.Coloring ℕ) : Nonempty ({π : β ≃ β // H.ColorOrder C π}) := by
  have e := equivRangeEncode β

  sorry

lemma label_mem_decode₂_of_adj {β : Type*} [Encodable β] {H : SimpleGraph β} {π : β ≃ β} {m n : ℕ}
  (ha : (H.label π).Adj m n) : ∃ c, c ∈ decode₂ β m   :=by
  rw [map_adj] at ha
  obtain ⟨a, b, h, ha, hb⟩ := ha
  use (π a), mem_decode₂.mpr ha

@[simp]
lemma label_adj' {β : Type*} [Encodable β] {H : SimpleGraph β} {π : β ≃ β} {m n : ℕ} {a b : β}
(ha : a ∈ decode₂ β m ) (hb : b ∈ decode₂ β n) :
    (H.label π).Adj m n ↔ H.Adj (π.symm a) (π.symm b) := by
  simp only [map_adj, encode', Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨u, v, hu⟩
    rw [mem_decode₂] at ha hb
    rw [← ha, ← hb ] at hu
    rw [← encode_inj.1 hu.2.1, ← encode_inj.1 hu.2.2]
    simpa using hu.1
  · intro hadj
    use (π.symm a), (π.symm b), hadj
    rw [mem_decode₂] at ha hb
    simpa using ⟨ha, hb⟩

lemma greedy_le_colorOrder [DecidableRel H.Adj] {C : H.Coloring ℕ} {π : β ≃ β} {n : ℕ} {b : β}
(h : H.ColorOrder C π) (hb : b ∈ decode₂ β n) :
    (H.label π).greedy n ≤ C (π.symm b)  := by
  induction n using Nat.strong_induction_on generalizing b
  rename_i ih
  by_contra! h'
  obtain ⟨m, hlt, hadj, heq⟩ := (H.label π).greedy_witness h'
  obtain ⟨_, hc⟩ := label_mem_decode₂_of_adj hadj
  cases (ih m hlt hc).lt_or_eq with
  | inl hl =>
    have := h _ _ (heq ▸ hl)
    simp_rw [Equiv.apply_symm_apply] at this
    rw [mem_decode₂] at hb hc
    subst_vars
    exact hlt.not_lt this
  | inr he =>
    exact C.valid ((label_adj' hc hb).1 hadj) (heq ▸ he).symm

theorem colorable_iff_greedyColorable [DecidableRel H.Adj] {n : ℕ} :
    H.Colorable n ↔ H.GreedyColorable n := by
  rw [colorable_iff_exists_bdd_nat_coloring]
  constructor
  · intro ⟨C, hC⟩
    obtain ⟨π, hp⟩ := H.exists_color_order C
    use π
    intro v
    rw [GreedyColoring]
    apply (H.greedy_le_colorOrder hp _).trans_lt <| hC (π.symm (π v))
    simp
  · intro ⟨f, _⟩
    use H.GreedyColoring f

end withEncodable

end SimpleGraph
