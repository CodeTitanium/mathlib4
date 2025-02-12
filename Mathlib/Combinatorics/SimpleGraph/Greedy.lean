import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Parity
import Mathlib.Logic.Encodable.Basic

namespace SimpleGraph

open Finset
section degreeLT
#check Encodable.decidableRangeEncode
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
abbrev LocallyFiniteLT :=
  ∀ v : α, Fintype (G.neighborSetLT v)

lemma degreeLT_le_degree (n : α) [Fintype (G.neighborSetLT n)] [Fintype (G.neighborSet n)] :
    G.degreeLT n ≤ G.degree n := by
  rw [degreeLT, degree]
  apply card_le_card
  intro m hm
  simp only [mem_neighborFinsetLT, mem_neighborFinset] at *
  exact hm.2.symm

lemma unused (c : α → ℕ) (n : α) [Fintype (G.neighborSetLT n)] :
    (range (G.degreeLT n + 1) \ ((G.neighborFinsetLT n).image c)).Nonempty := by
  apply card_pos.1 <| lt_of_lt_of_le (Nat.sub_pos_of_lt _) <| le_card_sdiff _ _
  apply lt_of_le_of_lt  <| card_image_le
  rw [← degreeLT, card_range]
  apply Nat.lt_succ_of_le le_rfl

end degreeLT

section withN
variable (H : SimpleGraph ℕ) [DecidableRel H.Adj]

/-- Any SimpleGraph ℕ with Decidable Adj is LocallyFiniteLT -/
instance instFintypeNeighborLTN : LocallyFiniteLT H := by
  intro n
  apply Fintype.ofFinset ((range n).filter (H.Adj n))
  intro m; rw [mem_filter, mem_range, adj_comm]
  rfl

@[simp]
lemma neighborFinsetLT_zero : H.neighborFinsetLT 0 = ∅ := by
  ext; rw [mem_neighborFinsetLT]; simp

@[simp]
lemma degreeLT_zero : H.degreeLT 0 = 0 := by
  simp

/-- The function defining a greedy ℕ - coloring of a SimpleGraph ℕ -/
def greedy (n : ℕ) : ℕ := min' _ <| H.unused (fun m ↦ ite (m < n) (greedy m) 0) n

lemma greedy_def (n : ℕ) : H.greedy n = min' _
    (H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n) := by
  rw [greedy]

@[simp]
lemma greedy_zero : H.greedy 0 = 0:=by
  rw [greedy_def]
  simp

lemma greedy_valid {m n : ℕ} (hadj : H.Adj m n) :
    H.greedy m ≠ H.greedy n := by
  intro heq
  wlog h : m < n
  · rw [not_lt] at h; exact this H hadj.symm heq.symm <| lt_of_le_of_ne h hadj.ne.symm
  apply H.greedy_def n ▸
    (mem_sdiff.mp <| min'_mem _ (H.unused (fun k ↦ ite (k < n) (H.greedy k) 0) n)).2
  simp_rw [mem_image,neighborFinsetLT, Set.mem_toFinset]
  use m, ⟨h, hadj⟩, if_pos h ▸ heq

lemma greedy_le (n : ℕ) : H.greedy n ≤ H.degreeLT n  := by
  rw [greedy_def]
  have h := min'_mem _ <| H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n
  rw [mem_sdiff, mem_range] at h
  apply Nat.succ_le_succ_iff.1 h.1

lemma greedy_bdd_degLT {Δ : ℕ} (h : ∀ v, H.degreeLT v ≤ Δ) (m : ℕ):  H.greedy m < Δ + 1 :=
  lt_of_le_of_lt (H.greedy_le m) <| Nat.succ_le_succ (h m)

/-- The greeding ℕ - coloring of a SimpleGraph ℕ -/
def GreedyColoringNat : H.Coloring ℕ := Coloring.mk H.greedy (fun hadj ↦ H.greedy_valid hadj)


abbrev greedy_colors [Fintype (Set.range H.greedy)] : Finset ℕ := (Set.range H.greedy).toFinset

lemma greedy_col_nonempty  [Fintype (Set.range H.greedy)] : H.greedy_colors.Nonempty :=
⟨0, by rw [Set.mem_toFinset]; exact ⟨0,H.greedy_zero⟩⟩

/-- The largest color used in the greedy coloring (assuming it exists)-/
def GreedyMax [Fintype (Set.range H.greedy)] : ℕ := max' (Set.range H.greedy).toFinset
    H.greedy_col_nonempty

/-- We have a computable H.Coloring (Fin (H.GreedyMax + 1)) -/
def GreedyColoringFinite  [Fintype (Set.range H.greedy)] : H.Coloring (Fin (H.GreedyMax + 1)) :=
  Coloring.mk (fun v ↦ ⟨H.greedy v,  Nat.lt_succ_iff.mpr <| le_max' _ _ (by simp)⟩)
              (by simp only [ne_eq, Fin.mk.injEq]; intro _ _ hadj; apply H.greedy_valid hadj)

def GreedyColoringFinBddDegLtN {Δ : ℕ} (h : ∀ v, H.degreeLT v ≤ Δ) : H.Coloring (Fin (Δ + 1)) :=
  Coloring.mk (fun v ↦ ⟨H.greedy v, H.greedy_bdd_degLT h v⟩)
  (by simp only [ne_eq, Fin.mk.injEq]; intro _ _ hadj; apply H.greedy_valid hadj)

/-- If all degrees are at most Δ  then we have a Fin (Δ + 1) - coloring -/
def GreedyColoringFinBddDegN {Δ : ℕ} [LocallyFinite H] (h : ∀ v, H.degree v ≤ Δ) :
    H.Coloring (Fin (Δ + 1)) :=
      H.GreedyColoringFinBddDegLtN fun v ↦ (H.degreeLT_le_degree v).trans (h v)

end withN
section Encodable
variable {β : Type*} [Encodable β] (H : SimpleGraph β) [Inhabited β]
open Encodable

/- If H is graph on an Encodable type β with Decidable Adj and π : β ≃ β is a permutation of β
then the graph on ℕ given by permuting β with π and then applying the encoding of β also
has Decidable Adj -/
instance instDecidableRelMapEncodableEquiv [DecidableRel H.Adj] (π : β ≃ β)  :
    DecidableRel (H.map (π.toEmbedding.trans (encode' β))).Adj := by
  intro a b
  set u := decode₂ β a with hu
  set v := decode₂ β b with hv
  match u with
  | none =>
    exact isFalse <| fun ⟨_, _, _, ha, _⟩ ↦ decode₂_ne_none_iff.2 ⟨_, ha⟩ hu.symm
  | some u =>
    match v with
    | none =>
      exact isFalse <| fun ⟨_,_,_,_, hb⟩ ↦ decode₂_ne_none_iff.2 ⟨_, hb⟩ hv.symm
    | some v =>
      exact if hadj : (H.Adj (π.symm u) (π.symm v)) then isTrue (by
        use (π.symm u), (π.symm v), hadj
        simpa [encode', ← mem_decode₂] using ⟨hu.symm, hv.symm⟩)
      else isFalse (by
        intro ⟨_, _, h, ha, hb⟩
        apply hadj
        rw [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, encode',
              Function.Embedding.coeFn_mk, ← mem_decode₂] at ha hb
        simpa [decode₂_inj hu.symm ha, decode₂_inj hv.symm hb] using h)


/-- Any SimpleGraph β with Encodable β and DecidableRel Adj is LocallyFiniteLT -/
instance instFintypeNeighborLTEquiv [DecidableRel H.Adj] (π : β ≃ β ) (b : β) :
    Fintype ((H.map (π.toEmbedding.trans (encode' β))).neighborSetLT (encode (π b))) := by
  let s := @filter _ (fun x ↦ x ∈ Set.range encode) (decidableRangeEncode β) (range (encode (π b)))
  apply Fintype.ofFinset <| @filter _
    (fun n ↦ (H.map (π.toEmbedding.trans (encode' β))).Adj n (encode (π b))) _ s
  intro a
  rw [@mem_filter, @mem_filter, mem_neighborSetLT, mem_range, map_adj, encode']
  simp only [Set.mem_range, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    Function.Embedding.coeFn_mk, encode_inj, and_congr_left_iff, and_iff_left_iff_imp,
    forall_exists_index, and_imp]
  intro x y h1 hlt heq h2
  use (π x)



/-- Given a graph on an encodable type β and a permutation of β this is the corresponding
greedy ℕ-coloring -/
abbrev GreedyColoring [DecidableRel H.Adj] (π : β ≃ β): H.Coloring ℕ := by
  apply Coloring.mk
    (fun v ↦ H.map (π.toEmbedding.trans (encode' _))|>.GreedyColoringNat _)
    (fun h h' ↦ H.map _ |>.GreedyColoringNat.valid (map_adj_apply.mpr h) h')


abbrev GreedyColorSet [DecidableRel H.Adj] (π : β ≃ β) :=
    Set.range ((H.map (π.toEmbedding.trans (encode' β)))).greedy

abbrev GreedyColorableEquiv [DecidableRel H.Adj] (π : β ≃ β) (n : ℕ) : Prop :=
    ∀ v, H.GreedyColoring π v < n

abbrev GreedyColorable [DecidableRel H.Adj] (n : ℕ) : Prop :=
    ∃ π : β ≃ β, H.GreedyColorableEquiv π n

def instLinearOrderofColoring (C : H.Coloring ℕ) : LinearOrder β where
  le := fun a b ↦ C a < C b ∨ C a = C b ∧ encode a ≤ encode b
  le_refl := fun _ ↦ by simp
  le_trans := fun a b c hab hbc ↦ by
    cases hab with
    | inl h =>
      cases hbc with
      | inl h' => exact Or.inl <| h.trans h'
      | inr h' => exact Or.inl <| lt_of_lt_of_le h h'.1.le
    | inr h =>
      cases hbc with
      | inl h' => exact Or.inl <| lt_of_le_of_lt h.1.le h'
      | inr h' => exact Or.inr <| ⟨h.1 ▸ h'.1, h.2.trans h'.2⟩
  le_antisymm := fun a b h h' ↦ by
    cases h with
    | inl h =>
      cases h' with
      | inl h' => exact False.elim <| h.not_lt h'
      | inr h' => exact False.elim (by rw [h'.1] at h; exact (Nat.lt_irrefl _) h)
    | inr h =>
      cases h' with
      | inr h' => exact encode_inj.mp <| h.2.antisymm h'.2
      | inl h' => exact False.elim (by rw [h.1] at h'; exact (Nat.lt_irrefl _) h')
  le_total := fun a b ↦ by
    wlog h : C a ≤ C b
    · rw [not_le] at h
      apply Or.symm <| this _ _ _ _ h.le
    · cases h.lt_or_eq with
    | inl h => left ; left; exact h
    | inr h =>
      wlog h' : encode a ≤ encode b
      · rw [not_le] at h'
        apply Or.symm <| this H _ _ _ _ h.symm.le h.symm h'.le
      · left; right; exact ⟨h, h'⟩
  decidableLE := fun a b ↦ if h : C a < C b ∨ C a = C b ∧ encode a ≤ encode b then isTrue h
                                else isFalse (by simp [h])


def GreedyOrder_ofColoring (C : H.Coloring ℕ) : β ≃ β where
  toFun := fun v => sorry
  invFun := fun v => sorry
  left_inv := fun v => sorry
  right_inv := fun v => sorry

lemma colorable_iff_greedyColorable [DecidableRel H.Adj] {n : ℕ} :
    H.Colorable n ↔ H.GreedyColorable n := by
  constructor <;> intro ⟨f,hf⟩
  ·
    sorry
  · apply (colorable_iff_exists_bdd_nat_coloring _).mpr
    use H.GreedyColoring f

abbrev GreedyColorFinset (π : β ≃ β) [DecidableRel H.Adj] [Fintype (GreedyColorSet H π)] :
    Finset ℕ := (GreedyColorSet H π).toFinset

instance instFintypeDegreeMap {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {v : V} [Fintype (G.neighborSet v)] {e : V ↪ W} : Fintype ((G.map e).neighborSet (e v)) := by
  apply Fintype.ofFinset ((G.neighborFinset v).image e)
  intro x; simp only [mem_image, mem_neighborFinset, mem_neighborSet, map_adj,
    EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro ⟨w, hw⟩
    use v, w, hw.1, rfl, hw.2
  · intro ⟨a, b, h⟩
    use b, h.2.1 ▸ h.1, h.2.2

lemma degree_eq_degree_map {V W : Type*} [DecidableEq V] [DecidableEq W] {G : SimpleGraph V}
    {v : V} [Fintype (G.neighborSet v)] {e : V ↪ W} :
    (G.map e).degree (e v) = G.degree v := by
  rw [degree, degree]
  convert  card_image_of_injective _ e.inj'
  ext; simp only [mem_image, mem_neighborFinset, mem_neighborSet, map_adj,
    EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro ⟨a, b, h⟩
    use b, h.2.1 ▸ h.1, h.2.2
  · intro ⟨w, hw⟩
    use v, w, hw.1, rfl, hw.2

end Encodable
end SimpleGraph
