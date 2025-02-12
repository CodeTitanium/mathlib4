import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Parity
import Mathlib.Logic.Encodable.Basic

namespace SimpleGraph

open Finset
section degreeLT
#check Encodable.decidableRangeEncode
variable {α : Type*} [Encodable α] [Inhabited α] (G : SimpleGraph α) [DecidableRel G.Adj]
open Encodable
/-- The set of neighbors less than a vertex -/
def neighborSetLT (b : α) : Set α := {a | encode a < encode b ∧ G.Adj a b}

/-- Any SimpleGraph α with Encodable α and DecidableRel Adj is LocallyFiniteLT -/
instance instFintypeNeighborLT (b : α): Fintype (G.neighborSetLT b) := by
  have := decidableEqOfEncodable α
  let s := @filter _ (fun x ↦ x ∈ Set.range encode) (decidableRangeEncode α) (range (encode b))
  let t := image (fun x ↦ decode₂ α x) s
  have : none ∉ t := by
    intro h
    rw [mem_image] at h
    obtain ⟨a, ha, h⟩ := h
    rw [@mem_filter] at ha
    exact decode₂_ne_none_iff.2 ha.2 h
  apply Fintype.ofFinset <| (t.image (fun x ↦ Option.getD x default)).filter (fun a ↦ G.Adj a b)
  intro a
  rw [mem_filter, mem_image]
  constructor <;> intro h
  · obtain ⟨c,hc⟩ := h.1
    cases c with
    | none => exfalso; exact this hc.1
    | some val =>
      simp only [Option.getD_some] at hc
      refine ⟨?_,h.2⟩
      rw [mem_image] at hc
      obtain ⟨x,hx⟩:= hc.1
      simp_all only
      rw [@mem_filter, mem_range] at hx
      convert hx.1.1
      rw [decode₂_eq_some] at hx
      exact hx.2
  · obtain ⟨ha,hb⟩:= h
    refine ⟨?_,hb⟩
    use (some a)
    simp only [Option.getD_some, and_true]
    rw [mem_image]
    simp_rw [decode₂_eq_some]
    use (encode a)
    simp only [mem_filter, mem_range]
    rw [@mem_filter,mem_range]
    simpa

/-- The set of neighbors less than a vertex as a Finset -/
def neighborFinsetLT (b : α) : Finset α :=
    (G.neighborSetLT b).toFinset

/-- The number of neighbors less than a vertex -/
abbrev degreeLT (b : α) : ℕ := #(G.neighborFinsetLT b)

lemma mem_neighborFinsetLT  {a b : α} :
    a ∈ G.neighborFinsetLT b ↔ encode a < encode b ∧ G.Adj a b := Set.mem_toFinset


/-- A graph is LocallyFiniteLT if every vertex has a finitely many neighbors less than it. -/
abbrev LocallyFiniteLT :=
  ∀ v : α, Fintype (G.neighborSetLT v)

lemma degreeLT_le_degree (a : α) [Fintype (G.neighborSetLT a)] [Fintype (G.neighborSet a)] :
    G.degreeLT a ≤ G.degree a := by
  rw [degreeLT, degree]
  apply card_le_card
  intro m hm
  simp only [mem_neighborFinsetLT, mem_neighborFinset] at *
  exact hm.2.symm

lemma unused (c : α → ℕ) (n : α)  :
    (range (G.degreeLT n + 1) \ ((G.neighborFinsetLT n).image c)).Nonempty := by
  apply card_pos.1
  apply lt_of_lt_of_le _ <| le_card_sdiff _ _
  rw [card_range]
  apply Nat.sub_pos_of_lt
  apply lt_of_le_of_lt  <| card_image_le
  apply Nat.lt_succ_of_le le_rfl



-- @[simp]
-- lemma neighborFinsetLT_zero : G.neighborFinsetLT 0 = ∅ := by
--   ext; rw [mem_neighborFinsetLT]; simp

-- @[simp]
-- lemma degreeLT_zero : H.degreeLT 0 = 0 := by
--   simp

/-- The function defining a greedy ℕ - coloring of a SimpleGraph ℕ -/
def greedy (n : α) : ℕ := min' _ <| G.unused (fun m ↦ ite (encode m < encode n) (greedy m) 0) n

lemma greedy_def (n : ℕ) : H.greedy n = min' _
    (H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n) := by
  rw [greedy]

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


-- abbrev greedy_colors [Fintype (Set.range H.greedy)] : Finset ℕ := (Set.range H.greedy).toFinset

-- lemma greedy_col_nonempty  [Fintype (Set.range H.greedy)] : H.greedy_colors.Nonempty :=
-- ⟨0, by rw [Set.mem_toFinset]; exact ⟨0,H.greedy_zero⟩⟩

-- /-- The largest color used in the greedy coloring (assuming it exists)-/
-- def GreedyMax [Fintype (Set.range H.greedy)] : ℕ := max' (Set.range H.greedy).toFinset
--     H.greedy_col_nonempty

-- /-- We have a computable H.Coloring (Fin (H.GreedyMax + 1)) -/
-- def GreedyColoringFinite  [Fintype (Set.range H.greedy)] : H.Coloring (Fin (H.GreedyMax + 1)) :=
--   Coloring.mk (fun v ↦ ⟨H.greedy v,  Nat.lt_succ_iff.mpr <| le_max' _ _ (by simp)⟩)
--               (by simp only [ne_eq, Fin.mk.injEq]; intro _ _ hadj; apply H.greedy_valid hadj)

-- def GreedyColoringFinBddDegLtN {Δ : ℕ} (h : ∀ v, H.degreeLT v ≤ Δ) : H.Coloring (Fin (Δ + 1)) :=
--   Coloring.mk (fun v ↦ ⟨H.greedy v, H.greedy_bdd_degLT h v⟩)
--   (by simp only [ne_eq, Fin.mk.injEq]; intro _ _ hadj; apply H.greedy_valid hadj)

-- /-- If all degrees are at most Δ  then we have a Fin (Δ + 1) - coloring -/
-- def GreedyColoringFinBddDegN {Δ : ℕ} [LocallyFinite H] (h : ∀ v, H.degree v ≤ Δ) :
--     H.Coloring (Fin (Δ + 1)) :=
--       H.GreedyColoringFinBddDegLtN fun v ↦ (H.degreeLT_le_degree v).trans (h v)

end withN
section Encodable
variable {β : Type*} [Encodable β] (H : SimpleGraph β)
open Encodable


variable [DecidableRel H.Adj]
/- If H is graph on an Encodable type β with Decidable Adj and π : β ≃ β is a permutation of β
then the graph on ℕ given by permuting β with π and then applying the encoding of β also
has Decidable Adj -/
instance instDecidableRelMapEncodableEquiv (π : β ≃ β)  :
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
      exact isFalse <| fun ⟨_, _, _, _,hb⟩ ↦ decode₂_ne_none_iff.2 ⟨_, hb⟩ hv.symm
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



/-- Given a graph on an encodable type β and a permutation of β this is the corresponding
greedy ℕ-coloring -/
abbrev GreedyColoring  (π : β ≃ β): H.Coloring ℕ := by
  apply Coloring.mk
    (fun v ↦ H.map (π.toEmbedding.trans (encode' _))|>.GreedyColoringNat _)
    (fun h h' ↦ H.map _ |>.GreedyColoringNat.valid (map_adj_apply.mpr h) h')


abbrev GreedyColorSet  (π : β ≃ β) := Set.range ((H.map (π.toEmbedding.trans (encode' β)))).greedy

abbrev GreedyColorableEquiv (π : β ≃ β) (n : ℕ) : Prop := ∀ v, H.GreedyColoring π v < n

abbrev GreedyColorable (n : ℕ) : Prop := ∃ π : β ≃ β , H.GreedyColorableEquiv π n


def GreedyOrder_ofColoring {n : ℕ} (C : H.Coloring (Fin n)) : β ≃ β where
  toFun := fun v => sorry
  invFun := fun v => sorry
  left_inv := fun v => sorry
  right_inv := fun v => sorry

lemma colorable_iff_greedyColorable {n : ℕ} : H.Colorable n ↔ H.GreedyColorable n := by
  constructor <;> intro ⟨f,hf⟩
  ·
    sorry
  · apply (colorable_iff_exists_bdd_nat_coloring _).mpr
    use H.GreedyColoring f


abbrev GreedyColorFinset (π : β ≃ β) [Fintype (GreedyColorSet H π)] : Finset ℕ :=
    (GreedyColorSet H π).toFinset

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
