/-
Copyright (c) 2023 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Parity
import Mathlib.Data.Rat.Encodable
/-!
# Concrete colorings of common graphs

This file defines colorings for some common graphs

## Main declarations

* `SimpleGraph.pathGraph.bicoloring`: Bicoloring of a path graph.

-/

assert_not_exists Field

namespace SimpleGraph

theorem two_le_chromaticNumber_of_adj {α} {G : SimpleGraph α} {u v : α} (hadj : G.Adj u v) :
    2 ≤ G.chromaticNumber := by
  refine le_of_not_lt ?_
  intro h
  have hc : G.Colorable 1 := chromaticNumber_le_iff_colorable.mp (Order.le_of_lt_add_one h)
  let c : G.Coloring (Fin 1) := hc.some
  exact c.valid hadj (Subsingleton.elim (c u) (c v))

/-- Bicoloring of a path graph -/
def pathGraph.bicoloring (n : ℕ) :
    Coloring (pathGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v
    rw [pathGraph_adj]
    rintro (h | h) <;> simp [← h, not_iff, Nat.succ_mod_two_eq_zero_iff]

/-- Embedding of `pathGraph 2` into the first two elements of `pathGraph n` for `2 ≤ n` -/
def pathGraph_two_embedding (n : ℕ) (h : 2 ≤ n) : pathGraph 2 ↪g pathGraph n where
  toFun v := ⟨v, trans v.2 h⟩
  inj' := by
    rintro v w
    rw [Fin.mk.injEq]
    exact Fin.ext
  map_rel_iff' := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [pathGraph, ← Fin.coe_covBy_iff]

theorem chromaticNumber_pathGraph (n : ℕ) (h : 2 ≤ n) :
    (pathGraph n).chromaticNumber = 2 := by
  have hc := (pathGraph.bicoloring n).colorable
  apply le_antisymm
  · exact hc.chromaticNumber_le
  · have hadj : (pathGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by simp [pathGraph_adj]
    exact two_le_chromaticNumber_of_adj hadj

theorem Coloring.even_length_iff_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Even p.length ↔ (c u ↔ c v) := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    simp only [Walk.length_cons, Nat.even_add_one]
    have : ¬ c u = true ↔ c v = true := by
      rw [← not_iff, ← Bool.eq_iff_iff]
      exact c.valid h
    tauto

theorem Coloring.odd_length_iff_not_congr {α} {G : SimpleGraph α}
    (c : G.Coloring Bool) {u v : α} (p : G.Walk u v) :
    Odd p.length ↔ (¬c u ↔ c v) := by
  rw [← Nat.not_even_iff_odd, c.even_length_iff_congr p]
  tauto

theorem Walk.three_le_chromaticNumber_of_odd_loop {α} {G : SimpleGraph α} {u : α} (p : G.Walk u u)
    (hOdd : Odd p.length) : 3 ≤ G.chromaticNumber := Classical.by_contradiction <| by
  intro h
  have h' : G.chromaticNumber ≤ 2 := Order.le_of_lt_add_one <| not_le.mp h
  let c : G.Coloring (Fin 2) := (chromaticNumber_le_iff_colorable.mp h').some
  let c' : G.Coloring Bool := recolorOfEquiv G finTwoEquiv c
  have : ¬c' u ↔ c' u := (c'.odd_length_iff_not_congr p).mp hOdd
  simp_all

/-- Bicoloring of a cycle graph of even size -/
def cycleGraph.bicoloring_of_even (n : ℕ) (h : Even n) : Coloring (cycleGraph n) Bool :=
  Coloring.mk (fun u ↦ u.val % 2 = 0) <| by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only [ne_eq, decide_eq_decide]
      simp only [cycleGraph_adj] at hadj
      cases hadj with
      | inl huv | inr huv =>
        rw [← add_eq_of_eq_sub' huv.symm, ← Fin.even_iff_mod_of_even h,
          ← Fin.even_iff_mod_of_even h, Fin.even_add_one_iff_odd]
        apply Classical.not_iff.mpr
        simp [Fin.not_odd_iff_even_of_even h, Fin.not_even_iff_odd_of_even h]

theorem chromaticNumber_cycleGraph_of_even (n : ℕ) (h : 2 ≤ n) (hEven : Even n) :
    (cycleGraph n).chromaticNumber = 2 := by
  have hc := (cycleGraph.bicoloring_of_even n hEven).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hadj : (cycleGraph n).Adj ⟨0, Nat.zero_lt_of_lt h⟩ ⟨1, h⟩ := by
      simp [cycleGraph_adj', Fin.sub_val_of_le]
    exact two_le_chromaticNumber_of_adj hadj

/-- Tricoloring of a cycle graph -/
def cycleGraph.tricoloring (n : ℕ) (h : 2 ≤ n) : Coloring (cycleGraph n)
  (Fin 3) := Coloring.mk (fun u ↦ if u.val = n - 1 then 2 else ⟨u.val % 2, by fin_omega⟩) <| by
    intro u v hadj
    match n with
    | 0 => exact u.elim0
    | 1 => simp at h
    | n + 2 =>
      simp only
      simp [cycleGraph_adj] at hadj
      split_ifs with hu hv
      · simp [Fin.eq_mk_iff_val_eq.mpr hu, Fin.eq_mk_iff_val_eq.mpr hv] at hadj
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val (?_))).symm
        exact v.val.mod_lt Nat.zero_lt_two
      · refine (Fin.ne_of_lt (Fin.mk_lt_of_lt_val ?_))
        exact u.val.mod_lt Nat.zero_lt_two
      · simp [Fin.ext_iff]
        have hu' : u.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        have hv' : v.val + (1 : Fin (n + 2)) < n + 2 := by fin_omega
        cases hadj with
        | inl huv | inr huv =>
          rw [← add_eq_of_eq_sub' huv.symm]
          simp only [Fin.val_add_eq_of_add_lt hv', Fin.val_add_eq_of_add_lt hu', Fin.val_one]
          rw [show ∀x y : ℕ, x % 2 = y % 2 ↔ (Even x ↔ Even y) by simp [Nat.even_iff]; omega,
            Nat.even_add]
          simp only [Nat.not_even_one, iff_false, not_iff_self, iff_not_self]
          exact id

theorem chromaticNumber_cycleGraph_of_odd (n : ℕ) (h : 2 ≤ n) (hOdd : Odd n) :
    (cycleGraph n).chromaticNumber = 3 := by
  have hc := (cycleGraph.tricoloring n h).colorable
  apply le_antisymm
  · apply hc.chromaticNumber_le
  · have hn3 : n - 3 + 3 = n := by
      refine Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h ?_))
      intro h2
      rw [← h2] at hOdd
      exact (Nat.not_odd_iff.mpr rfl) hOdd
    let w : (cycleGraph (n - 3 + 3)).Walk 0 0 := cycleGraph_EulerianCircuit (n - 3)
    have hOdd' : Odd w.length := by
      rw [cycleGraph_EulerianCircuit_length, hn3]
      exact hOdd
    rw [← hn3]
    exact Walk.three_le_chromaticNumber_of_odd_loop w hOdd'


--------- Greedy colorings
open Finset
section degreeLT

variable {α : Type*} [LT α] (G : SimpleGraph α)

/-- The set of neighbors less than a vertex -/
def neighborSetLT (b : α) : Set α := {a | a < b ∧ G.Adj a b}

/-- The set of neighbors less than a vertex as a Finset -/
def neighborFinsetLT (b : α)  [Fintype (G.neighborSetLT b)] : Finset α :=
    (G.neighborSetLT b).toFinset

/-- The number of neighbors less than a vertex -/
def degreeLT (b : α) [Fintype (G.neighborSetLT b)] : ℕ := #(G.neighborFinsetLT b)

lemma mem_neighborFinsetLT  {a b : α} [Fintype (G.neighborSetLT b)] :
    a ∈ G.neighborFinsetLT b ↔ a < b ∧ G.Adj a b := Set.mem_toFinset

/-- A graph is LocallyFiniteLT if every vertex has a finitely many neighbors less than it. -/
abbrev LocallyFiniteLT :=
  ∀ v : α, Fintype (G.neighborSetLT v)

lemma degreeLT_le_degree (n : α) [Fintype (G.neighborSetLT n)] [Fintype (G.neighborSet n)] :
    G.degreeLT n ≤ G.degree n := by
  rw [degreeLT,degree]
  apply card_le_card
  intro m hm; simp only [mem_neighborFinsetLT, mem_neighborFinset] at *
  exact hm.2.symm

lemma unused (c : α → ℕ) (n : α) [Fintype (G.neighborSetLT n)] :
    (range (G.degreeLT n + 1) \ ((G.neighborFinsetLT n).image c)).Nonempty := by
  apply card_pos.1
  apply lt_of_lt_of_le _ <| le_card_sdiff _ _
  rw [card_range]
  apply Nat.sub_pos_of_lt
  apply lt_of_le_of_lt  <| card_image_le
  apply Nat.lt_succ_of_le le_rfl

end degreeLT
section withN

variable (H : SimpleGraph ℕ) [DecidableRel H.Adj]
/-- Any SimpleGraph ℕ is LocallyFiniteLT -/
instance instFintypeNeighborLTN : LocallyFiniteLT H := by
  intro n
  apply Fintype.ofFinset ((range n).filter (H.Adj n))
  intro m; rw [mem_filter, mem_range, adj_comm]
  rfl

/-- The function defining a greedy ℕ - coloring of a SimpleGraph ℕ -/
private def greedy (n : ℕ) : ℕ := min' _ <| H.unused (fun m ↦ ite (m < n) (greedy m) 0) n

private lemma greedy_def (n : ℕ) : H.greedy n = min' _
    (H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n) := by
  rw [greedy]

private lemma greedy_valid {m n : ℕ} (hadj : H.Adj m n) :
    H.greedy m ≠ H.greedy n := by
  intro heq
  wlog h : m < n
  · rw [not_lt] at h; exact this H hadj.symm heq.symm <| lt_of_le_of_ne h hadj.ne.symm
  apply H.greedy_def n ▸
    (mem_sdiff.mp <| min'_mem _ (H.unused (fun k ↦ ite (k < n) (H.greedy k) 0) n)).2
  simp_rw [mem_image,neighborFinsetLT, Set.mem_toFinset]
  use m, ⟨h, hadj⟩, if_pos h ▸ heq

private lemma greedy_le (n : ℕ) : H.greedy n ≤ H.degreeLT n  := by
  rw [greedy_def]
  have h := min'_mem _ <| H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n
  rw [mem_sdiff, mem_range] at h
  apply Nat.succ_le_succ_iff.1 h.1

private lemma greedy_bdd_degLT {Δ : ℕ} (h : ∀ v, H.degreeLT v ≤ Δ) : ∀ m, H.greedy m < Δ + 1 :=
  fun m ↦ lt_of_le_of_lt (H.greedy_le m) <| Nat.succ_le_succ (h m)

/-- The greeding ℕ - coloring of a SimpleGraph ℕ -/
def GreedyColoring : H.Coloring ℕ := Coloring.mk H.greedy (fun hadj ↦ H.greedy_valid hadj)

#check Set.range H.greedy
noncomputable def GreedyChromaticNumber : ℕ := max' (Set.range H.greedy)

def GreedyColoringFinBddDegLtN {Δ : ℕ} (h : ∀ v, H.degreeLT v ≤ Δ) : H.Coloring (Fin (Δ + 1)) :=
  Coloring.mk (fun v ↦ ⟨H.greedy v, H.greedy_bdd_degLT h v⟩)
  (by simp only [ne_eq, Fin.mk.injEq]; intro _ _ hadj; apply H.greedy_valid hadj)

/-- If all degrees are at most Δ  then we have a Fin (Δ + 1) - coloring -/
def GreedyColoringFinBddDegN {Δ : ℕ} [LocallyFinite H] (h : ∀ v, H.degree v ≤ Δ) :
    H.Coloring (Fin (Δ + 1)) :=
      H.GreedyColoringFinBddDegLtN fun v ↦ (H.degreeLT_le_degree v).trans (h v)

end withN

section Encodable
variable {β : Type*} [Encodable β] (H : SimpleGraph β) [DecidableRel H.Adj]

open Encodable
instance instDecidableRelMapEncodable : ∀ a b, Decidable
  (Relation.Map H.Adj (encode' β) (encode' β) a b) :=by
    intro a b
    set u := decode₂ β a with hu
    set v := decode₂ β b with hv
    match u with
    | none =>
      exact isFalse <| fun ⟨_, _, _,ha,_⟩ ↦ decode₂_ne_none_iff.2 ⟨_, ha⟩ hu.symm
    | some u =>
      match v with
      | none =>
        exact isFalse <| fun ⟨_, _, _,_,hb⟩ ↦ decode₂_ne_none_iff.2 ⟨_, hb⟩ hv.symm
      | some v =>
        exact if hadj : (H.Adj u v) then isTrue (by
          use u, v, hadj
          constructor <;> rw [encode'] <;> dsimp <;> rw [ ← mem_decode₂]
          · exact hu.symm
          · exact hv.symm)
        else isFalse (by
          intro ⟨x, y, h, ha, hb⟩
          apply hadj
          rw [encode'] at ha hb; dsimp at ha hb
          rw [← mem_decode₂] at ha hb
          exact decode₂_inj hu.symm ha ▸ decode₂_inj hv.symm hb ▸ h)

-- instance instFintypeNeighborMapEncodable  [LocallyFinite H] :
--   LocallyFinite (H.map (encode' β)) := by
--   intro n
--   set u := decode₂ β n with hu
--   match u with
--   | none =>
--     apply Fintype.ofFinset ∅; simp only [not_mem_empty, mem_neighborSet, map_adj, false_iff,
--       not_exists, not_and]
--     intro n a b hadj h hf
--     rw [encode'] at *; dsimp at *; rw [← mem_decode₂,← hu] at h
--     contradiction
--   | some u' =>
--     let s :=(H.neighborFinset u')
--     apply Fintype.ofFinset  ((H.neighborFinset u').map (encode' β))
--     intro n
--     simp only [mem_map, mem_neighborSet, map_adj]
--     constructor
--     · intro ⟨a,ha1,ha2⟩
--       use u',a
--       rw [mem_neighborFinset] at ha1
--       refine ⟨ha1, ?_, ha2⟩
--       have : u' ∈ decode₂ β _:=  hu.symm
--       rwa [mem_decode₂] at this
--     · intro ⟨u',v',had,h1,h2⟩
--       use v'
--       simp only [mem_neighborFinset]
--       refine ⟨?_,h2⟩
--       convert had
--       rw [encode']at h1; dsimp at h1 ; rw [← mem_decode₂] at h1
--       apply decode₂_inj hu.symm h1

def GreedyColoring' : H.Coloring ℕ := by
  apply Coloring.mk
    (fun v ↦ (H.map (encode' β)).GreedyColoring ((encode' β) v))
    (fun hadj heq ↦ (H.map (encode' β)).GreedyColoring.valid
      (map_adj_apply.mpr hadj) heq)

open Rat
variable {k : ℕ} {K : SimpleGraph ℚ} [DecidableRel K.Adj]

#check K.GreedyColoring'

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
