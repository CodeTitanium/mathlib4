import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fin.Parity
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
abbrev LocallyFiniteLT :=
  ∀ v : α, Fintype (G.neighborSetLT v)

lemma degreeLT_le_degree (a : α) [Fintype (G.neighborSetLT a)] [Fintype (G.neighborSet a)] :
    G.degreeLT a ≤ G.degree a := by
  rw [degreeLT, degree]
  apply card_le_card
  intro m hm
  simp only [mem_neighborFinsetLT, mem_neighborFinset] at *
  exact hm.2.symm

lemma unused (c : α → ℕ) (a : α) [Fintype (G.neighborSetLT a)] :
    (range (G.degreeLT a + 1) \ ((G.neighborFinsetLT a).image c)).Nonempty := by
  apply card_pos.1 <|  (Nat.sub_pos_of_lt _).trans_le <| le_card_sdiff _ _
  apply card_image_le.trans_lt
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

/-- The function defining a greedy ℕ - coloring of a SimpleGraph ℕ -/
def greedy (n : ℕ) : ℕ := min' _ <| H.unused (fun m ↦ ite (m < n) (greedy m) 0) n

lemma greedy_def (n : ℕ) : H.greedy n = min' _
    (H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n) := by
  rw [greedy]

lemma greedy_valid {m n : ℕ} (hadj : H.Adj m n) :
    H.greedy m ≠ H.greedy n := by
  intro heq
  wlog h : m < n
  · exact this H hadj.symm heq.symm <| hadj.ne.symm.lt_of_le <| not_lt.1 h
  apply H.greedy_def n ▸
    (mem_sdiff.mp <| min'_mem _ (H.unused (fun k ↦ ite (k < n) (H.greedy k) 0) n)).2
  simp_rw [mem_image, neighborFinsetLT, Set.mem_toFinset]
  use m, ⟨h, hadj⟩, if_pos h ▸ heq

lemma greedy_le (n : ℕ) : H.greedy n ≤ H.degreeLT n  := by
  rw [greedy_def]
  have h := min'_mem _ <| H.unused (fun m ↦ ite (m < n) (H.greedy m) 0) n
  rw [mem_sdiff, mem_range] at h
  exact Nat.succ_le_succ_iff.1 h.1

lemma greedy_bdd_degLT {Δ : ℕ} (h : ∀ v, H.degreeLT v ≤ Δ) (m : ℕ):  H.greedy m < Δ + 1 :=
  (H.greedy_le m).trans_lt <| Nat.succ_le_succ (h m)

/-- If we used a color larger than c at vertex n then n must have an earlier neighbor that
was already colored with c -/
lemma greedy_witness {c n : ℕ} (h : c < H.greedy n) : ∃ m < n, H.Adj m n ∧ H.greedy m = c := by
  by_contra! hc
  have h2 : c ∉ ((H.neighborFinsetLT n).image (fun m ↦ ite (m < n) (H.greedy m) 0) ):= by
    intro hf
    obtain ⟨a,ha⟩ := mem_image.mp hf
    rw [mem_neighborFinsetLT, if_pos ha.1.1] at ha
    exact hc _ ha.1.1 ha.1.2 ha.2
  have := min'_le _ c <| mem_sdiff.mpr ⟨mem_range_succ_iff.2 <| h.le.trans (H.greedy_le n), h2⟩
  exact not_lt.2 this <| H.greedy_def _ ▸ h

@[simp]
lemma neighborFinsetLT_zero : H.neighborFinsetLT 0 = ∅ := by
  ext; rw [mem_neighborFinsetLT]; simp

@[simp]
lemma degreeLT_zero : H.degreeLT 0 = 0 := by
  simp

abbrev ColorOrderN (C : H.Coloring ℕ) (π : ℕ ≃ ℕ) : Prop :=
  ∀ a b, C a < C b → (π a) < (π b)

lemma greedy_le_colorOrderN [DecidableRel H.Adj] {C : H.Coloring ℕ} {π : ℕ ≃ ℕ}
    [DecidableRel (H.map π.toEmbedding).Adj] (h : H.ColorOrderN C π) (a : ℕ) :
    (H.map π).greedy a ≤ C (π.symm a)  := by
  induction a using Nat.strong_induction_on
  rename_i n ih
  by_contra! h'
  obtain ⟨m, hlt, hadj, heq⟩ := (H.map π.toEmbedding).greedy_witness h'
  cases (ih m hlt).lt_or_eq with
  | inl hl =>
    have := h _ _ (heq ▸ hl)
    simp_rw [Equiv.apply_symm_apply] at this
    exact hlt.not_lt this
  | inr he =>
    apply C.valid _ (heq ▸ he).symm
    obtain ⟨u, v, _, h2, h3⟩ := (map_adj ..).mp hadj
    rw [← h2, ← h3]
    simpa



end withN
section withEncodable
open Encodable

/-- The SimpleGraph ℕ formed from a SimpleGraph β given by permuting β by π and then encoding in ℕ-/
abbrev label {β : Type*} [Encodable β] (H : SimpleGraph β) (π : β ≃ β) : SimpleGraph ℕ :=
    H.map (π.toEmbedding.trans (encode' β))

@[simp]
lemma label_adj {β : Type*} [Encodable β] {H : SimpleGraph β} {π : β ≃ β} {a b : β} :
    (H.label π).Adj (encode (π a)) (encode (π b)) ↔ H.Adj a b :=
  ⟨fun _ ↦ by simp_all [encode'], fun h ↦ by use a, b, h; simp [encode']⟩

lemma label_mem_decode₂_of_adj {β : Type*} [Encodable β] {H : SimpleGraph β} {π : β ≃ β} {m n : ℕ}
  (ha : (H.label π).Adj m n) : ∃ c, c ∈ decode₂ β m   :=by
  rw [map_adj] at ha
  obtain ⟨a, b, h, ha, hb⟩ := ha
  use (π a)
  exact mem_decode₂.mpr ha


@[simp]
lemma label_adj' {β : Type*} [Encodable β] {H : SimpleGraph β} {π : β ≃ β} {m n : ℕ} {a b : β}
(ha : a ∈ decode₂ β m ) (hb : b ∈ decode₂ β n) :
    (H.label π).Adj m n ↔ H.Adj (π.symm a) (π.symm b) := by
  simp only [map_adj, encode', Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
    Function.Embedding.coeFn_mk]
  constructor
  · intro ⟨u,v,hu⟩
    rw [mem_decode₂] at ha hb
    rw [← ha, ← hb ] at hu
    rw [← encode_inj.1 hu.2.1, ← encode_inj.1  hu.2.2]
    simpa using hu.1
  · intro hadj
    use (π.symm a), (π.symm b), hadj
    rw [mem_decode₂] at ha hb
    simpa using ⟨ha,hb⟩

variable {β : Type*} [Encodable β] (H : SimpleGraph β)
/- If H is graph on an Encodable type β with Decidable Adj and π : β ≃ β is a permutation of β
then the graph on ℕ given by permuting β with π and then applying the encoding of β also
has Decidable Adj -/
instance instDecidableRelMapEncodableEquiv [DecidableRel H.Adj] (π : β ≃ β) :
    DecidableRel (H.label π).Adj := by
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

lemma exists_color_order  (C : H.Coloring ℕ) : Nonempty ({π : β ≃ β // H.ColorOrder C π}) := by
  have e:=equivRangeEncode β
  
  sorry

lemma greedy_le_colorOrder [DecidableRel H.Adj] {C : H.Coloring ℕ} {π : β ≃ β} {n : ℕ} {b : β}
(h : H.ColorOrder C π) (hb : b ∈ decode₂ β n) :
    (H.label π).greedy n ≤ C (π.symm b)  := by
  induction n using Nat.strong_induction_on generalizing b
  rename_i n ih
  by_contra! h'
  obtain ⟨m, hlt, hadj, heq⟩ := (H.label π).greedy_witness h'
  obtain ⟨c, hc⟩ := label_mem_decode₂_of_adj hadj
  cases (ih m hlt hc).lt_or_eq with
  | inl hl =>
    have := h _ _ (heq ▸ hl)
    simp_rw [Equiv.apply_symm_apply] at this
    rw [mem_decode₂] at hb hc
    subst_vars
    apply hlt.not_lt this
  | inr he =>
    apply C.valid _ (heq ▸ he).symm
    obtain ⟨u, v, _, h2, h3⟩ := (map_adj ..).mp hadj
    convert hadj using 1
    rw [label_adj' hc hb]


lemma colorable_iff_greedyColorable [DecidableRel H.Adj] {n : ℕ} :
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
  · intro ⟨f ,_⟩
    use H.GreedyColoring f


def GreedyOrder_ofColoring (C : H.Coloring ℕ) : β ≃ β where
  toFun := fun v => sorry
  invFun := fun v => sorry
  left_inv := fun v => sorry
  right_inv := fun v => sorry

end withEncodable
end SimpleGraph
