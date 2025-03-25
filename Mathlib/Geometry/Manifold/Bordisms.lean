/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Instances.Real

/-!
## (Unoriented) bordism theory

This file defines the beginnings of unoriented bordism theory. We define singular n-manifolds,
the building blocks of unoriented bordism groups. Future pull requests will define bordisms
and the bordism groups of a topological space, and prove it these are abelian groups.

The basic notion of bordism theory is that of a bordism between smooth manifolds.
Two compact smooth `n`-dimensional manifolds `M` and `N` are **bordant** if there exists a smooth
**bordism** between them: this is a compact `n+1`-dimensional manifold `W` whose boundary is
(diffeomorphic to) the disjoint union `M ⊕ N`. Being bordant is an equivalence relation
(transitivity follows from the collar neighbourhood theorem). The set of equivalence classes has an
abelian group structure, with the group operation given as disjoint union of manifolds,
and is called the `n`-th (unoriented) bordism group.

This construction can be generalised one step further, to produce an extraordinary homology theory.
Given a topological space `X`, a **singular `n`-manifold** on `X` is a closed `n`-dimensional smooth
manifold `M` together with a continuous map `M → F`. (The word *singular* does not refer to
singularities, but is by analogy to singular `n`-chains in the definition of singular homology.)

Given two singular `n`-manifolds `s` and `t`, an (oriented) bordism between `s` and `t` is a compact
smooth `n+1`-dimensional manifold `W` whose boundary is (diffeomorphic to) the disjoint union
of `s` and `t`, together with a map `W → X` which restricts to the maps on `s` and `t`.
We call `s` and `t` bordant if there exists a bordism between them: again, this defines an
equivalence relation. The `n`-th bordism group of `X` is the set of bordism classes of singular
`n`-manifolds on`X`. If `X` is a single point, this recovers the bordism groups from the preceding
paragraph.

These absolute bordism groups can be generalised further to relative bordism groups, for each
topological pair `(X, A)`; in fact, these define an extra-ordinary homology theory.

## Main definitions

- **SingularNManifold X k I**: a singular manifold on a topological space `X`, is a pair `(M, f)` of
  a closed `C^k`-manifold manifold `M` modelled on `I` together with a continuous map `M → X`.
  We don't assume `M` to be modelled on `ℝⁿ`, but add the model topological space `H`,
  the vector space `E` and the model with corners `I` as type parameters.
  To define a disjoint unions of singular `n`-manifolds, we require their domains to be manifolds
  over the same model with corners: this is why we make the model explicit.

## Main results

- `SingularNManifold.map`: a map `X → Y` of topological spaces induces a map between the spaces
  of singular `n`-manifolds. This will be used to define functoriality of bordism groups.
- `SingularNManifold.comap`: if `(N, f)` is a singular `n`-manifold on `X`
  and `φ: M → N` is continuous, the `comap` of `(N, f)` and `φ`
  is the induced singular `n`-manifold `(M, f ∘ φ)` on `X`.
- `SingularNManifold.empty`: the empty set `M`, viewed as an `n`-manifold,
  as a singular `n`-manifold over any space `X`.
- `SingularNManifold.toPUnit`: an `n`-dimensional manifold induces a singular `n`-manifold
  on the one-point space.
- `SingularNManifold.prod`: the product of a singular `n`-manifold and a singular `m`-manifold
  on the one-point space, is a singular `n+m`-manifold on the one-point space.
- `SingularNManifold.sum`: the disjoint union of two singular `n`-manifolds
  is a singular `n`-manifold.

## Implementation notes

* We choose a bundled design for singular `n`-manifolds (and also for bordisms): to construct the
  group structure on the set of bordism classes, having that be a type is useful.
* The underlying model with corners is a type parameter, as defining a disjoint union of singular
  `n`-manifolds requires their domains to be manifolds over the same model with corners.
  Thus, either we restrict to manifolds modelled over `𝓡n` (which we prefer not to),
  or the model must be a type parameter.
* Having `SingularNManifold` contain the type `M` as explicit structure field is not ideal,
  as this adds a universe parameter to the structure. However, this is the best solution we found:
  we generally cannot have `M` live in the same universe as `X` (a common case is `X` being
  `PUnit`), and determining the universe of `M` from the universes of `E` and `H` would make
  `SingularNManifold.map` painful to state (as that would require `ULift`ing `M`).

## TODO
- define bordisms and prove basic constructions (e.g. reflexivity, symmetry, transitivity)
  and operations (e.g. disjoint union, sum with the empty set)
- define the bordism relation and prove it is an equivalence relation
- define the unoriented bordism group (the set of bordism classes) and prove it is an abelian group
- for bordisms on a one-point space, define multiplication and prove the bordism ring structure
- define relative bordism groups (generalising the previous three points)
- prove that relative unoriented bordism groups define an extraordinary homology theory

## Tags

singular n-manifold, bordism, bordism group
-/

open scoped Manifold
open Module Set

suppress_compilation

/-- A **singular `n`-manifold** on a topological space `X`, for `n ∈ ℕ`, is a pair `(M, f)`
of a closed `n`-dimensional `C^k` manifold `M` together with a continuous map `M → X`.
We assume that `M` is a manifold over the pair `(E, H)` with model `I`.

In practice, one commonly wants to take `k=∞` (as then e.g. the intersection form is a powerful tool
to compute bordism groups; for the definition, this makes no difference.)

This is parametrised on the universe `M` lives in; ensure `u` is the first universe argument. -/
structure SingularNManifold.{u} (X : Type*) [TopologicalSpace X] (k : WithTop ℕ∞)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) where
  /-- The manifold `M` of a singular `n`-manifold `(M, f)` -/
  M : Type u
  /-- The manifold `M` is a topological space. -/
  [topSpaceM : TopologicalSpace M]
  /-- The manifold `M` is a charted space over `H`. -/
  [chartedSpace : ChartedSpace H M]
  /-- `M` is a `C^k` manifold. -/
  [isManifold : IsManifold I k M]
  [compactSpace : CompactSpace M]
  [boundaryless : BoundarylessManifold I M]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M, f)` on `X` -/
  f : M → X
  hf : Continuous f

namespace SingularNManifold

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {k : WithTop ℕ∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I k M] [CompactSpace M] [BoundarylessManifold I M]

instance {s : SingularNManifold X k I} : TopologicalSpace s.M := s.topSpaceM

instance {s : SingularNManifold X k I} : ChartedSpace H s.M := s.chartedSpace

instance {s : SingularNManifold X k I} : IsManifold I k s.M := s.isManifold

instance {s : SingularNManifold X k I} : CompactSpace s.M := s.compactSpace

instance {s : SingularNManifold X k I} : BoundarylessManifold I s.M := s.boundaryless

/-- A map of topological spaces induces a corresponding map of singular n-manifolds. -/
-- This is part of proving functoriality of the bordism groups.
def map.{u} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {k : WithTop ℕ∞}
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} (s : SingularNManifold.{u} X k I)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold.{u} Y k I where
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp, mfld_simps]
lemma map_f (s : SingularNManifold X k I) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).f = φ ∘ s.f :=
  rfl

@[simp, mfld_simps]
lemma map_M (s : SingularNManifold X k I) {φ : X → Y} (hφ : Continuous φ) :
    (s.map hφ).M = s.M :=
  rfl

lemma map_comp (s : SingularNManifold X k I)
    {φ : X → Y} {ψ : Y → Z} (hφ : Continuous φ) (hψ : Continuous ψ) :
    ((s.map hφ).map hψ).f = (ψ ∘ φ) ∘ s.f := by
  simp [Function.comp_def]

variable {E' E'' E''' H' H'' H''' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable (M I) in
/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
noncomputable def refl : SingularNManifold M k I where
  M := M
  f := id
  hf := continuous_id

/-- If `(N, f)` is a singular `n`-manifold on `X` and `M` another `n`-dimensional manifold,
a continuous map `φ : M → N` induces a singular `n`-manifold structure `(M, f ∘ φ)` on `X`. -/
noncomputable def comap (s : SingularNManifold X k I)
    {φ : M → s.M} (hφ : Continuous φ) : SingularNManifold X k I where
  M := M
  f := s.f ∘ φ
  hf := s.hf.comp hφ

@[simp, mfld_simps]
lemma comap_M (s : SingularNManifold X k I) {φ : M → s.M} (hφ : Continuous φ) :
    (s.comap hφ).M = M := by
  rfl

@[simp, mfld_simps]
lemma comap_f (s : SingularNManifold X k I) {φ : M → s.M} (hφ : Continuous φ) :
    (s.comap hφ).f = s.f ∘ φ :=
  rfl

variable (X) in
/-- The canonical singular `n`-manifold associated to the empty set (seen as an `n`-dimensional
manifold, i.e. modelled on an `n`-dimensional space). -/
def empty.{u} (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I k M] [IsEmpty M] : SingularNManifold X k I where
  M := M
  f x := (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim

omit [CompactSpace M] [BoundarylessManifold I M] in
@[simp, mfld_simps]
lemma empty_M [IsEmpty M] : (empty X M I (k := k)).M = M := rfl

instance [IsEmpty M] : IsEmpty (SingularNManifold.empty X M I (k := k)).M := by
  unfold SingularNManifold.empty
  infer_instance

variable (M I) in
/-- An `n`-dimensional manifold induces a singular `n`-manifold on the one-point space. -/
def toPUnit : SingularNManifold PUnit k I where
  M := M
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

variable {I' : ModelWithCorners ℝ E' H'} [FiniteDimensional ℝ E']

/-- The product of a singular `n`- and a singular `m`-manifold into a one-point space
is a singular `n+m`-manifold. -/
-- FUTURE: prove that this observation induces a commutative ring structure
-- on the unoriented bordism group `Ω_n^O = Ω_n^O(pt)`.
def prod (s : SingularNManifold PUnit k I) (t : SingularNManifold PUnit k I') :
    SingularNManifold PUnit k (I.prod I') where
  M := s.M × t.M
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

variable (s t : SingularNManifold X k I)

/-- The disjoint union of two singular `n`-manifolds on `X` is a singular `n`-manifold on `X`. -/
-- We need to choose a model space for the disjoint union (as a priori `s` and `t` could be
-- modelled on very different spaces: for simplicity, we choose `ℝ^n`; all real work is contained
-- in the two instances above.
def sum (s t : SingularNManifold X k I) : SingularNManifold X k I where
  M := s.M ⊕ t.M
  f := Sum.elim s.f t.f
  hf := s.hf.sumElim t.hf

@[simp, mfld_simps]
lemma sum_M (s t : SingularNManifold X k I) : (s.sum t).M = (s.M ⊕ t.M) := rfl

@[simp, mfld_simps]
lemma sum_f (s t : SingularNManifold X k I) : (s.sum t).f = Sum.elim s.f t.f := rfl

end SingularNManifold
