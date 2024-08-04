/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Oplax

/-!
# Strong natural transformations

A strong natural transformation is an oplax natural transformation such that each component 2-cell
is an isomorphism.

## Main definitions

* `StrongNatTrans F G` : strong natural transformations between oplax functors `F` and `G`.
* `mkOfOplax η η'` : given an oplax natural transformation `η` such that each component 2-cell
  is an isomorphism, `mkOfOplax` gives the corresponding strong natural transformation.
* `StrongNatTrans.vcomp η θ` : the vertical composition of strong natural transformations `η`
  and `θ`.
* `StrongNatTrans.category F G` : a category structure on pseudofunctors between `F` and `G`,
  where the morphisms are strong natural transformations.

## TODO

After having defined lax functors, we should define 3 different types of strong natural
transformations:
* strong natural transformations between oplax functors (as defined here).
* strong natural transformations between lax functors.
* strong natural transformations between pseudofunctors. From these types of strong natural
  transformations, we can define the underlying natural transformations between the underlying
  oplax resp. lax functors. Many properties can then be inferred from these.

## References
* [Niles Johnson, Donald Yau, *2-Dimensional Categories*](https://arxiv.org/abs/2002.06055)

-/

namespace CategoryTheory

open Category Bicategory

open scoped Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Pseudofunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

/-- A strong natural transformation between oplax functors `F` and `G` is a natural transformation
that is "natural up to 2-isomorphisms".

More precisely, it consists of the following:
* a 1-morphism `η.app a : F.obj a ⟶ G.obj a` for each object `a : B`.
* a 2-isomorphism `η.naturality f : F.map f ≫ app b ⟶ app a ≫ G.map f` for each 1-morphism
`f : a ⟶ b`.
* These 2-isomorphisms satisfy the naturality condition, and preserve the identities and the
compositions modulo some adjustments of domains and codomains of 2-morphisms.
-/
structure StrongNatTrans (F G : Pseudofunctor B C) where
  /-- The component 1-morphism. -/
  app (a : B) : F.obj a ⟶ G.obj a
  /-- The 2-isomorphism underlying the strong naturality constraint. -/
  naturality {a b : B} (f : a ⟶ b) : F.map f ≫ app b ≅ app a ≫ G.map f
  /-- Naturality of the strong naturality constraint. -/
  naturality_naturality :
    ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
      F.map₂ η ▷ app b ≫ (naturality g).hom = (naturality f).hom ≫ app a ◁ G.map₂ η := by
    aesop_cat
  /-- The strong naturality constraint is compatible with the oplax unity constraint. -/
  naturality_id :
    ∀ a : B,
      (naturality (𝟙 a)).hom ≫ app a ◁ (G.mapId a).hom =
        (F.mapId a).hom ▷ app a ≫ (λ_ (app a)).hom ≫ (ρ_ (app a)).inv := by
    aesop_cat
  /-- The strong naturality constraint is compatible with the oplax functoriality constraint. -/
  naturality_comp :
    ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
      (naturality (f ≫ g)).hom ≫ app a ◁ (G.mapComp f g).hom =
        (F.mapComp f g).hom ▷ app c ≫ (α_ _ _ _).hom ≫ F.map f ◁ (naturality g).hom ≫
        (α_ _ _ _).inv ≫ (naturality f).hom ▷ G.map g ≫ (α_ _ _ _).hom := by
    aesop_cat

attribute [reassoc (attr := simp)] StrongNatTrans.naturality_naturality
  StrongNatTrans.naturality_id StrongNatTrans.naturality_comp

namespace StrongNatTrans

section

variable (F : Pseudofunctor B C)

/-- The identity strong natural transformation. -/
@[simps!]
def id : StrongNatTrans F F where
  app a := 𝟙 (F.obj a)
  naturality {a b} f := (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm

instance : Inhabited (StrongNatTrans F F) :=
  ⟨id F⟩

/-- The underlying oplax natural transformation of a strong natural transformation. -/
@[simps]
def toStrongOplax {F G : Pseudofunctor B C} (η : StrongNatTrans F G) :
    OplaxFunctor.StrongNatTrans F.toOplax G.toOplax where
  app := η.app
  naturality f := (η.naturality f)

@[simp]
lemma id.toOplax : (id F).toStrongOplax = OplaxFunctor.StrongNatTrans.id F.toOplax :=
  rfl


variable {F} {G H : Pseudofunctor B C} (η : StrongNatTrans F G) (θ : StrongNatTrans G H)

section

variable {a b c : B} {a' : C}

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_naturality (f : a' ⟶ G.obj a) {g h : a ⟶ b} (β : g ⟶ h) :
    f ◁ G.map₂ β ▷ θ.app b ≫ f ◁ (θ.naturality h).hom =
      f ◁ (θ.naturality g).hom ≫ f ◁ θ.app a ◁ H.map₂ β :=
  θ.toStrongOplax.whiskerLeft_naturality_naturality _ _

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_naturality {f g : a ⟶ b} (β : f ⟶ g) (h : G.obj b ⟶ a') :
    F.map₂ β ▷ η.app b ▷ h ≫ (η.naturality g).hom ▷ h =
      (η.naturality f).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ G.map₂ β ▷ h ≫ (α_ _ _ _).inv :=
  η.toStrongOplax.whiskerRight_naturality_naturality _ _

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_comp (f : a' ⟶ G.obj a) (g : a ⟶ b) (h : b ⟶ c) :
    f ◁ (θ.naturality (g ≫ h)).hom ≫ f ◁ θ.app a ◁ (H.mapComp g h).hom =
      f ◁ (G.mapComp g h).hom ▷ θ.app c ≫
        f ◁ (α_ _ _ _).hom ≫
          f ◁ G.map g ◁ (θ.naturality h).hom ≫
            f ◁ (α_ _ _ _).inv ≫ f ◁ (θ.naturality g).hom ▷ H.map h ≫ f ◁ (α_ _ _ _).hom :=
  θ.toStrongOplax.whiskerLeft_naturality_comp _ _ _

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_comp (f : a ⟶ b) (g : b ⟶ c) (h : G.obj c ⟶ a') :
    (η.naturality (f ≫ g)).hom ▷ h ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapComp f g).hom ▷ h =
      (F.mapComp f g).hom ▷ η.app c ▷ h ≫
        (α_ _ _ _).hom ▷ h ≫
          (α_ _ _ _).hom ≫
            F.map f ◁ (η.naturality g).hom ▷ h ≫
              (α_ _ _ _).inv ≫
                (α_ _ _ _).inv ▷ h ≫
                 (η.naturality f).hom ▷ G.map g ▷ h ≫ (α_ _ _ _).hom ▷ h ≫ (α_ _ _ _).hom :=
  η.toStrongOplax.whiskerRight_naturality_comp _ _ _

@[reassoc (attr := simp)]
theorem whiskerLeft_naturality_id (f : a' ⟶ G.obj a) :
    f ◁ (θ.naturality (𝟙 a)).hom ≫ f ◁ θ.app a ◁ (H.mapId a).hom =
      f ◁ (G.mapId a).hom ▷ θ.app a ≫ f ◁ (λ_ (θ.app a)).hom ≫ f ◁ (ρ_ (θ.app a)).inv :=
  θ.toStrongOplax.whiskerLeft_naturality_id _

@[reassoc (attr := simp)]
theorem whiskerRight_naturality_id (f : G.obj a ⟶ a') :
    (η.naturality (𝟙 a)).hom ▷ f ≫ (α_ _ _ _).hom ≫ η.app a ◁ (G.mapId a).hom ▷ f =
    (F.mapId a).hom ▷ η.app a ▷ f ≫ (λ_ (η.app a)).hom ▷ f ≫ (ρ_ (η.app a)).inv ▷ f ≫
    (α_ _ _ _).hom :=
  η.toStrongOplax.whiskerRight_naturality_id _

end

-- TODO: add mk from Oplax and specialize to get this one?!
/-- Vertical composition of strong natural transformations. -/
@[simps!]
def vcomp (η : StrongNatTrans F G) (θ : StrongNatTrans G H) : StrongNatTrans F H where
  app a := η.app a ≫ θ.app a
  naturality {a b} f :=
    (α_ _ _ _).symm ≪≫ whiskerRightIso (η.naturality f) (θ.app b) ≪≫
      (α_ _ _ _) ≪≫ whiskerLeftIso (η.app a) (θ.naturality f) ≪≫ (α_ _ _ _).symm
  naturality_comp {a b c} f g := by
    sorry

end

end StrongNatTrans

variable (B C)

@[simps id comp]
instance categoryStruct : CategoryStruct (Pseudofunctor B C) where
  Hom F G := StrongNatTrans F G
  id F := StrongNatTrans.id F
  comp := StrongNatTrans.vcomp

end Pseudofunctor

end CategoryTheory
