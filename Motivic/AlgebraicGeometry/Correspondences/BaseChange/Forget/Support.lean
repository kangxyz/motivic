/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Admissibility
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.CorrespondenceCycle
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Original correspondence supports after forgetting a separated base

The product over the original base includes as a closed subscheme in the
product over a separated smaller base. Pushing the original integral support
through this inclusion preserves its source projection, not its scalar degree.
For an unramified finite-type base map the product inclusion is also open.
These constructions do not yet assert preservation of correspondence composition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) (f : X ⟶ T) (g : Y ⟶ T)

/-- The original two projections, now viewed over the smaller base. -/
def forgetBaseProductMap : pullback f g ⟶ pullback (f ≫ r) (g ≫ r) :=
  pullback.map f g (f ≫ r) (g ≫ r) (𝟙 X) (𝟙 Y) r
    (Category.id_comp _).symm (Category.id_comp _).symm

@[reassoc (attr := simp)]
theorem forgetBaseProductMap_fst :
    forgetBaseProductMap r f g ≫ pullback.fst (f ≫ r) (g ≫ r) = pullback.fst f g := by
  simp [forgetBaseProductMap, pullback.map]

@[reassoc (attr := simp)]
theorem forgetBaseProductMap_snd :
    forgetBaseProductMap r f g ≫ pullback.snd (f ≫ r) (g ≫ r) = pullback.snd f g := by
  simp [forgetBaseProductMap, pullback.map]

instance [IsSeparated r] : IsClosedImmersion (forgetBaseProductMap r f g) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g r)
    (inferInstanceAs (IsClosedImmersion (pullback.diagonal r)))

instance [FormallyUnramified r] [LocallyOfFiniteType r] :
    IsOpenImmersion (forgetBaseProductMap r f g) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g r)
    (inferInstanceAs (IsOpenImmersion (pullback.diagonal r)))

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Hom

variable {f g} [IsSeparated r] [IsSeparated g] [LocallyOfFiniteType g]
  [LocallyOfFiniteType r] (A : FiniteCorrespondenceGenerator f g)

/-- The closed image of the original support in the smaller-base product. -/
def forgetBase : FiniteCorrespondenceGenerator (f ≫ r) (g ≫ r) := by
  let C := A.toIntegralClosedSubscheme
  let j := forgetBaseProductMap r f g
  refine ⟨(C.finiteImage j).val, (C.finiteImage j).property, ?_, ?_⟩
  · have : IsFinite ((C.val.subschemeι ≫ j) ≫ pullback.fst (f ≫ r) (g ≫ r)) := by
      change IsFinite ((A.inclusion ≫ forgetBaseProductMap r f g) ≫
        pullback.fst (f ≫ r) (g ≫ r))
      rw [Category.assoc, forgetBaseProductMap_fst]
      exact inferInstanceAs (IsFinite A.projection)
    exact isFinite_image_projection (C.val.subschemeι ≫ j) _
  · change Set.range ((C.val.subschemeι ≫ j).imageι ≫
      pullback.fst (f ≫ r) (g ≫ r)) ∈ _
    rw [range_image_projection, Category.assoc, forgetBaseProductMap_fst]
    exact A.range_projection_mem

/-- Forgetting the base retains exactly the original integral closed image. -/
@[simp]
theorem toIntegralClosedSubscheme_forgetBase :
    (A.forgetBase r).toIntegralClosedSubscheme =
      A.toIntegralClosedSubscheme.finiteImage (forgetBaseProductMap r f g) := rfl

/-- No support component or multiplicity is replaced when forgetting the base. -/
def forgetBaseSupportIso : A.scheme ≅ (A.forgetBase r).scheme := by
  have : IsIso (A.inclusion ≫ forgetBaseProductMap r f g).toImage :=
    IsClosedImmersion.instIsIsoSchemeToImage _
  exact asIso (A.inclusion ≫ forgetBaseProductMap r f g).toImage

@[reassoc (attr := simp)]
theorem forgetBaseSupportIso_hom_inclusion :
    (A.forgetBaseSupportIso r).hom ≫ (A.forgetBase r).inclusion =
      A.inclusion ≫ forgetBaseProductMap r f g :=
  (A.inclusion ≫ forgetBaseProductMap r f g).toImage_imageι

@[reassoc (attr := simp)]
theorem forgetBaseSupportIso_hom_projection :
    (A.forgetBaseSupportIso r).hom ≫ (A.forgetBase r).projection = A.projection := by
  change (A.forgetBaseSupportIso r).hom ≫
    ((A.forgetBase r).inclusion ≫ pullback.fst (f ≫ r) (g ≫ r)) = _
  rw [← Category.assoc, forgetBaseSupportIso_hom_inclusion, Category.assoc,
    forgetBaseProductMap_fst]
  rfl

@[reassoc]
theorem forgetBaseSupportIso_hom_targetProjection :
    (A.forgetBaseSupportIso r).hom ≫ (A.forgetBase r).targetProjection =
      A.targetProjection := by
  change (A.forgetBaseSupportIso r).hom ≫
    ((A.forgetBase r).inclusion ≫ pullback.snd (f ≫ r) (g ≫ r)) = _
  rw [← Category.assoc, forgetBaseSupportIso_hom_inclusion, Category.assoc,
    forgetBaseProductMap_snd]

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence

variable [IsSeparated r] [IsSeparated g] [LocallyOfFiniteType g] [LocallyOfFiniteType r]

/-- The additive map uses the same integer coefficient on each original support. -/
def forgetBase : FiniteCorrespondence f g →+ FiniteCorrespondence (f ≫ r) (g ≫ r) :=
  Finsupp.mapDomain.addMonoidHom (fun A => A.forgetBase r)

@[simp]
theorem forgetBase_single (A : FiniteCorrespondenceGenerator f g) (n : ℤ) :
    forgetBase r f g (Finsupp.single A n) = Finsupp.single (A.forgetBase r) n :=
  Finsupp.mapDomain_single

end FiniteCorrespondence

end Motivic
