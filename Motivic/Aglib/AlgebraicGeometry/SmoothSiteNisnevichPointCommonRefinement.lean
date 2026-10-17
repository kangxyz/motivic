/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPointSections

/-!
# Actual common pointed Nisnevich neighborhoods

Every arrow in the original pointed-neighborhood index is étale and induces
an isomorphism on residue fields at its distinguished center. Two neighborhoods
have a common neighborhood on their literal scheme pullback. Its chosen point
is the pullback lift of their original canonical residue-field points.

The comparison with the existing smooth-site étale pullback is the identity
on the underlying scheme. This geometric consumer introduces no new point,
stalk, or cofiltered-colimit framework, and is not a standalone upstream leaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.SmoothSite.NisnevichNeighborhood

variable {S : Scheme.{u}} {X : SmoothSite S} {x : X.left}

/-- The structural arrow of an indexed neighborhood is étale. -/
instance etale_toBase (N : NisnevichNeighborhood X x) : Etale N.toBase.left :=
  inferInstanceAs (Etale N.obj.obj.hom)

/-- The smooth-site map of an actual pointed refinement preserves its center. -/
@[simp]
theorem map_center {M N : NisnevichNeighborhood X x} (q : M ⟶ N) :
    ((nisnevichNeighborhoodFunctor X x).map q).left M.center = N.center :=
  refinement_center q

/-- Refinement maps are actual étale scheme morphisms, not merely index arrows. -/
instance etale_map {M N : NisnevichNeighborhood X x} (q : M ⟶ N) :
    Etale ((nisnevichNeighborhoodFunctor X x).map q).left :=
  inferInstanceAs (Etale q.hom.hom.left)

/-- A pointed refinement preserves the residue field at its actual center. -/
instance isIso_residueFieldMap_map_center {M N : NisnevichNeighborhood X x} (q : M ⟶ N) :
    IsIso (((nisnevichNeighborhoodFunctor X x).map q).left.residueFieldMap M.center) := by
  let f := (nisnevichNeighborhoodFunctor X x).map q
  have hcomp : f.left ≫ N.toBase.left = M.toBase.left :=
    congrArg (fun g ↦ g.left) (map_toBase q)
  have : IsIso (N.toBase.left.residueFieldMap (f.left M.center)) := by
    change IsIso (N.toBase.left.residueFieldMap
      (((nisnevichNeighborhoodFunctor X x).map q).left M.center))
    rw [map_center q]
    infer_instance
  apply (isIso_comp_left_iff (N.toBase.left.residueFieldMap (f.left M.center))
    (f.left.residueFieldMap M.center)).mp
  rw [← Scheme.residueFieldMap_comp]
  exact (congrArg (fun g : M.obj.obj.left ⟶ X.left ↦
    IsIso (g.residueFieldMap M.center)) hcomp).mpr inferInstance

/-- The chosen canonical field-valued point of the literal common pullback. -/
def commonPoint (N M : NisnevichNeighborhood X x) :
    Spec (X.left.residueField x) ⟶ pullback N.toBase.left M.toBase.left :=
  pullback.lift N.obj.val.left M.obj.val.left
    ((Over.w N.obj.val).trans (Over.w M.obj.val).symm)

/-- The literal pullback with its original canonical field-valued point is an
object of the same pointed-neighborhood index. -/
def common (N M : NisnevichNeighborhood X x) : NisnevichNeighborhood X x :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk
      (pullback.snd N.toBase.left M.toBase.left ≫ M.toBase.left))
    (Over.homMk (commonPoint N M) (by
      change commonPoint N M ≫
        (pullback.snd N.toBase.left M.toBase.left ≫ M.toBase.left) = _
      rw [← Category.assoc, commonPoint, pullback.lift_snd]
      exact Over.w M.obj.val)),
    by
      change smoothSeparatedFiniteType
        ((pullback.snd N.toBase.left M.toBase.left ≫ M.toBase.left) ≫ X.hom)
      rw [Category.assoc, MorphismProperty.Over.w]
      exact (etalePullback N.toBase M.toBase).prop⟩

@[simp]
theorem common_left (N M : NisnevichNeighborhood X x) :
    (common N M).obj.obj.left = pullback N.toBase.left M.toBase.left := rfl

@[simp]
theorem common_point (N M : NisnevichNeighborhood X x) :
    (common N M).obj.val.left = commonPoint N M := rfl

@[simp]
theorem common_center (N M : NisnevichNeighborhood X x) :
    (common N M).center = commonPoint N M default := rfl

/-- The first literal pullback projection, as a morphism in the original index. -/
def commonFst (N M : NisnevichNeighborhood X x) : common N M ⟶ N :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk (pullback.fst N.toBase.left M.toBase.left)
      (pullback.condition)) (by
      apply Over.OverMorphism.ext
      exact pullback.lift_fst _ _ _))

/-- The second literal pullback projection, as a morphism in the original index. -/
def commonSnd (N M : NisnevichNeighborhood X x) : common N M ⟶ M :=
  ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk (pullback.snd N.toBase.left M.toBase.left) rfl) (by
      apply Over.OverMorphism.ext
      exact pullback.lift_snd _ _ _))

/-- The original-index object is the actual smooth-site pullback, up to only
reassociation of its structure map; the scheme comparison is the identity. -/
def commonIso (N M : NisnevichNeighborhood X x) :
    (nisnevichNeighborhoodFunctor X x).obj (common N M) ≅
      etalePullback N.toBase M.toBase :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change (𝟙 _) ≫ (pullback.snd N.toBase.left M.toBase.left ≫
      (M.obj.obj.hom ≫ X.hom)) =
        (pullback.snd N.toBase.left M.toBase.left ≫ M.obj.obj.hom) ≫ X.hom
    simp only [Category.id_comp, Category.assoc])

@[simp]
theorem commonIso_hom_left (N M : NisnevichNeighborhood X x) :
    (commonIso N M).hom.left = 𝟙 _ := rfl

@[simp]
theorem commonIso_inv_left (N M : NisnevichNeighborhood X x) :
    (commonIso N M).inv.left = 𝟙 _ := rfl

@[simp]
theorem map_commonFst (N M : NisnevichNeighborhood X x) :
    (nisnevichNeighborhoodFunctor X x).map (commonFst N M) =
      (commonIso N M).hom ≫ etalePullbackFst N.toBase M.toBase := by
  apply MorphismProperty.Over.Hom.ext
  exact (Category.id_comp _).symm

@[simp]
theorem map_commonSnd (N M : NisnevichNeighborhood X x) :
    (nisnevichNeighborhoodFunctor X x).map (commonSnd N M) =
      (commonIso N M).hom ≫ etalePullbackSnd N.toBase M.toBase := by
  apply MorphismProperty.Over.Hom.ext
  exact (Category.id_comp _).symm

end Motivic.SmoothSite.NisnevichNeighborhood
