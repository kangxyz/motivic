/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Sections
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Normalization
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.CommonRefinement

/-!
# Pullback of smooth-site germs
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v

namespace AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
variable {S : Scheme.{u}} {X Y : SmoothSite S} (f : X ⟶ Y) (x : X.left)

/-- The target neighborhood's original point after the actual residue-field map. -/
def pullbackAlongTargetPoint (N : NisnevichNeighborhood Y (f.left x)) :
    Spec (X.left.residueField x) ⟶ N.obj.obj.left :=
  Spec.map (f.left.residueFieldMap x) ≫ N.obj.val.left

@[reassoc]
theorem pullbackAlongTargetPoint_toBase (N : NisnevichNeighborhood Y (f.left x)) :
    pullbackAlongTargetPoint f x N ≫ N.toBase.left =
      X.left.fromSpecResidueField x ≫ f.left := by
  have hN : N.obj.val.left ≫ N.toBase.left =
      Y.left.fromSpecResidueField (f.left x) := Over.w N.obj.val
  rw [pullbackAlongTargetPoint, Category.assoc, hN]
  exact f.left.SpecMap_residueFieldMap_fromSpecResidueField x

/-- The literal residue-field point of the scheme pullback. -/
def pullbackAlongPoint (N : NisnevichNeighborhood Y (f.left x)) :
    Spec (X.left.residueField x) ⟶ pullback N.toBase.left f.left :=
  pullback.lift (pullbackAlongTargetPoint f x N) (X.left.fromSpecResidueField x)
    (pullbackAlongTargetPoint_toBase f x N)

/-- An actual pointed neighborhood pulled back along an arbitrary smooth-site map. -/
def pullbackAlong (N : NisnevichNeighborhood Y (f.left x)) : NisnevichNeighborhood X x :=
  ⟨Functor.elementsMk _ (Scheme.Etale.mk (pullback.snd N.toBase.left f.left))
    (Over.homMk (pullbackAlongPoint f x N) (pullback.lift_snd _ _ _)),
    by
      change smoothSeparatedFiniteType (pullback.snd N.toBase.left f.left ≫ X.hom)
      exact (etalePullback N.toBase f).prop⟩

/-- The literal projection from the source neighborhood to the target neighborhood. -/
def pullbackAlongToTarget (N : NisnevichNeighborhood Y (f.left x)) :
    (nisnevichNeighborhoodFunctor X x).obj (pullbackAlong f x N) ⟶
      (nisnevichNeighborhoodFunctor Y (f.left x)).obj N :=
  homMk (pullback.fst N.toBase.left f.left) (by
    change pullback.fst N.toBase.left f.left ≫ (N.toBase.left ≫ Y.hom) =
      pullback.snd N.toBase.left f.left ≫ X.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, MorphismProperty.Over.w])

@[reassoc]
theorem pullbackAlongToTarget_toBase (N : NisnevichNeighborhood Y (f.left x)) :
    pullbackAlongToTarget f x N ≫ N.toBase = (pullbackAlong f x N).toBase ≫ f := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.condition

@[simp]
theorem pullbackAlongToTarget_center (N : NisnevichNeighborhood Y (f.left x)) :
    (dsimp% only [nisnevichNeighborhoodFunctor_obj_left]
      (pullbackAlongToTarget f x N).left (pullbackAlong f x N).center) = N.center := by
  have h := congrArg (fun g : Spec (X.left.residueField x) ⟶ N.obj.obj.left => g default)
    (pullback.lift_fst (pullbackAlongTargetPoint f x N)
      (X.left.fromSpecResidueField x) (pullbackAlongTargetPoint_toBase f x N))
  change (pullbackAlongToTarget f x N).left (pullbackAlong f x N).center =
    N.obj.val.left (Spec.map (f.left.residueFieldMap x) default) at h
  have he : Spec.map (f.left.residueFieldMap x) default =
      (default : Spec (Y.left.residueField (f.left x))) := Subsingleton.elim _ _
  exact h.trans (congrArg N.obj.val.left he)

/-- Refinement of actual target neighborhoods induces an actual source refinement. -/
def pullbackAlongMap {N M : NisnevichNeighborhood Y (f.left x)} (q : N ⟶ M) :
    pullbackAlong f x N ⟶ pullbackAlong f x M := by
  let p : pullback N.toBase.left f.left ⟶ pullback M.toBase.left f.left :=
    pullback.lift (pullback.fst N.toBase.left f.left ≫ q.hom.hom.left)
      (pullback.snd N.toBase.left f.left) (by
        rw [Category.assoc]
        have hq : q.hom.hom.left ≫ M.toBase.left = N.toBase.left :=
          MorphismProperty.Over.w q.hom.hom
        rw [hq, pullback.condition])
  refine ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk p (pullback.lift_snd _ _ _)) ?_)
  apply Over.OverMorphism.ext
  change pullbackAlongPoint f x N ≫ p = pullbackAlongPoint f x M
  apply pullback.hom_ext
  · simp only [Category.assoc, p, pullback.lift_fst]
    rw [← Category.assoc, pullbackAlongPoint, pullback.lift_fst,
      pullbackAlongPoint, pullback.lift_fst]
    dsimp only [pullbackAlongTargetPoint]
    rw [Category.assoc, refinement_point]
  · simp only [Category.assoc, p, pullback.lift_snd, pullbackAlongPoint]

@[reassoc]
theorem pullbackAlongMap_toTarget {N M : NisnevichNeighborhood Y (f.left x)}
    (q : N ⟶ M) :
    (nisnevichNeighborhoodFunctor X x).map (pullbackAlongMap f x q) ≫
        pullbackAlongToTarget f x M =
      pullbackAlongToTarget f x N ≫ (nisnevichNeighborhoodFunctor Y (f.left x)).map q := by
  apply MorphismProperty.Over.Hom.ext
  exact pullback.lift_fst _ _ _

end AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] {X Y : SmoothSite S}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}) (f : X ⟶ Y) (x : X.left)
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

/-- Restrict every original target representative on its actual pointed pullback. -/
def originalGermPullbackCocone :
    Cocone ((nisnevichNeighborhoodFunctor Y (f.left x)).op ⋙ F) where
  pt := (nisnevichPointFiberCocone X x F).pt
  ι :=
    { app := fun N => F.map (NisnevichNeighborhood.pullbackAlongToTarget f x N.unop).op ≫
        (nisnevichPointFiberCocone X x F).ι.app (op (NisnevichNeighborhood.pullbackAlong f x
            N.unop))
      naturality := by
        intro N M q
        change F.map ((nisnevichNeighborhoodFunctor Y (f.left x)).map q.unop).op ≫
            (F.map (NisnevichNeighborhood.pullbackAlongToTarget f x M.unop).op ≫
              (nisnevichPointFiberCocone X x F).ι.app (op (NisnevichNeighborhood.pullbackAlong f x
                  M.unop))) =
          (F.map (NisnevichNeighborhood.pullbackAlongToTarget f x N.unop).op ≫
            (nisnevichPointFiberCocone X x F).ι.app (op (NisnevichNeighborhood.pullbackAlong f x
                N.unop))) ≫ 𝟙 _
        rw [Category.comp_id, ← Category.assoc, ← F.map_comp, ← op_comp,
          ← NisnevichNeighborhood.pullbackAlongMap_toTarget, op_comp, F.map_comp, Category.assoc]
        have h := (nisnevichPointFiberCocone X x F).w (NisnevichNeighborhood.pullbackAlongMap f x
            q.unop).op
        exact congrArg (fun t => F.map (NisnevichNeighborhood.pullbackAlongToTarget f x N.unop).op ≫
            t) h }

/-- Pullback of original Nisnevich germs, induced by the existing fiber colimit.
No transfer, sheaf, or compatibility law is used in this construction. -/
def originalGermPullback : (nisnevichPointFiberCocone Y (f.left x) F).pt ⟶
    (nisnevichPointFiberCocone X x F).pt :=
  (isColimitNisnevichPointFiberCocone Y (f.left x) F).desc (originalGermPullbackCocone F f x)

@[reassoc]
theorem originalGermPullback_ι (N : NisnevichNeighborhood Y (f.left x)) :
    (nisnevichPointFiberCocone Y (f.left x) F).ι.app (op N) ≫ originalGermPullback F f x =
      F.map (NisnevichNeighborhood.pullbackAlongToTarget f x N).op ≫
        (nisnevichPointFiberCocone X x F).ι.app (op (NisnevichNeighborhood.pullbackAlong f x N)) :=
  (isColimitNisnevichPointFiberCocone Y (f.left x) F).fac (originalGermPullbackCocone F f x) _

/-- The colimit-induced germ pullback agrees with actual restriction on sections. -/
@[reassoc]
theorem sectionToNisnevichPoint_originalGermPullback :
    sectionToNisnevichPoint F Y (f.left x) ≫ originalGermPullback F f x =
      F.map f.op ≫ sectionToNisnevichPoint F X x := by
  rw [sectionToNisnevichPoint, Category.assoc, originalGermPullback_ι,
    ← Category.assoc, ← F.map_comp, ← op_comp, NisnevichNeighborhood.pullbackAlongToTarget_toBase,
    op_comp, F.map_comp, Category.assoc, restriction_sectionToNisnevichPoint]

end AlgebraicGeometry.Scheme.SmoothSite
