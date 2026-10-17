/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichCommonGerms
public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteBranchLift

/-!
# Original germs at designated points of a Čech pullback

A point above both designated neighborhood centers is the canonical residue-field
point. Thus equality in the original point-fiber colimit supplies the actual
matching-germ condition there, without closedness or acyclicity assumptions.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace Motivic.SmoothSite
variable {S : Scheme.{u}} {X : SmoothSite S} {x : X.left}

namespace NisnevichNeighborhood

/-- The first projection of the actual common point is the first designated center. -/
theorem commonPoint_fst (N M : NisnevichNeighborhood X x) :
    (pullback.fst N.toBase.left M.toBase.left) (commonPoint N M default) = N.center := by
  have h := congrArg (fun f : Spec (X.left.residueField x) ⟶ N.obj.obj.left =>
    f default) (pullback.lift_fst N.obj.val.left M.obj.val.left
      ((Over.w N.obj.val).trans (Over.w M.obj.val).symm))
  exact h

/-- The second projection of the actual common point is the second designated center. -/
theorem commonPoint_snd (N M : NisnevichNeighborhood X x) :
    (pullback.snd N.toBase.left M.toBase.left) (commonPoint N M default) = M.center := by
  have h := congrArg (fun f : Spec (X.left.residueField x) ⟶ M.obj.obj.left =>
    f default) (pullback.lift_snd N.obj.val.left M.obj.val.left
      ((Over.w N.obj.val).trans (Over.w M.obj.val).symm))
  exact h

/-- Both designated projections determine the point, since the displayed residue
map of the second neighborhood is an isomorphism. -/
theorem eq_commonPoint_of_projections (N M : NisnevichNeighborhood X x)
    (w : (etalePullback N.toBase M.toBase).left)
    (hfst : (etalePullbackFst N.toBase M.toBase).left w = N.center)
    (hsnd : (etalePullbackSnd N.toBase M.toBase).left w = M.center) :
    w = commonPoint N M default := by
  exact Scheme.Hom.pullback_point_ext_of_residueFieldIso N.toBase.left M.toBase.left
    M.center w (commonPoint N M default) hsnd (commonPoint_snd N M)
    (hfst.trans (commonPoint_fst N M).symm)

end NisnevichNeighborhood

variable [IsAffine S]

/-- Equal original Nisnevich germs match at every actual Čech point whose two
projections are the designated centers, not merely at a newly chosen stalk. -/
theorem literal_cech_germs_eq_at_designated_point
    (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
    (N M : NisnevichNeighborhood X x)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj N)))
    (t : F.obj (op ((nisnevichNeighborhoodFunctor X x).obj M)))
    (hst : (nisnevichPointFiberCocone X x F).ι.app (op N) s =
      (nisnevichPointFiberCocone X x F).ι.app (op M) t)
    (w : (etalePullback N.toBase M.toBase).left)
    (hfst : (etalePullbackFst N.toBase M.toBase).left w = N.center)
    (hsnd : (etalePullbackSnd N.toBase M.toBase).left w = M.center) :
    sectionToNisnevichPoint F (etalePullback N.toBase M.toBase) w
        (F.map (etalePullbackFst N.toBase M.toBase).op s) =
      sectionToNisnevichPoint F (etalePullback N.toBase M.toBase) w
        (F.map (etalePullbackSnd N.toBase M.toBase).op t) := by
  rw [NisnevichNeighborhood.eq_commonPoint_of_projections N M w hfst hsnd]
  exact literal_cech_germs_eq F N M s t hst

end Motivic.SmoothSite
