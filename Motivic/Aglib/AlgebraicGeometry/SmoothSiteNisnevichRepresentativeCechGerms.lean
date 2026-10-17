/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichDesignatedCechGerms
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichGermRestriction
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichFiniteSections

/-!
# Čech matching for representatives of original germ tuples

Representatives may be chosen at different target points. A designated Čech
point forces their target labels to coincide, so they represent the same entry
of the original tuple of point-fiber classes.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u v
namespace Motivic.SmoothSite
variable {S : Scheme.{u}} [IsAffine S] {Y : SmoothSite S}
  (F : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})

/-- Every element of the original point fiber has an actual pointed-neighborhood
section representative, by the original filtered-colimit universal property. -/
theorem exists_original_germ_representative (y : Y.left)
    (a : (nisnevichPointFiberCocone Y y F).pt) :
    ∃ (N : NisnevichNeighborhood Y y)
      (s : F.obj (op ((nisnevichNeighborhoodFunctor Y y).obj N))),
      (nisnevichPointFiberCocone Y y F).ι.app (op N) s = a := by
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, max (u + 1) v, u, max (u + 1) v} _
  obtain ⟨N, s, hs⟩ := Concrete.isColimit_exists_rep _
    (isColimitNisnevichPointFiberCocone Y y F) a
  exact ⟨N.unop, s, hs⟩

/-- At a designated Čech point, two representatives of the same original germ
tuple agree. Equality of their target labels is proved from the actual projections. -/
theorem representative_pair_cech_germs_eq
    (a : ∀ y : Y.left, (nisnevichPointFiberCocone Y y F).pt)
    {y z : Y.left} (N : NisnevichNeighborhood Y y) (M : NisnevichNeighborhood Y z)
    (s : F.obj (op ((nisnevichNeighborhoodFunctor Y y).obj N)))
    (t : F.obj (op ((nisnevichNeighborhoodFunctor Y z).obj M)))
    (hs : (nisnevichPointFiberCocone Y y F).ι.app (op N) s = a y)
    (ht : (nisnevichPointFiberCocone Y z F).ι.app (op M) t = a z)
    (w : (etalePullback N.toBase M.toBase).left)
    (hfst : (etalePullbackFst N.toBase M.toBase).left w = N.center)
    (hsnd : (etalePullbackSnd N.toBase M.toBase).left w = M.center) :
    sectionToNisnevichPoint F (etalePullback N.toBase M.toBase) w
        (F.map (etalePullbackFst N.toBase M.toBase).op s) =
      sectionToNisnevichPoint F (etalePullback N.toBase M.toBase) w
        (F.map (etalePullbackSnd N.toBase M.toBase).op t) := by
  have hyz : y = z := by
    have hw := congrArg (fun f : (pullback N.toBase.left M.toBase.left) ⟶ Y.left =>
      f w) (pullback.condition (f := N.toBase.left) (g := M.toBase.left))
    change N.toBase.left ((etalePullbackFst N.toBase M.toBase).left w) =
      M.toBase.left ((etalePullbackSnd N.toBase M.toBase).left w) at hw
    simpa only [hfst, hsnd, N.toBase_center, M.toBase_center] using hw
  subst z
  exact literal_cech_germs_eq_at_designated_point F N M s t (hs.trans ht.symm) w hfst hsnd

end Motivic.SmoothSite
