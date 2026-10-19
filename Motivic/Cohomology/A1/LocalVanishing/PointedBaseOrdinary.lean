/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.PointLocallyZero
public import Motivic.Cohomology.A1.LocalVanishing.Cylinder.OrdinaryComparison
public import Motivic.Cohomology.A1.LocalVanishing.Puncture.PointColimit
public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.LocalTriviality

/-! # Positive original ordinary cohomology has zero actual base-neighborhood germs -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]

/-- The original big-site base-neighborhood diagram is the actual small-site point diagram. -/
def pointedBaseOrdinaryIso (n : ℕ) :
    pointedBaseValues R Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F n) ≅
      (Functor.Elements.π Φ.fiber).op ⋙
        LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (nisnevichTopology X.left) ((restrict X AddCommGrpCat).obj F) n :=
  NatIso.ofComponents (fun V =>
    (cohomologyRestrictionEquiv X F n V.unop.obj).toAddCommGrpIso) (by
    intro V W f
    ext x
    exact cohomologyRestrictionEquiv_restriction F n
      ((Functor.Elements.π Φ.fiber).map f.unop) x)

/-- Positive base germs vanish by actual ordinary local effacement and the actual point axiom. -/
theorem pointedBaseColimit_isZero_succ (n : ℕ) :
    IsZero (colimit (pointedBaseValues R Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F (n + 1)))) := by
  have h := Φ.presheafFiber_isZero_of_locally_zero
    (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (nisnevichTopology X.left) ((restrict X AddCommGrpCat).obj F) (n + 1))
    (fun V s => LargeCohomology.zeroSieve_mem_succ (nisnevichTopology X.left)
      ((restrict X AddCommGrpCat).obj F) n V s)
  exact h.of_iso (colim.mapIso (pointedBaseOrdinaryIso R X Φ F (n + 1)))

/-- For positive original cohomology, only the punctured projection comparison is needed
for vanishing of the actual cylinder restriction; base-germ vanishing is supplied. -/
theorem pointedCylinderRestriction_colimit_eq_zero_succ
    {U : SmoothSite (Spec R)} (j : U ⟶ X) (n : ℕ)
    [IsIso (colim.map (pointedProjection R Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F (n + 1)) (pointedPuncture R j Φ)))] :
    colim.map (pointedCylinderRestriction R j Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F (n + 1))) = 0 :=
  pointedCylinderRestriction_colimit_eq_zero R j Φ _
    (pointedBaseColimit_isZero_succ R X Φ F n)

/-- The actual positive higher-direct-image point fiber vanishes once the punctured
comparison and the original cylinder-restriction monomorphism have been proved. -/
theorem pointedProjectionFiber_isZero_succ
    [HasExt.{u + 1}
      (Sheaf (nisnevichTopology (SmoothSite.a1Cylinder R X).left) AddCommGrpCat.{u + 1})]
    {U : SmoothSite (Spec R)} (j : U ⟶ X) (n : ℕ)
    [IsIso (colim.map (pointedProjection R Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F (n + 1)) (pointedPuncture R j Φ)))]
    [Mono (colim.map (pointedCylinderRestriction R j Φ
      (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec R)) F (n + 1))))] :
    IsZero (Φ.sheafFiber.obj
      (((directImage (SmoothSite.a1Projection R X).left).rightDerived (n + 1)).obj
        ((restrict (SmoothSite.a1Cylinder R X) AddCommGrpCat.{u + 1}).obj F))) :=
  (pointedCylinder_colimit_isZero R j Φ _
    (pointedBaseColimit_isZero_succ R X Φ F n)).of_iso
      (pointedCylinderColimitFiberIso R X Φ F (n + 1)).symm

end Motivic.FiniteEtaleSite
