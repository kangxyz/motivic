/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteRepresentativeUnion
public import Lean.Util.CollectAxioms

/-! The appended representatives retain their actual maps, centers and original germs. -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
universe u v
namespace MotivicTest.SmoothSiteNisnevichFiniteRepresentativeUnion

variable {B : Scheme.{u}} [IsAffine B] {Y : SmoothSite B} {n m : ℕ}
  (y : Fin n → Y.left) (R : ∀ i, SmoothSite.NisnevichNeighborhood Y (y i))
  (z : Fin m → Y.left) (S : ∀ j, SmoothSite.NisnevichNeighborhood Y (z j))
  (F : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v})
  (s : ∀ i, F.obj (op ((SmoothSite.nisnevichNeighborhoodFunctor Y (y i)).obj (R i))))
  (t : ∀ j, F.obj (op ((SmoothSite.nisnevichNeighborhoodFunctor Y (z j)).obj (S j))))

omit [IsAffine B] in
/-- The left branch keeps its original map to the target, not only its image. -/
theorem actual_left_toBase (i : Fin n) :
    (appendLeftIso y R z S i).hom ≫
      (appendFamily y R z S (Fin.castAdd m i)).toBase = (R i).toBase :=
  appendLeftIso_hom_toBase y R z S i

/-- Both representative families still represent the same original germ tuple. -/
theorem actual_appended_germs
    (a : ∀ p : Y.left, (SmoothSite.nisnevichPointFiberCocone Y p F).pt)
    (hs : ∀ i, (SmoothSite.nisnevichPointFiberCocone Y (y i) F).ι.app (op (R i))
      (s i) = a (y i))
    (ht : ∀ j, (SmoothSite.nisnevichPointFiberCocone Y (z j) F).ι.app (op (S j))
      (t j) = a (z j)) :
    ∀ l, (SmoothSite.nisnevichPointFiberCocone Y (appendPoints y R z S l) F).ι.app
      (op (appendFamily y R z S l)) (appendSections y R z S F s t l) =
        a (appendPoints y R z S l) :=
  appendSections_represents y R z S F s t a hs ht

open Lean in
run_cmd do
  for name in #[``actual_left_toBase, ``actual_appended_germs,
      ``appendLeftIso_hom_left, ``appendRightIso_hom_left,
      ``appendLeftIso_hom_center, ``appendRightIso_hom_center,
      ``appendSections_left, ``appendSections_right] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual appended pointed representatives: standard foundations only."

end MotivicTest.SmoothSiteNisnevichFiniteRepresentativeUnion
