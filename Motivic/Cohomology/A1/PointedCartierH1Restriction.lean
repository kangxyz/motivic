/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PointedCartierH1RestrictionMono
public import Motivic.Cohomology.A1.ContractionBoundaryIso

/-! # Original Cartier H1 puncture injectivity with the boundary input discharged -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace Motivic.FiniteEtaleSite

/-- The original H1 restriction at every complete field-valued Cartier mark is
monic. Canonical boundary epimorphisms are proved, not additional hypotheses. -/
theorem pointedCylinderRestriction_H1_mono_of_cartier
    {k : Type u} [Field k] [Infinite k]
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
    (Y : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant)
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) [IsClosedImmersion i] [Smooth (i ≫ Y.hom)]
    (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    {U : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hcomp : Set.range i = (Set.range j.left)ᶜ)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y.left) (s : Spec (.of K))
    (hb : b s ∈ Set.range i) :
    Mono (colim.map (pointedCylinderRestriction (.of k) j
      (relativeFieldPoint b K (𝟙 _))
      (SheafCohomology.presheaf.{u + 1, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
          ((SheafWithTransfers.toSheaf k).obj F) 1))) := by
  exact pointedCylinderRestriction_H1_mono_of_cartier_of_boundary_epi
    Y F hF (fun X => contractionToBoundary_epi X F hF) i hI j hcomp K b s hb

end Motivic.FiniteEtaleSite
