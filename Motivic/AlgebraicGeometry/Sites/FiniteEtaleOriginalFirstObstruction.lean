/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOrdinaryFirstObstruction
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleOriginalMapAtBase

/-! # First obstruction for the original big-site neighborhood restriction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {B : Scheme.{u}} {X Y : SmoothSite B} (h : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]
  (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})

/-- The obstruction of an original ordinary class, valued in the actual higher image. -/
def originalFirstObstruction (N : ℕ) (V : FiniteEtaleSite X.left)
    (α : SheafCohomology.H.{u + 1, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B)
      F N ((toSmoothSite Y).obj ((baseChange h.left).obj V))) :
    (((directImage h.left).rightDerived N).obj
      ((restrict Y AddCommGrpCat.{u + 1}).obj F)).obj.obj (op V) :=
  ordinaryFirstObstruction h.left V ((restrict Y AddCommGrpCat).obj F) N
    (cohomologyRestrictionEquiv Y F N ((baseChange h.left).obj V) α)

/-- Zero obstruction is precisely lifting along the original restriction map.
The coefficient hypothesis is the original direct-image map, never an inverse-image iso. -/
theorem originalFirstObstruction_eq_zero_iff [IsIso (restrictionToDirectImage F h)]
    (N : ℕ) (hN : 0 < N) (V : FiniteEtaleSite X.left)
    (hR : ∀ q : ℕ, 0 < q → q < N →
      IsZero (((directImage h.left).rightDerived q).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)))
    (α : SheafCohomology.H.{u + 1, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B)
      F N ((toSmoothSite Y).obj ((baseChange h.left).obj V))) :
    originalFirstObstruction h F N V α = 0 ↔
      ∃ β, (SheafCohomology.presheaf (SmoothSite.nisnevichTopology B) F N).map
        ((restrictionProjection h).app V).op β = α := by
  rw [originalFirstObstruction, ordinaryFirstObstruction_eq_zero_iff _ _ _ N hN hR]
  let c := ((SheafCohomology.presheafFunctor.{u + 1, u + 1, u, u + 1}
    (nisnevichTopology X.left) N).map (restrictionToDirectImage F h)).app (op V)
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z', hz'⟩ := (ConcreteCategory.bijective_of_isIso c).2 z
    obtain ⟨β, hβ⟩ := (cohomologyRestrictionEquiv X F N V).surjective z'
    refine ⟨β, (cohomologyRestrictionEquiv Y F N _).injective ?_⟩
    rw [← ordinaryEdgeMap_restrictionToDirectImage h F N V β]
    change ordinaryEdgeMap h.left V _ N (c (cohomologyRestrictionEquiv X F N V β)) = _
    rw [hβ, hz']
    exact hz
  · rintro ⟨β, rfl⟩
    refine ⟨c (cohomologyRestrictionEquiv X F N V β), ?_⟩
    exact ordinaryEdgeMap_restrictionToDirectImage h F N V β

end Motivic.FiniteEtaleSite
