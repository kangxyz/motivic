/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.InfinityBoundaryIdeal

/-! # The actual prescribed trivialization on the entire disjoint boundary -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Glue the canonical infinity unit to the exact étale coordinate trivialization.
Neither component triviality is a premise, and the original full Spec B is retained. -/
theorem exists_fullBoundaryDivisorIso
    (R B : Type u) [CommRing R] [CommRing B] (z : Polynomial R →+* B)
    {C Y D : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
    (j : Y ⟶ C) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of (Polynomial R))) [Flat p]
    (hq : j ≫ q = p ≫ boundaryLineProjection R)
    (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z))
    (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
    (U : (pullback (j ≫ q) q).Opens)
    (hU : Set.range (compactificationGraph q j) ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ pullback.fst (j ≫ q) q)] :
    let hI := graph_idealModule_isLocallyRankOne j q U hU
    let L := (Invertible.dualLineBundle _ ⟨idealModule (compactificationGraph q j), hI⟩).val
    let a := infinityProductMap q j d
    let b := graphBoundaryRestriction q j s
    ∃ E : (Scheme.Modules.pullback (coprod.desc a b)).obj L ≅
        SheafOfModules.unit ((pullback (pullback.snd (j ≫ q) q) d ⨿
          pullback (j ≫ q) (s ≫ j ≫ q))).ringCatSheaf,
      (Scheme.Modules.restrictFunctor (coprod.inl : pullback (pullback.snd (j ≫ q) q) d ⟶
        pullback (pullback.snd (j ≫ q) q) d ⨿ pullback (j ≫ q) (s ≫ j ≫ q))).map E.hom ≫
          (restrictUnitIso _).hom =
        (coprodPullbackRestrictLeft a b).hom.app L ≫ (infinityBoundaryDivisorIso q j d hd hI).hom ∧
      (Scheme.Modules.restrictFunctor (coprod.inr : pullback (j ≫ q) (s ≫ j ≫ q) ⟶
        pullback (pullback.snd (j ≫ q) q) d ⨿ pullback (j ≫ q) (s ≫ j ≫ q))).map E.hom ≫
          (restrictUnitIso _).hom =
        (coprodPullbackRestrictRight a b).hom.app L ≫
          (compactificationBoundaryDivisorIso R B z q j p hq s hs H hI).hom := by
  dsimp only
  exact exists_coprod_pullback_unitIso _ _ _
    (infinityBoundaryDivisorIso q j d hd (graph_idealModule_isLocallyRankOne j q U hU))
    (compactificationBoundaryDivisorIso R B z q j p hq s hs H
      (graph_idealModule_isLocallyRankOne j q U hU))

end AlgebraicGeometry.Scheme.Hom
