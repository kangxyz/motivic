/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.InfinityBoundaryIdeal

/-! # The coordinate graph frame on the literal marked-boundary pullback

The existing coordinate construction uses the product with the entire marked
scheme. This leaf transports that same frame to the nested pullback used by the
original graph moving consumer. Neither the source nor the boundary is shrunk.


Intended upstream module: `Aglib.AlgebraicGeometry.EffectiveCartierDivisor.MarkedProductFrame`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Polynomial

universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C Y Z : Scheme.{u}} (q : C ⟶ S) (j : Y ⟶ C) (s : Z ⟶ Y)

/-- The original marked product and the literal base change of the second
projection are canonically the same scheme. -/
def markedBoundaryProductIso :
    pullback (j ≫ q) (s ≫ j ≫ q) ≅
      pullback (pullback.snd (j ≫ q) q) (s ≫ j) :=
  (graphBoundaryRestriction_isPullback q j s).isoPullback

@[reassoc (attr := simp)]
theorem markedBoundaryProductIso_inv_map :
    (markedBoundaryProductIso q j s).inv ≫ graphBoundaryRestriction q j s =
      infinityProductMap q j (s ≫ j) :=
  (graphBoundaryRestriction_isPullback q j s).isoPullback_inv_fst

/-- Transport of the same graph ideal frame, through the canonical product
comparison, with no replacement of the underlying ideal. -/
def markedBoundaryIdealFrame
    (e : SheafOfModules.unit (pullback (j ≫ q) (s ≫ j ≫ q)).ringCatSheaf ≅
      (Scheme.Modules.pullback (graphBoundaryRestriction q j s)).obj
        (idealModule (compactificationGraph q j))) :
    (Scheme.Modules.pullback (infinityProductMap q j (s ≫ j))).obj
      (idealModule (compactificationGraph q j)) ≅
    SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) (s ≫ j)).ringCatSheaf :=
  ((Scheme.Modules.pullbackCongr (markedBoundaryProductIso_inv_map q j s)).app
      (idealModule (compactificationGraph q j))).symm ≪≫
    ((Scheme.Modules.pullbackComp (markedBoundaryProductIso q j s).inv
      (graphBoundaryRestriction q j s)).app (idealModule (compactificationGraph q j))).symm ≪≫
    (Scheme.Modules.pullback (markedBoundaryProductIso q j s).inv).mapIso e.symm ≪≫
    pullbackUnitIso (markedBoundaryProductIso q j s).inv

/-- The frame morphism is precisely the transported original frame morphism. -/
theorem markedBoundaryIdealFrame_hom
    (e : SheafOfModules.unit (pullback (j ≫ q) (s ≫ j ≫ q)).ringCatSheaf ≅
      (Scheme.Modules.pullback (graphBoundaryRestriction q j s)).obj
        (idealModule (compactificationGraph q j))) :
    (markedBoundaryIdealFrame q j s e).hom =
      ((Scheme.Modules.pullbackCongr (markedBoundaryProductIso_inv_map q j s)).app
        (idealModule (compactificationGraph q j))).inv ≫
      ((Scheme.Modules.pullbackComp (markedBoundaryProductIso q j s).inv
        (graphBoundaryRestriction q j s)).app
          (idealModule (compactificationGraph q j))).inv ≫
      (Scheme.Modules.pullback (markedBoundaryProductIso q j s).inv).map e.inv ≫
      (pullbackUnitIso (markedBoundaryProductIso q j s).inv).hom := rfl

/-- The constructed coordinate frame in the exact type consumed by the original
compactification graph mover. The whole Cartesian boundary condition is retained;
there is no supplied frame or affineness hypothesis on Y. -/
def coordinateMarkedBoundaryIdealFrame
    (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
    {C Y : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
    (j : Y ⟶ C) [IsOpenImmersion j]
    (p : Y ⟶ Spec (.of R[X])) [Flat p]
    (hq : j ≫ q = p ≫ boundaryLineProjection R)
    (s : Spec (.of B) ⟶ Y) (h : s ≫ p = boundaryCoordinateMap R B z)
    (H : IsPullback s (𝟙 _) p (boundaryCoordinateMap R B z)) :
    (Scheme.Modules.pullback (infinityProductMap q j (s ≫ j))).obj
      (idealModule (compactificationGraph q j)) ≅
    SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) (s ≫ j)).ringCatSheaf :=
  markedBoundaryIdealFrame q j s
    (compactificationBoundaryIdealIso R B z q j p hq s h H)

end AlgebraicGeometry.Scheme.Hom
