/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryInclusions
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.PrescribedPairPullback

/-! # The original correcting section pair agrees on infinity

The same numerator and denominator used by the relative section producer agree
on the entire infinity boundary. No new sections or frames are chosen. This is
a boundary input to a nullhomotopy pencil, not its correspondence endpoint theorem.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.InfinityEquality`.
Incoming project consumers: `Motivic.Transfers.Presheaf.Actions.Pencils.Correction`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y A Z C D : Scheme.{u}}
  (q : X ⟶ S) [IsSeparated q] (π : C ⟶ S)
  (j : Y ⟶ C) (p : Y ⟶ X) (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [Flat a] (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (N : LineBundle (pullback (a ≫ q) π))
  (nS dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
  (hN : pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS =
    (fixedProductBoundaryFrame q π a z e ha d).hom ≫
      pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)

include hN in
/-- The prescribed scalar is one on the whole infinity scheme, so these exact
sections agree there, without reducing the boundary or changing either section. -/
theorem correctionSections_infinity_eq :
    pullbackSectionMap (pullback.fst (pullback.snd (a ≫ q) π) d) nS =
      pullbackSectionMap (pullback.fst (pullback.snd (a ≫ q) π) d) dS := by
  have h := scalar_pair_pullback coprod.inl
    (psiBoundaryInclusion q π j p hq a z s hs d) nS dS
    (fixedProductBoundaryFrame q π a z e ha d).hom hN
  rw [fixedProductBoundaryFrame_inl, Category.id_comp] at h
  dsimp only [psiBoundaryInclusion] at h
  rw [coprod.inl_desc] at h
  exact h

include hN in
/-- The same equality holds for the actual dual functionals required by the
boundary pencil; it is not an equality of only their supports or divisor classes. -/
theorem correctionFunctionals_infinity_eq :
    Hom.pullbackToUnit (sectionDualFunctional _ N nS)
        (pullback.fst (pullback.snd (a ≫ q) π) d) =
      Hom.pullbackToUnit (sectionDualFunctional _ N dS)
        (pullback.fst (pullback.snd (a ≫ q) π) d) := by
  have h := correctionSections_infinity_eq q π j p hq a z s hs e ha d N nS dS hN
  rw [sectionDualFunctional_pullback, sectionDualFunctional_pullback]
  simp only [pulledSectionDualFunctional, h]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
