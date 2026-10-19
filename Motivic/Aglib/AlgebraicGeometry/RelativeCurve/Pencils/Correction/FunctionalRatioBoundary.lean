/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryInclusions
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.PrescribedPairPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.FunctionalRatio
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedFiber
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar

/-! # The original functional correction quotient on the full boundary

The actual functional quotient retains the original numerator over denominator,
hence its divisor is the negative of
the correcting signed cycle. Its marked value is the original prescribed
coordinate, not one. The residual factor must map into the entire supplied
infinity scheme, including its nilpotents.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalRatioBoundary`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalChartMarkedNorm`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

private theorem functionalRatio_coordinate_of_factorization
    {X W B Q : Scheme.{u}} (w : W ⟶ X) (b : B ⟶ X)
    (L : LineBundle X) (n d : SheafOfModules.unit X.ringCatSheaf ⟶ L.val)
    [IsIso (pullbackUnitMap w (sectionDualFunctional X L d))]
    (c : SheafOfModules.unit B.ringCatSheaf ⟶ SheafOfModules.unit B.ringCatSheaf)
    (hn : pullbackSectionMap b n = c ≫ pullbackSectionMap b d)
    (r : Q ⟶ W) (v : Q ⟶ B) (h : r ≫ w = v ≫ b) :
    Hom.unitEndomorphismPullback r
      (inv (pullbackUnitMap w (sectionDualFunctional X L d)) ≫
        pullbackUnitMap w (sectionDualFunctional X L n)) =
      Hom.unitEndomorphismPullback v c := by
  apply functionalQuotient_boundary_of_sectionEquation w r L n d
  have hh := scalar_pair_pullback v b n d c hn
  rw [← h] at hh
  exact hh

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
/-- The literal chart ratio retains the full prescribed correction coordinate. -/
theorem correctionFunctionalRatio_boundary_coordinate {T W : Scheme.{u}}
    (w : T ⟶ pullback (a ≫ q) π) [IsIso (pullbackUnitMap w (sectionDualFunctional _ N dS))]
    (r : W ⟶ T)
    (v : W ⟶ (pullback (pullback.snd (a ≫ q) π) d ⨿
      pullback (a ≫ q) (z ≫ q)))
    (h : r ≫ w = v ≫ psiBoundaryInclusion q π j p hq a z s hs d) :
    Hom.unitEndomorphismPullback r
      (inv (pullbackUnitMap w (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap w (sectionDualFunctional _ N nS)) =
      Hom.unitEndomorphismPullback v (fixedProductBoundaryFrame q π a z e ha d).hom :=
  functionalRatio_coordinate_of_factorization w _ N nS dS _ hN r v h

include hN in
/-- On the full marked scheme the correction is the given graph coordinate. -/
theorem correctionFunctionalRatio_marked_scalar {T W : Scheme.{u}}
    (w : T ⟶ pullback (a ≫ q) π) [IsIso (pullbackUnitMap w (sectionDualFunctional _ N dS))]
    (r : W ⟶ T) (v : W ⟶ pullback (a ≫ q) (z ≫ q))
    (h : r ≫ w = v ≫ psiZeroInclusion q π j p hq a z s hs) :
    r.appTop (Modules.Hom.app
      (inv (pullbackUnitMap w (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap w (sectionDualFunctional _ N nS)) ⊤ (1 : Γ(T, ⊤))) =
    Modules.Hom.app (Hom.unitEndomorphismPullback (v ≫ Hom.boundaryProductMap q a z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤ (1 : Γ(W, ⊤)) := by
  rw [← Hom.unitEndomorphismPullback_app_one]
  have hh := correctionFunctionalRatio_boundary_coordinate q π j p hq a z s hs e ha d N nS dS hN
    w r (v ≫ coprod.inr) (by simpa [psiBoundaryInclusion] using h)
  rw [hh, ← Hom.unitEndomorphismPullback_comp, fixedProductBoundaryFrame_inr,
    Hom.unitEndomorphismPullback_comp]

include hN in
/-- A genuine factorization through the entire infinity boundary gives one. -/
theorem correctionFunctionalRatio_infinity_scalar {T W : Scheme.{u}}
    (w : T ⟶ pullback (a ≫ q) π) [IsIso (pullbackUnitMap w (sectionDualFunctional _ N dS))]
    (r : W ⟶ T) (v : W ⟶ pullback (pullback.snd (a ≫ q) π) d)
    (h : r ≫ w = v ≫ pullback.fst (pullback.snd (a ≫ q) π) d) :
    r.appTop (Modules.Hom.app
      (inv (pullbackUnitMap w (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap w (sectionDualFunctional _ N nS)) ⊤ (1 : Γ(T, ⊤))) = 1 := by
  rw [← Hom.unitEndomorphismPullback_app_one]
  have hh := correctionFunctionalRatio_boundary_coordinate q π j p hq a z s hs e ha d N nS dS hN
    w r (v ≫ coprod.inl) (by simpa [psiBoundaryInclusion] using h)
  rw [hh, ← Hom.unitEndomorphismPullback_comp, fixedProductBoundaryFrame_inl]
  rw [Hom.unitEndomorphismPullback_app_one]
  change v.appTop (1 : Γ(pullback (pullback.snd (a ≫ q) π) d, ⊤)) = 1
  exact map_one v.appTop.hom

include hN in
/-- The actual finite-chart norm of the same correction ratio has the original
marked value. Only the total chart module is free; the residual can be nonreduced.
The two factorization hypotheses are equalities of original scheme maps. -/
theorem correctionFunctionalRatio_norm_marked_value
    {R Q : Type u} [CommRing R] [CommRing Q] {T V : Scheme.{u}}
    (f : T ⟶ Spec (.of R)) [IsFinite f] (φ : R →+* Q)
    (k : V ⟶ T) [IsOpenImmersion k] (σ : Spec (.of Q) ⟶ V)
    (hf : (σ ≫ k) ≫ f = Spec.map (CommRingCat.ofHom φ))
    (HF : IsPullback σ (𝟙 _) (k ≫ f) (Spec.map (CommRingCat.ofHom φ)))
    (w : T ⟶ pullback (a ≫ q) π) [IsIso (pullbackUnitMap w (sectionDualFunctional _ N dS))]
    (m : Spec (.of Q) ⟶ pullback (a ≫ q) (z ≫ q))
    (hm : (σ ≫ k) ≫ w = m ≫ psiZeroInclusion q π j p hq a z s hs)
    (r : (Scheme.residualMarkedFiberOpen f k
      (Spec.map (CommRingCat.ofHom φ)) σ hf).toScheme ⟶
        pullback (pullback.snd (a ≫ q) π) d)
    (hr : Scheme.residualMarkedFiberMap f k
      (Spec.map (CommRingCat.ofHom φ)) σ hf ≫ w =
        r ≫ pullback.fst (pullback.snd (a ≫ q) π) d) :
    let b : Γ(T, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap w (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap w (sectionDualFunctional _ N nS)) ⊤ (1 : Γ(T, ⊤))
    let c : Γ(Spec (.of Q), ⊤) := Modules.Hom.app (Hom.unitEndomorphismPullback
      (m ≫ Hom.boundaryProductMap q a z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤
        (1 : Γ(Spec (.of Q), ⊤))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap f).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)], φ (Algebra.norm R b) = (Scheme.ΓSpecIso (.of Q)).hom c := by
  dsimp only
  apply FiniteSchemeNormBaseChange.norm_eq_marked_value f φ k σ hf HF
  · have hh := correctionFunctionalRatio_marked_scalar q π j p hq a z s hs e ha d N nS dS hN
      w (σ ≫ k) m hm
    simpa only [Iso.hom_inv_id_apply] using hh
  · exact correctionFunctionalRatio_infinity_scalar q π j p hq a z s hs e ha d N nS dS hN
      w _ r hr

include hN in
/-- On an actual full infinity fiber, base change of the correction norm is one.
The fiber is the entire scheme pullback, not its reduction or its point support. -/
theorem correctionFunctionalRatio_norm_infinity_value
    {R Q : Type u} [CommRing R] [CommRing Q] {T : Scheme.{u}}
    (f : T ⟶ Spec (.of R)) [IsFinite f] (φ : R →+* Q)
    (w : T ⟶ pullback (a ≫ q) π)
    [IsIso (pullbackUnitMap w (sectionDualFunctional _ N dS))]
    (v : pullback f (Spec.map (CommRingCat.ofHom φ)) ⟶
      pullback (pullback.snd (a ≫ q) π) d)
    (hv : pullback.fst f (Spec.map (CommRingCat.ofHom φ)) ≫ w =
      v ≫ pullback.fst (pullback.snd (a ≫ q) π) d) :
    let b : Γ(T, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap w (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap w (sectionDualFunctional _ N nS)) ⊤ (1 : Γ(T, ⊤))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap f).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)], φ (Algebra.norm R b) = 1 := by
  let : IsAffine T := isAffine_of_isAffineHom f
  let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap f).toAlgebra
  let : Module.Finite R Γ(T, ⊤) := FiniteSchemeNormBaseChange.sections_finite f
  let : Algebra Q Γ(pullback f (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  rw [← FiniteSchemeNormBaseChange.norm_fst_of_finite_free f φ]
  rw [correctionFunctionalRatio_infinity_scalar q π j p hq a z s hs e ha d N
    nS dS hN w _ v hv, map_one]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
