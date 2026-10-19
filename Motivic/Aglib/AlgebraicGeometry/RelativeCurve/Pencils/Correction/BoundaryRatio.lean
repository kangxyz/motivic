/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.BoundaryInclusions
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.PrescribedPairPullback
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.MarkedFiber
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.IdealFrameBoundaryScalar

/-! # The original correction ratio on the full boundary

The ratio is numerator over denominator, hence its divisor is the negative of
the correcting signed cycle. Its marked value is the original prescribed
coordinate, not one. The residual factor must map into the entire supplied
infinity scheme, including its nilpotents.


Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.BoundaryRatio`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.ChartMarkedNorm`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

private theorem sectionRatio_pullback_mul {X W : Scheme.{u}} (f : W ⟶ X)
    {M : X.Modules} (n d : SheafOfModules.unit X.ringCatSheaf ⟶ M) [IsIso d] :
    Hom.unitEndomorphismPullback f (n ≫ inv d) ≫ pullbackSectionMap f d =
      pullbackSectionMap f n := by
  simp only [Hom.unitEndomorphismPullback, pullbackSectionMap,
    Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, IsIso.inv_hom_id, Category.comp_id]

private theorem sectionRatio_coordinate_of_factorization
    {X W B Q : Scheme.{u}} (w : W ⟶ X) (b : B ⟶ X)
    {M : X.Modules} (n d : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    [IsIso (pullbackSectionMap w d)]
    (c : SheafOfModules.unit B.ringCatSheaf ⟶ SheafOfModules.unit B.ringCatSheaf)
    (hn : pullbackSectionMap b n = c ≫ pullbackSectionMap b d)
    (r : Q ⟶ W) (v : Q ⟶ B) (h : r ≫ w = v ≫ b) :
    Hom.unitEndomorphismPullback r
      (pullbackSectionMap w n ≫ inv (pullbackSectionMap w d)) =
      Hom.unitEndomorphismPullback v c := by
  have hh := scalar_pair_pullback v b n d c hn
  rw [← h, ← pullbackSectionMap_comp, ← pullbackSectionMap_comp] at hh
  have hh' : pullbackSectionMap r (pullbackSectionMap w n) =
      Hom.unitEndomorphismPullback v c ≫
        pullbackSectionMap r (pullbackSectionMap w d) := by
    apply (cancel_mono ((Modules.pullbackComp r w).hom.app M)).mp
    simpa only [Category.assoc] using hh
  have : IsIso (pullbackSectionMap r (pullbackSectionMap w d)) := by
    change IsIso ((pullbackUnitIso r).inv ≫
      (Modules.pullback r).map (pullbackSectionMap w d))
    infer_instance
  apply (cancel_mono (pullbackSectionMap r (pullbackSectionMap w d))).mp
  rw [sectionRatio_pullback_mul, hh']

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
theorem correctionRatio_boundary_coordinate {T W : Scheme.{u}}
    (w : T ⟶ pullback (a ≫ q) π) [IsIso (pullbackSectionMap w dS)]
    (r : W ⟶ T)
    (v : W ⟶ (pullback (pullback.snd (a ≫ q) π) d ⨿
      pullback (a ≫ q) (z ≫ q)))
    (h : r ≫ w = v ≫ psiBoundaryInclusion q π j p hq a z s hs d) :
    Hom.unitEndomorphismPullback r
      (pullbackSectionMap w nS ≫ inv (pullbackSectionMap w dS)) =
      Hom.unitEndomorphismPullback v (fixedProductBoundaryFrame q π a z e ha d).hom :=
  sectionRatio_coordinate_of_factorization w _ nS dS _ hN r v h

include hN in
/-- On the full marked scheme the correction is the given graph coordinate. -/
theorem correctionRatio_marked_scalar {T W : Scheme.{u}}
    (w : T ⟶ pullback (a ≫ q) π) [IsIso (pullbackSectionMap w dS)]
    (r : W ⟶ T) (v : W ⟶ pullback (a ≫ q) (z ≫ q))
    (h : r ≫ w = v ≫ psiZeroInclusion q π j p hq a z s hs) :
    r.appTop (Modules.Hom.app
      (pullbackSectionMap w nS ≫ inv (pullbackSectionMap w dS)) ⊤ (1 : Γ(T, ⊤))) =
    Modules.Hom.app (Hom.unitEndomorphismPullback (v ≫ Hom.boundaryProductMap q a z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤ (1 : Γ(W, ⊤)) := by
  rw [← Hom.unitEndomorphismPullback_app_one]
  have hh := correctionRatio_boundary_coordinate q π j p hq a z s hs e ha d N nS dS hN
    w r (v ≫ coprod.inr) (by simpa [psiBoundaryInclusion] using h)
  rw [hh, ← Hom.unitEndomorphismPullback_comp, fixedProductBoundaryFrame_inr,
    Hom.unitEndomorphismPullback_comp]

include hN in
/-- A genuine factorization through the entire infinity boundary gives one. -/
theorem correctionRatio_infinity_scalar {T W : Scheme.{u}}
    (w : T ⟶ pullback (a ≫ q) π) [IsIso (pullbackSectionMap w dS)]
    (r : W ⟶ T) (v : W ⟶ pullback (pullback.snd (a ≫ q) π) d)
    (h : r ≫ w = v ≫ pullback.fst (pullback.snd (a ≫ q) π) d) :
    r.appTop (Modules.Hom.app
      (pullbackSectionMap w nS ≫ inv (pullbackSectionMap w dS)) ⊤ (1 : Γ(T, ⊤))) = 1 := by
  rw [← Hom.unitEndomorphismPullback_app_one]
  have hh := correctionRatio_boundary_coordinate q π j p hq a z s hs e ha d N nS dS hN
    w r (v ≫ coprod.inl) (by simpa [psiBoundaryInclusion] using h)
  rw [hh, ← Hom.unitEndomorphismPullback_comp, fixedProductBoundaryFrame_inl]
  rw [Hom.unitEndomorphismPullback_app_one]
  change v.appTop (1 : Γ(pullback (pullback.snd (a ≫ q) π) d, ⊤)) = 1
  exact map_one v.appTop.hom

include hN in
/-- The actual finite-chart norm of the same correction ratio has the original
marked value. Only the total chart module is free; the residual can be nonreduced.
The two factorization hypotheses are equalities of original scheme maps. -/
theorem correctionRatio_norm_marked_value
    {R Q : Type u} [CommRing R] [CommRing Q] {T V : Scheme.{u}}
    (f : T ⟶ Spec (.of R)) [IsFinite f] (φ : R →+* Q)
    (k : V ⟶ T) [IsOpenImmersion k] (σ : Spec (.of Q) ⟶ V)
    (hf : (σ ≫ k) ≫ f = Spec.map (CommRingCat.ofHom φ))
    (HF : IsPullback σ (𝟙 _) (k ≫ f) (Spec.map (CommRingCat.ofHom φ)))
    (w : T ⟶ pullback (a ≫ q) π) [IsIso (pullbackSectionMap w dS)]
    (m : Spec (.of Q) ⟶ pullback (a ≫ q) (z ≫ q))
    (hm : (σ ≫ k) ≫ w = m ≫ psiZeroInclusion q π j p hq a z s hs)
    (r : (Scheme.residualMarkedFiberOpen f k
      (Spec.map (CommRingCat.ofHom φ)) σ hf).toScheme ⟶
        pullback (pullback.snd (a ≫ q) π) d)
    (hr : Scheme.residualMarkedFiberMap f k
      (Spec.map (CommRingCat.ofHom φ)) σ hf ≫ w =
        r ≫ pullback.fst (pullback.snd (a ≫ q) π) d) :
    let b : Γ(T, ⊤) := Modules.Hom.app
      (pullbackSectionMap w nS ≫ inv (pullbackSectionMap w dS)) ⊤ (1 : Γ(T, ⊤))
    let c : Γ(Spec (.of Q), ⊤) := Modules.Hom.app (Hom.unitEndomorphismPullback
      (m ≫ Hom.boundaryProductMap q a z)
      (e.hom ≫ Hom.idealInclusion (Hom.boundaryGraphTarget q z))) ⊤
        (1 : Γ(Spec (.of Q), ⊤))
    let : Algebra R Γ(T, ⊤) := (FiniteSchemeNormBaseChange.scalarMap f).toAlgebra
    ∀ [Module.Free R Γ(T, ⊤)], φ (Algebra.norm R b) = (Scheme.ΓSpecIso (.of Q)).hom c := by
  dsimp only
  apply FiniteSchemeNormBaseChange.norm_eq_marked_value f φ k σ hf HF
  · have hh := correctionRatio_marked_scalar q π j p hq a z s hs e ha d N nS dS hN
      w (σ ≫ k) m hm
    simpa only [Iso.hom_inv_id_apply] using hh
  · exact correctionRatio_infinity_scalar q π j p hq a z s hs e ha d N nS dS hN
      w _ r hr

end AlgebraicGeometry.Scheme.RelativeCurvePencil
