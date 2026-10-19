/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalRatioBoundary
/-! # The correction norm on the entire original inverse infinity

The factor of the complete chart fiber through the original correction boundary
is constructed from the original inverse-infinity factor. In particular, a
pointwise support inclusion is not used to infer a boundary function equation.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.FunctionalChartInfinityNorm`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Correction.FunctionalInfinityProduct`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
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
/-- The original entire inverse-infinity factor computes the norm on the full
chart fiber. Only the total finite chart module is required to be free. -/
theorem correctionFunctionalChart_norm_infinity_value
    {R Q : Type u} [CommRing R] [CommRing Q] {W K I : Scheme.{u}}
    (f : C ⟶ K) (i : I ⟶ K)
    (bI : pullback f i ⟶ D) (hbI : bI ≫ d = pullback.fst f i)
    (n : W ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q)
    (u : W ⟶ C) (t : Spec (.of R) ⟶ K) (Hf : IsPullback u n f t)
    (τ : Spec (.of Q) ⟶ I)
    (hτ : Spec.map (CommRingCat.ofHom φ) ≫ t = τ ≫ i)
    (w : W ⟶ pullback (a ≫ q) π)
    (hw : w ≫ pullback.snd (a ≫ q) π = u)
    [IsIso (pullbackUnitMap w (sectionDualFunctional _ N dS))] :
    let b : Γ(W, ⊤) := Modules.Hom.app
      (inv (pullbackUnitMap w (sectionDualFunctional _ N dS)) ≫
        pullbackUnitMap w (sectionDualFunctional _ N nS)) ⊤ (1 : Γ(W, ⊤))
    let : Algebra R Γ(W, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(W, ⊤)], φ (Algebra.norm R b) = 1 := by
  let : Algebra R Γ(W, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
  dsimp only
  intro hfree
  let := hfree
  let δ := pullback.fst n (Spec.map (CommRingCat.ofHom φ))
  let ε := pullback.snd n (Spec.map (CommRingCat.ofHom φ))
  have hc : (δ ≫ u) ≫ f = (ε ≫ τ) ≫ i := by
    calc
      _ = δ ≫ n ≫ t := by rw [Category.assoc, Hf.w]
      _ = ε ≫ Spec.map (CommRingCat.ofHom φ) ≫ t := by
        rw [← Category.assoc, pullback.condition]
        rfl
      _ = _ := by rw [hτ, Category.assoc]
  let rC := pullback.lift (δ ≫ u) (ε ≫ τ) hc
  have hr : (δ ≫ w) ≫ pullback.snd (a ≫ q) π = (rC ≫ bI) ≫ d := by
    simp only [Category.assoc, hw, hbI, rC, pullback.lift_fst]
  let r := pullback.lift (δ ≫ w) (rC ≫ bI) hr
  exact correctionFunctionalRatio_norm_infinity_value q π j p hq a z s hs e ha d N
    nS dS hN n φ w r (pullback.lift_fst _ _ _).symm

end AlgebraicGeometry.Scheme.RelativeCurvePencil
