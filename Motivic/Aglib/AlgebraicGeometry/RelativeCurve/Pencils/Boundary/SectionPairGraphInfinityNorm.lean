/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphCoordinate
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange

/-! # The full-infinity norm in the original section-induced ideal frame

The original numerator and pole determine the frame. The whole base-changed
source factors through the actual inverse target infinity and the chosen full
boundary, retaining nilpotents. No marked graph coefficient is inverted.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphInfinityNorm`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (π : C ⟶ S) [IsSeparated π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (T : LineBundle (pullback (j ≫ π) π))
  (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
  (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
  (hA : pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) aS ≫
      pullbackTensorMap (Hom.fullBoundaryProductMap π j d s) T.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
    tensorUnitSection (pullbackSectionMap (Hom.fullBoundaryProductMap π j d s) bS)
      (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv)


variable {R Q : Type u} [CommRing R] [CommRing Q] {W K I : Scheme.{u}}
  (f : C ⟶ K) (i : I ⟶ K)
  (bI : pullback f i ⟶ D) (hbI : bI ≫ d = pullback.fst f i)
  (n : W ⟶ Spec (.of R)) [IsFinite n] (φ : R →+* Q)
  (u : W ⟶ C) (t : Spec (.of R) ⟶ K) (Hf : IsPullback u n f t)
  (τ : Spec (.of Q) ⟶ I) (hτ : Spec.map (CommRingCat.ofHom φ) ≫ t = τ ≫ i)
  (w : W ⟶ pullback (j ≫ π) π) (hw : w ≫ pullback.snd (j ≫ π) π = u)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ T bS) w)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) aS) w)]

include hA hbI Hf hτ hw in
/-- The whole inverse infinity factors through the actual chosen boundary. Its
scheme-theoretic scalar one implies norm one, even over nonreduced base change. -/
theorem sectionPairGraphCoefficient_norm_infinity :
    let c : Γ(W, ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient π j T aS bS w) ⊤ (1 : Γ(W, ⊤))
    let : Algebra R Γ(W, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
    ∀ [Module.Free R Γ(W, ⊤)], φ (Algebra.norm R c) = 1 := by
  dsimp only
  intro hfree
  let : Algebra R Γ(W, ⊤) := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
  let := hfree
  let : IsAffine W := isAffine_of_isAffineHom n
  let : Module.Finite R Γ(W, ⊤) := FiniteSchemeNormBaseChange.sections_finite n
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
  have hr : (δ ≫ w) ≫ pullback.snd (j ≫ π) π = (rC ≫ bI) ≫ d := by
    simp only [Category.assoc, hw, hbI, rC, pullback.lift_fst]
  let r := pullback.lift (δ ≫ w) (rC ≫ bI) hr
  have hone := sectionPairGraphCoefficient_infinity_scalar q π j p hq z s hs H e d hd
    T aS bS hA w δ r (pullback.lift_fst _ _ _).symm
  let : Algebra Q Γ(pullback n (Spec.map (CommRingCat.ofHom φ)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd n (Spec.map (CommRingCat.ofHom φ)))).toAlgebra
  have hnorm := FiniteSchemeNormBaseChange.norm_fst_of_finite_free n φ
    (show Γ(W, ⊤) from
      Modules.Hom.app (sectionPairGraphCoefficient π j T aS bS w) ⊤ (1 : Γ(W, ⊤)))
  rw [hone, map_one] at hnorm
  exact hnorm.symm

end AlgebraicGeometry.Scheme.RelativeCurvePencil
