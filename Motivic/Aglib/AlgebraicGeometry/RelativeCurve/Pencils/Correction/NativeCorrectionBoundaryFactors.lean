/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ThickBoundaryBaseChange
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeGeometry
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter
/-! # Restrict the same complete correction-boundary factors

The existing thickened boundary is restricted to the already selected coefficient
open. The entire inverse infinity and entire residual fiber retain their original
scheme-theoretic factorizations, with no replacement thickening or section choice.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.NativeCorrectionBoundaryFactors`.

The exact hypotheses are the section variables and declaration signatures below.
This is a standalone API with no current direct import consumer.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C D E : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C) (V : S.Opens)
  (m : E ⟶ boundaryBaseCompactification π V) (b : E ⟶ D)
  (hb : b ≫ d = m ≫ pullback.snd V.ι π)

/-- An original factor into D restricts to its literal coefficient-open inverse
image, using the existing factorization as a scheme-map equality. -/
def boundaryBaseWholeFactor : E ⟶ ((d ≫ π) ⁻¹ᵁ V).toScheme :=
  IsOpenImmersion.lift ((d ≫ π) ⁻¹ᵁ V).ι b (by
    rintro _ ⟨x, rfl⟩
    rw [Opens.range_ι]
    change ((b ≫ d) ≫ π) x ∈ V
    rw [hb, Category.assoc, ← pullback.condition, ← Category.assoc]
    exact (pullback.fst V.ι π (m x)).property)

@[reassoc (attr := simp)]
theorem boundaryBaseWholeFactor_inclusion :
    boundaryBaseWholeFactor π d V m b hb ≫ boundaryBaseWholeMap π d V = m := by
  rw [← cancel_mono (pullback.snd V.ι π)]
  simp only [Category.assoc, boundaryBaseWholeMap_snd]
  rw [← Category.assoc, boundaryBaseWholeFactor, IsOpenImmersion.lift_fac, hb]

variable (R : Type u) [CommRing R] {C D DA : Scheme.{u}}
  (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite f]
  (d : D ⟶ C) (dA : DA ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
  (V : (Spec (.of R)).Opens) [IsAffine V.toScheme]

/-- The full inverse of the native original infinity maps to its original whole
inverse fiber before restriction. No reduced boundary or residual support is used. -/
def nativeCorrectionInfinityFiberMap :
    pullback (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f V)
      (targetNativeInfinity R V dA) ⟶ pullback f dA :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd V.ι (f ≫ ProjectiveSpace.toSpec R _))
    (pullback.snd _ _ ≫
      ((dA ≫ ((𝟙 _) ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ V).ι) (by
      calc
        (pullback.fst _ _ ≫ pullback.snd V.ι _) ≫ f =
            pullback.fst _ _ ≫ (pullback.snd V.ι _ ≫ f) := Category.assoc _ _ _
        _ = pullback.fst _ _ ≫
            (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f V ≫
              ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R V.ι) _) :=
          congrArg (fun k => pullback.fst _ _ ≫ k)
            (ConstantCurve.affineSourceToProjectiveSpace_map R
              (ULift.{u} (Fin 2)) V.ι f).symm
        _ = (pullback.fst _ _ ≫ boundaryBaseProjectiveMap R _ f V) ≫
            ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R V.ι) _ :=
          (Category.assoc _ _ _).symm
        _ = (pullback.snd _ _ ≫ targetNativeInfinity R V dA) ≫
            ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R V.ι) _ :=
          congrArg (fun k => k ≫
            ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R V.ι) _)
            (pullback.condition (f := boundaryBaseProjectiveMap R _ f V)
              (g := targetNativeInfinity R V dA))
        _ = pullback.snd _ _ ≫ (targetNativeInfinity R V dA ≫
            ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R V.ι) _) :=
          Category.assoc _ _ _
        _ = pullback.snd _ _ ≫
            (((dA ≫ ((𝟙 _) ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ V).ι ≫ dA) :=
          congrArg (fun k => pullback.snd _ _ ≫ k)
            (targetNativeInfinity_coefficient R V dA)
        _ = _ := (Category.assoc _ _ _).symm)

/-- The original entire inverse-infinity factor survives the common coefficient
restriction, landing in exactly the boundary used by the native section record. -/
def nativeCorrectionInfinityFactor :
    pullback (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f V)
      (targetNativeInfinity R V dA) ⟶
        ((d ≫ (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ V).toScheme :=
  boundaryBaseWholeFactor (f ≫ ProjectiveSpace.toSpec R _) d V (pullback.fst _ _)
    (nativeCorrectionInfinityFiberMap R f dA V ≫ bI) (by
      rw [Category.assoc, hbI]
      exact pullback.lift_fst _ _ _)

omit [IsFinite f] in
@[reassoc (attr := simp)]
theorem nativeCorrectionInfinityFactor_inclusion :
    nativeCorrectionInfinityFactor R f d dA bI hbI V ≫
      boundaryBaseWholeMap (f ≫ ProjectiveSpace.toSpec R _) d V = pullback.fst _ _ :=
  boundaryBaseWholeFactor_inclusion _ _ _ _ _ _

section Residual
variable {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R)))
  (j : Y ⟶ C)
  (hq : j ≫ (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) =
    p ≫ boundaryLineProjection R)
  (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (hsK : (s ≫ j) ≫ f = z ≫ chart R 0)

/-- The native original marked map retains its literal original ambient point. -/
theorem nativeCorrectionMarked_coefficient :
    (targetNativeMarked R V z ≫ chart Γ(V.toScheme, ⊤) 0) ≫
      ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R V.ι)
        (ULift.{u} (Fin 2)) =
      ((z ≫ boundaryLineProjection R) ⁻¹ᵁ V).ι ≫ (z ≫ chart R 0) := by
  simp only [Category.assoc, chart_map, targetNativeMarked,
    targetAffineOpenIso_inv_coordinate_assoc, morphismRestrict_ι_assoc]
  rfl

omit [IsFinite f] [IsAffine V.toScheme] in
/-- The original source marked point is restricted only on the coefficient base. -/
theorem nativeCorrectionMarked_source :
    ((z ≫ boundaryLineProjection R) ⁻¹ᵁ V).ι ≫ (s ≫ j) =
      (boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ V
        (fun _ _ => trivial) ≫
       boundaryBaseCoverInclusion (boundaryLineProjection R) p
        (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) j hq ⊤ V) ≫
      pullback.snd V.ι (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  simp only [Category.assoc, boundaryBaseCoverInclusion_snd,
    boundaryBaseCoverLift_ι_assoc]

include hsK in
omit [IsFinite f] in
/-- Exact native marked triangle after the fixed coefficient restriction. -/
theorem nativeCorrectionMarked_triangle :
    (boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ V
        (fun _ _ => trivial) ≫
       boundaryBaseCoverInclusion (boundaryLineProjection R) p
        (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) j hq ⊤ V) ≫
      boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f V =
        targetNativeMarked R V z ≫ chart Γ(V.toScheme, ⊤) 0 := by
  let t := ProjectiveSpace.map (ConstantCurve.affineSourceCoefficientMap R V.ι)
    (ULift.{u} (Fin 2))
  let : IsOpenImmersion t := MorphismProperty.of_isPullback
    (ConstantCurve.affineSourceProjectiveSquare R (ULift.{u} (Fin 2)) V.ι).flip
    inferInstance
  rw [← cancel_mono t]
  dsimp only [t, boundaryBaseProjectiveMap]
  rw [Category.assoc, ConstantCurve.affineSourceToProjectiveSpace_map]
  rw [← Category.assoc, ← nativeCorrectionMarked_source R f V p j hq z s hs,
    Category.assoc, hsK]
  exact (nativeCorrectionMarked_coefficient R V z).symm

/-- The same original residual factor, restricted to the same coefficient open,
lands scheme-theoretically in the unchanged restricted thickened boundary. -/
def nativeCorrectionResidualFactor
    (bE : (Scheme.residualMarkedFiberOpen f j (z ≫ chart R 0) s hsK).toScheme ⟶ D)
    (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j (z ≫ chart R 0) s hsK) :
    (Scheme.residualMarkedFiberOpen
      (boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) f V)
      (boundaryBaseCoverInclusion (boundaryLineProjection R) p
        (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) j hq ⊤ V)
      (targetNativeMarked R V z ≫ chart Γ(V.toScheme, ⊤) 0)
      (boundaryBaseCoverLift (boundaryLineProjection R) p z s hs ⊤ V
        (fun _ _ => trivial))
      (nativeCorrectionMarked_triangle R f V p j hq z s hs hsK)).toScheme ⟶
      ((d ≫ (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ V).toScheme :=
  boundaryBaseWholeFactor (f ≫ ProjectiveSpace.toSpec R _) d V
    (Scheme.residualMarkedFiberMap _ _ _ _ _)
    (Scheme.residualBaseChangeMap f j (z ≫ chart R 0) s hsK
      _ _ _ _ _ (pullback.snd V.ι (f ≫ ProjectiveSpace.toSpec R _)) _
      (ConstantCurve.affineSourceToProjectiveSpace_isPullback R (ULift.{u} (Fin 2)) V.ι f)
      ((z ≫ boundaryLineProjection R) ⁻¹ᵁ V).ι
      (nativeCorrectionMarked_coefficient R V z)
      (nativeCorrectionMarked_source R f V p j hq z s hs) ≫ bE)
    (Scheme.residualBaseChangeMap_boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hbE)

@[reassoc (attr := simp)]
theorem nativeCorrectionResidualFactor_inclusion
    (bE : (Scheme.residualMarkedFiberOpen f j (z ≫ chart R 0) s hsK).toScheme ⟶ D)
    (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j (z ≫ chart R 0) s hsK) :
    nativeCorrectionResidualFactor R f d V p j hq z s hs hsK bE hbE ≫
      boundaryBaseWholeMap (f ≫ ProjectiveSpace.toSpec R _) d V =
        Scheme.residualMarkedFiberMap _ _ _ _ _ :=
  boundaryBaseWholeFactor_inclusion _ _ _ _ _ _

end Residual
end AlgebraicGeometry.Scheme.Hom
