/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingRelativeQuasicoherent
public import MotivicTest.FiniteOpenCoverGluingRecovery

/-!
# Quasi-coherence of the actual signed three-open gluing

The checked nonidentity rational-line example is now proved quasi-coherent
by the local-to-global theorem, using the original local coefficients and
the actual covering proof.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Motivic.MotivicTest.FiniteOpenCoverGluing

open Scheme.Modules Motivic.FiniteOpenModuleGluing

variable (R : CommRingCat.{0}) (r : R)

/-- The original structure module is quasi-coherent through its actual tilde comparison. -/
theorem structureModule_isQuasicoherent : (structureModule R).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso tildeSelf inferInstance

/-- The actual signed three-open equalizer is quasi-coherent, without a global QC premise. -/
theorem threeGlued_isQuasicoherent : (threeGlued R r).IsQuasicoherent := by
  have := structureModule_isQuasicoherent R
  have (i : Fin 3) : (localModules R r i).IsQuasicoherent := inferInstance
  exact glued_isQuasicoherent (threeOpens R r) (localModules R r) (threeDatum R r)
    (threeOpens_cover R r)

/-- The inhabited, nonidentity affine-line descent consumer is genuinely quasi-coherent. -/
theorem polynomialGlued_isQuasicoherent :
    (threeGlued rationalPolynomialRing Polynomial.X).IsQuasicoherent :=
  threeGlued_isQuasicoherent _ _

/-- Actual affine global sections reconstruct the signed glued sheaf by the tilde counit. -/
def threeGluedTildeIso :
    tilde ((modulesSpecToSheaf.obj (threeGlued R r)).presheaf.obj (.op ⊤)) ≅ threeGlued R r := by
  have := threeGlued_isQuasicoherent R r
  exact asIso (threeGlued R r).fromTildeΓ

/-- The same three-open family refined inside an arbitrary actual ambient open. -/
def relativeThreeOpens (V : (Spec R).Opens) (i : Fin 3) : (Spec R).Opens :=
  threeOpens R r i ⊓ V

/-- This relative family covers exactly the prescribed open, not necessarily the ambient scheme. -/
theorem relativeThreeOpens_union (V : (Spec R).Opens) :
    ⨆ i, relativeThreeOpens R r V i = V := by
  simp only [relativeThreeOpens, ← iSup_inf_eq, threeOpens_cover, top_inf_eq]

/-- A signed actual restriction datum for the relative covering family. -/
def relativeThreeDatum (V : (Spec R).Opens) :
    Datum (relativeThreeOpens R r V)
      (restrictedModules (relativeThreeOpens R r V) (structureModule R)) :=
  signedDatum _ _ (canonicalDatum (relativeThreeOpens R r V) (structureModule R)) localSigns

/-- The ambient equalizer becomes quasi-coherent on exactly the whole prescribed open. -/
theorem relativeThreeGlued_isQuasicoherent (V : (Spec R).Opens) :
    ((restrictFunctor V.ι).obj
      (glued (relativeThreeOpens R r V)
        (restrictedModules (relativeThreeOpens R r V) (structureModule R))
        (relativeThreeDatum R r V))).IsQuasicoherent := by
  have := structureModule_isQuasicoherent R
  have (i : Fin 3) :
      (restrictedModules (relativeThreeOpens R r V) (structureModule R) i).IsQuasicoherent :=
    inferInstance
  exact glued_restrict_isQuasicoherent _ _ (relativeThreeDatum R r V) V
    (relativeThreeOpens_union R r V)

/-- The relative-cover theorem has a genuinely proper affine-line open available as its union. -/
theorem polynomial_firstOpen_ne_top :
    threeOpens rationalPolynomialRing Polynomial.X 0 ≠ ⊤ := by
  intro h
  have hh := congrArg
    (fun V : (Spec rationalPolynomialRing).Opens => polynomialPoint 0 ∈ V) h
  change (Polynomial.eval 0 Polynomial.X ≠ 0) = True at hh
  simp at hh

/-- The relative theorem is consumed on the proper principal affine-line open D(X). -/
theorem polynomialRelativeGlued_isQuasicoherent :
    have V := threeOpens rationalPolynomialRing Polynomial.X 0
    ((restrictFunctor V.ι).obj
      (glued (relativeThreeOpens rationalPolynomialRing Polynomial.X V)
        (restrictedModules (relativeThreeOpens rationalPolynomialRing Polynomial.X V)
          (structureModule rationalPolynomialRing))
        (relativeThreeDatum rationalPolynomialRing Polynomial.X V))).IsQuasicoherent :=
  relativeThreeGlued_isQuasicoherent _ _ _

end Motivic.MotivicTest.FiniteOpenCoverGluing
