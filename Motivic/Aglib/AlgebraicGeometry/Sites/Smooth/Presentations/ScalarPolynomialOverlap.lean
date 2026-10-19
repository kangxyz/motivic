/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Presentations.ScalarPolynomial
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.BaseChange.ScalarEtalePullback

/-! # The native scalar original polynomial overlap

The canonical map from the scalar-coordinate overlap to the scalar extension of
the original overlap retains both original projections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra.Smooth k R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

local instance : Algebra.Smooth k (Polynomial R) := by
  let : Algebra.Smooth R (Polynomial R) := {}
  exact Algebra.Smooth.comp k R (Polynomial R)

local instance : Algebra.Smooth L ((Polynomial R) ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L (Polynomial R))

variable {Y : SmoothSite (Spec (.of k))}
  (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]

local notation "F" => fieldBaseChange (algebraMap k L)
local notation "a" => openInclusion (k := k) (Polynomial.X : Polynomial R)
local notation "aL" => openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))
local notation "pL" =>
  CategoryTheory.Functor.map (fieldBaseChange (algebraMap k L)) p ≫
    Iso.hom (scalarLineIso k R L)

local instance : Etale (pL).left := by
  have : Etale (p ≫ (polynomialAffineIso k R).hom).left := by
    simpa only [MorphismProperty.Comma.comp_left] using
      inferInstanceAs (Etale (p.left ≫ (polynomialAffineIso k R).hom.left))
  have hE : Etale (((F).map (p ≫ (polynomialAffineIso k R).hom)).left ≫
      (affineScalarIso k (Polynomial R) L).hom.left) :=
    MorphismProperty.of_isPullback (scalarPolynomialSourceSquare k R L p) inferInstance
  have h := congrArg (fun f => f.left) (tensorPolynomialLineIso_map k R L p)
  simp only [MorphismProperty.Comma.comp_left] at h
  rw [MorphismProperty.Comma.comp_left, ← h, ← Category.assoc]
  infer_instance

/-- The concrete scalar polynomial overlap maps to the scalar extension of the
original overlap, without a supplied comparison morphism. -/
def scalarPolynomialOverlapMap :
    etalePullback pL aL ⟶ (F).obj (etalePullback p a) :=
  scalarEtalePullbackLift p a (etalePullbackFst pL aL)
    (etalePullbackSnd pL aL ≫ (scalarPunctureIso k R L).inv) (by
      apply (cancel_mono (scalarLineIso k R L).hom).mp
      simp only [Category.assoc, scalarPunctureIso_open,
        Iso.inv_hom_id_assoc]
      apply MorphismProperty.Over.Hom.ext
      exact pullback.condition)

/-- The overlap map preserves the literal original native scalar source projection. -/
@[reassoc]
theorem scalarPolynomialOverlapMap_fst :
    scalarPolynomialOverlapMap k R L p ≫ (F).map (etalePullbackFst p a) =
      etalePullbackFst pL aL :=
  scalarEtalePullbackLift_fst _ _ _ _ _

/-- The second projection retains the canonical Laurent puncture comparison. -/
@[reassoc]
theorem scalarPolynomialOverlapMap_snd :
    scalarPolynomialOverlapMap k R L p ≫ (F).map (etalePullbackSnd p a) =
      etalePullbackSnd pL aL ≫ (scalarPunctureIso k R L).inv :=
  scalarEtalePullbackLift_snd _ _ _ _ _

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
