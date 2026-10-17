/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Residue degree of a morphism between spectra of fields

The canonical identification of a field with the residue field of its spectrum
is evaluation of its actual global section. Naturality therefore identifies
the geometric residue action with the original field map. No finite-dimensional
or separability hypothesis is needed for the resulting equality of finranks.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical identification of a field with the residue field of its
spectrum at its unique point. -/
def Spec.fieldEquivResidueField (K : Type u) [Field K] (x : Spec (.of K)) :
    K ≃+* (Spec (.of K)).residueField x :=
  x.asIdeal.algEquivResidueFieldOfField.toRingEquiv.trans
    (Spec.residueFieldIso (.of K) x).symm.commRingCatIsoToRingEquiv

/-- The canonical field identification is the actual global evaluation map. -/
theorem Spec.fieldEquivResidueField_eq_evaluation (K : Type u) [Field K]
    (x : Spec (.of K)) :
    CommRingCat.ofHom (Spec.fieldEquivResidueField K x).toRingHom =
      (ΓSpecIso (.of K)).inv ≫ (Spec (.of K)).Γevaluation x := by
  change CommRingCat.ofHom (algebraMap K x.asIdeal.ResidueField) ≫
    (Spec.residueFieldIso (.of K) x).inv = _
  exact Spec.algebraMap_residueFieldIso_inv (.of K) x

/-- The actual geometric residue map commutes with the original field map,
under canonical field-to-residue identifications. -/
theorem Spec.fieldEquivResidueField_naturality {F E : Type u} [Field F] [Field E]
    (φ : F →+* E) (x : Spec (.of E)) :
    CommRingCat.ofHom (Spec.fieldEquivResidueField F
        (Spec.map (CommRingCat.ofHom φ) x)).toRingHom ≫
        (Spec.map (CommRingCat.ofHom φ)).residueFieldMap x =
      CommRingCat.ofHom φ ≫
        CommRingCat.ofHom (Spec.fieldEquivResidueField E x).toRingHom := by
  rw [Spec.fieldEquivResidueField_eq_evaluation,
    Spec.fieldEquivResidueField_eq_evaluation]
  rw [Category.assoc, Γevaluation_naturality,
    ← ΓSpecIso_inv_naturality_assoc]

/-- The residue degree of the actual morphism of field spectra is the degree
of its original scalar map, including the infinite-dimensional case. -/
theorem Hom.residueDegree_SpecMap (F E : Type u) [Field F] [Field E]
    (φ : F →+* E) (x : Spec (.of E)) :
    let : Algebra F E := φ.toAlgebra
    (Spec.map (CommRingCat.ofHom φ)).residueDegree x = Module.finrank F E := by
  let : Algebra F E := φ.toAlgebra
  let f := Spec.map (CommRingCat.ofHom φ)
  let : Algebra ((Spec (.of F)).residueField (f x))
      ((Spec (.of E)).residueField x) := (f.residueFieldMap x).hom.toAlgebra
  exact (Algebra.finrank_eq_of_equiv_equiv
    (Spec.fieldEquivResidueField F (f x)) (Spec.fieldEquivResidueField E x)
    (congrArg CommRingCat.Hom.hom (Spec.fieldEquivResidueField_naturality φ x))).symm

/-- In particular the residue degree of the spectrum map of an algebra is
its actual module dimension. -/
theorem Hom.residueDegree_SpecMap_algebraMap (F E : Type u) [Field F] [Field E]
    [Algebra F E] (x : Spec (.of E)) :
    (Spec.map (CommRingCat.ofHom (algebraMap F E))).residueDegree x =
      Module.finrank F E := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap F E))
  let : Algebra ((Spec (.of F)).residueField (f x))
      ((Spec (.of E)).residueField x) := (f.residueFieldMap x).hom.toAlgebra
  exact (Algebra.finrank_eq_of_equiv_equiv
    (Spec.fieldEquivResidueField F (f x)) (Spec.fieldEquivResidueField E x)
    (congrArg CommRingCat.Hom.hom
      (Spec.fieldEquivResidueField_naturality (algebraMap F E) x))).symm

end AlgebraicGeometry.Scheme
