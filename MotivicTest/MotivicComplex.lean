/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.Complex
public import Lean.Util.CollectAxioms

/-! # Canonical motivic complex: concrete input, signed shift, and term dictionaries -/

@[expose] public noncomputable section

open _root_.CategoryTheory.SingularComplex.Indexing (singularDegree)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers
open scoped Simplicial

universe u

namespace MotivicTest.MotivicComplex

variable (k : Type u) [Field k]

/-- The canonical definition works over every field without extra hypotheses. -/
def overEveryField (q : ℕ) : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  motivicComplex k q

example (q : ℕ) : motivicComplex k q =
    (singularSheafCochainComplex k (reducedTorus k q) 0)⟦-(q : ℤ)⟧ := rfl

example (q : ℕ) (i j l : ℤ) :
    (motivicComplex k q).d i j ≫ (motivicComplex k q).d j l = 0 :=
  motivicComplex_d_squared k q i j l

example (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicComplex k q).X i) := isZero_motivicComplex_X k q i hi

example (q : ℕ) (i : ℤ) : IsNisnevichSheaf k ((motivicComplex k q).X i).obj :=
  motivicComplex_X_isNisnevichSheaf k q i

/-- Term identification with literal relative products before sheafification. -/
example (q r : ℕ) (U : SmoothSite (Spec (.of k))) :
    (motivicSingularPresheaf k q r).obj (op U) =
      sections (reducedTorus k q) (Cor.simplexProduct (Cor.mk U) r) := rfl

example (q r : ℕ) {U V : SmoothSite (Spec (.of k))} (f : U ⟶ V) :
    (motivicSingularPresheaf k q r).map f.op =
      transfer (reducedTorus k q) ((Cor.graphFunctor k).map
        (SmoothSite.productMap f (𝟙 ((cosimplicialSmoothSite k).obj ⦋r⦌)))) :=
  motivicSingularPresheaf_map k q r f

/-- The coefficients at every product are actual quotient groups of signed cycles. -/
def productQuotient (q r : ℕ) (U : SmoothSite (Spec (.of k))) :
    (motivicSingularPresheaf k q r).obj (op U) ≅
      AddCommGrpCat.of
        (sections (torusRepresentable k q) (Cor.simplexProduct (Cor.mk U) r) ⧸
          torusIdentityRelations k q (Cor.simplexProduct (Cor.mk U) r)) :=
  reducedTorusSectionsIsoQuotient k q (Cor.simplexProduct (Cor.mk U) r)

/-- Actual identity axes, rather than arbitrary selected relations, are killed. -/
example (q : ℕ) (i : Fin q) :
    torusIdentityAxis k q i ≫ toReducedTorus k q = 0 :=
  torusIdentityAxis_toReducedTorus k q i

/-- The comparison is a natural isomorphism before specializing the coefficient. -/
example (q : ℕ) {P Q : PresheafWithTransfers.{u + 1} k} (η : P ⟶ Q) :
    (singularSheafCochainFunctor k q).map η ≫
        (motivicComplexPlacementNatIso k q).hom.app Q =
      (motivicComplexPlacementNatIso k q).hom.app P ≫
        (motivicComplexFunctor k q).map η :=
  (motivicComplexPlacementNatIso k q).hom.naturality η

example (q r : ℕ) :
    (motivicComplexPlacementIso k q).hom.f (singularDegree q r) =
      (-1 : ℤ) ^ (q * r) •
        ((singularSheafCochainXIso k (reducedTorus k q) q r).hom ≫
          (motivicComplexXIso k q r).inv) :=
  motivicComplexPlacementIso_hom_f k q r

/-- The actual ordinary sheaf is the Nisnevich sheafification of the literal product presheaf. -/
def ordinaryTerm (q r : ℕ) :
    (SheafWithTransfers.toSheaf k).obj
        ((motivicComplex k q).X (singularDegree q r)) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj (motivicSingularPresheaf k q r) :=
  motivicComplexUnderlyingXIso k q r

/-- It also compares to the existing ordinary singular construction. -/
def ordinarySingularTerm (q r : ℕ) := motivicComplexOrdinaryXIso k q r

/-- Weight zero uses the genuine representable of the base scheme. -/
def weightZeroInput : motivicComplex k 0 ≅
    singularSheafCochainComplex k
      ((representableLarge k).obj (Cor.mk (SmoothSite.base (Spec (.of k))))) 0 :=
  motivicComplexZeroInputIso k

example : (motivicComplex k 1).X 0 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 1)).X 1) :=
  motivicComplexOneXZeroIso k

example : (motivicComplex k 1).X 1 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 1)).X 0) :=
  motivicComplexOneXOneIso k

example : (motivicComplex k 2).X 1 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 2)).X 1) :=
  motivicComplexTwoXOneIso k

example : (motivicComplex k 2).X 2 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 2)).X 0) :=
  motivicComplexTwoXTwoIso k

/-- The arbitrary-degree dictionary includes negative cochain degrees. -/
example : (motivicComplex k 2).X (-4) ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 2)).X 6) :=
  motivicComplexXIso k 2 6

example : IsZero ((motivicComplex k 2).X 3) :=
  isZero_motivicComplex_X k 2 3 (by norm_num)

/-- The first odd-weight comparison component explicitly carries minus one. -/
example : (motivicComplexPlacementIso k 1).hom.f 0 =
    -((singularSheafCochainXIso k (reducedTorus k 1) 1 1).hom ≫
      (motivicComplexOneXZeroIso k).inv) := by
  have h := motivicComplexPlacementIso_one_hom_f k 1
  change (motivicComplexPlacementIso k 1).hom.f 0 = (-1 : ℤ) •
    ((singularSheafCochainXIso k (reducedTorus k 1) 1 1).hom ≫
      (motivicComplexOneXZeroIso k).inv) at h
  simpa only [neg_one_zsmul] using h

/-- All even-weight comparison components carry positive sign. -/
example (r : ℕ) :
    (motivicComplexPlacementIso k 2).hom.f (singularDegree 2 r) =
      (singularSheafCochainXIso k (reducedTorus k 2) 2 r).hom ≫
        (motivicComplexXIso k 2 r).inv := motivicComplexPlacementIso_two_hom_f k r

/-- Weight two has literally the sheafified face-zero minus face-one differential. -/
example : (motivicComplex k 2).d 1 2 =
    (motivicComplexTwoXOneIso k).hom ≫
      ((nisnevichSheafify k).map (singularFace (reducedTorus k 2) 0 (0 : Fin 2)) -
        (nisnevichSheafify k).map (singularFace (reducedTorus k 2) 0 (1 : Fin 2))) ≫
      (motivicComplexTwoXTwoIso k).inv := motivicComplex_two_d_one_two k

/-- Weight one retains mathlib's necessary negative shift sign. -/
example : (motivicComplex k 1).d 0 1 =
    -((motivicComplexOneXZeroIso k).hom ≫
      ((nisnevichSheafify k).map (singularFace (reducedTorus k 1) 0 (0 : Fin 2)) -
        (nisnevichSheafify k).map (singularFace (reducedTorus k 1) 0 (1 : Fin 2))) ≫
      (motivicComplexOneXOneIso k).inv) := motivicComplex_one_d_zero_one k

open Lean in
run_cmd do
  for name in #[``motivicComplexFunctor, ``motivicComplex, ``motivicComplex_eq,
      ``motivicComplexPlacementNatIso, ``motivicComplexPlacementIso,
      ``motivicComplexXIso, ``motivicComplexPlacementIso_hom_f,
      ``motivicComplexPlacementIso_comm, ``motivicComplex_d_squared,
      ``isZero_motivicComplex_X, ``motivicComplex_X_isNisnevichSheaf,
      ``motivicSingularPresheaf, ``motivicSingularPresheaf_obj, ``motivicSingularPresheaf_map,
      ``motivicComplexUnderlyingXIso, ``motivicComplexOrdinaryXIso,
      ``motivicComplexZeroInputIso, ``motivicComplexOneXZeroIso, ``motivicComplexOneXOneIso,
      ``motivicComplexTwoXOneIso, ``motivicComplexTwoXTwoIso,
      ``motivicComplexPlacementIso_one_hom_f, ``motivicComplexPlacementIso_two_hom_f,
      ``motivicComplex_d, ``motivicComplex_d_faces, ``motivicComplex_two_d_one_two,
      ``motivicComplex_one_d_zero_one, ``overEveryField, ``productQuotient,
      ``ordinaryTerm, ``ordinarySingularTerm, ``weightZeroInput] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The canonical motivic complex uses only standard Lean foundations."

end MotivicTest.MotivicComplex
