/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.SingularComplex.Presheaf
public import Motivic.Transfers.Presheaf.NisnevichSheafification
public import Motivic.Aglib.Algebra.Homology.Sheafification.Singular

/-!
# Degreewise sheafified singular complexes with actual transfers

The proved additive transfer-preserving Nisnevich sheafification is applied to
every term and differential. Its transfer-natural unit is a chain map, and
the construction remains functorial in the input transfer presheaf. Chain
degree `r` can also be placed in cochain degree `q-r` before sheafification.
No reduced torus, normalization, or motivic-complex identification is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.SingularComplex

variable (k : Type u) [Field k]
/-- Apply actual transfer-preserving sheafification in each singular chain degree. -/
def singularSheafFunctor : PresheafWithTransfers.{u + 1} k ⥤
    ChainComplex (SheafWithTransfers.{u + 1} k) ℕ :=
  singularComplexFunctor ⋙ (nisnevichSheafify k).mapHomologicalComplex (ComplexShape.down ℕ)

/-- The singular chain complex of actual Nisnevich sheaves with transfers. -/
abbrev singularSheafComplex (P : PresheafWithTransfers.{u + 1} k) :
    ChainComplex (SheafWithTransfers.{u + 1} k) ℕ :=
  (singularSheafFunctor k).obj P

@[simp]
theorem singularSheafComplex_X (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    (singularSheafComplex k P).X n = (nisnevichSheafify k).obj ((singularComplex P).X n) := rfl

@[simp]
theorem singularSheafComplex_d (P : PresheafWithTransfers.{u + 1} k) (i j : ℕ) :
    (singularSheafComplex k P).d i j =
      (nisnevichSheafify k).map ((singularComplex P).d i j) := rfl

/-- Coefficient morphisms induce actual maps of sheaf complexes with transfers. -/
@[simp]
theorem singularSheafFunctor_map_f {P Q : PresheafWithTransfers.{u + 1} k}
    (η : P ⟶ Q) (n : ℕ) :
    ((singularSheafFunctor k).map η).f n =
      (nisnevichSheafify k).map ((singularComplexMap η).f n) := rfl

/-- The degreewise transfer-natural unit is a genuine map of singular complexes. -/
def singularSheafUnit : singularComplexFunctor ⟶ singularSheafFunctor k ⋙
    (SheafWithTransfers.forget k).mapHomologicalComplex (ComplexShape.down ℕ) where
  app P :=
    { f n := toNisnevichSheafify k ((singularComplex P).X n)
      comm' i j _ := (toNisnevichSheafify_naturality k ((singularComplex P).d i j)).symm }
  naturality P Q η := by
    ext n : 1
    exact toNisnevichSheafify_naturality k ((singularComplexMap η).f n)

@[simp]
theorem singularSheafUnit_app_f (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    ((singularSheafUnit k).app P).f n =
      toNisnevichSheafify k ((singularComplex P).X n) := rfl

/-- Place the transfer complex in degrees `q-r`, then sheafify degreewise. -/
def singularSheafCochainFunctor (q : ℕ) : PresheafWithTransfers.{u + 1} k ⥤
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  singularCochainFunctor q ⋙ (nisnevichSheafify k).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The placed, degreewise-sheafified complex of actual sheaves with transfers. -/
abbrev singularSheafCochainComplex (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  (singularSheafCochainFunctor k q).obj P

/-- The term at `q-r` is exactly sheafification of the original degree-`r` transfer presheaf. -/
def singularSheafCochainXIso (P : PresheafWithTransfers.{u + 1} k) (q r : ℕ) :
    (singularSheafCochainComplex k P q).X (Indexing.singularDegree q r) ≅
      (nisnevichSheafify k).obj ((singularComplex P).X r) :=
  (nisnevichSheafify k).mapIso (singularCochainXIso P q r)

/-- Sheafified terms above the stated weight vanish. -/
theorem isZero_singularSheafCochainComplex_X (P : PresheafWithTransfers.{u + 1} k)
    (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((singularSheafCochainComplex k P q).X i) :=
  (nisnevichSheafify k).map_isZero (isZero_singularCochainComplex_X P q i hi)

/-- The placed differential is sheafification of the exact alternating differential. -/
theorem singularSheafCochainComplex_d (P : PresheafWithTransfers.{u + 1} k) (q r : ℕ) :
    (singularSheafCochainComplex k P q).d (Indexing.singularDegree q (r + 1))
        (Indexing.singularDegree q r) =
      (singularSheafCochainXIso k P q (r + 1)).hom ≫
        (nisnevichSheafify k).map ((singularComplex P).d (r + 1) r) ≫
        (singularSheafCochainXIso k P q r).inv := by
  change (nisnevichSheafify k).map ((singularCochainComplex P q).d _ _) = _
  rw [singularCochainComplex_d]
  simp only [Functor.map_comp]
  rfl

/-- The placed complex has the same canonical, transfer-natural sheafification unit. -/
def singularSheafCochainUnit (q : ℕ) : singularCochainFunctor q ⟶
    singularSheafCochainFunctor k q ⋙
      (SheafWithTransfers.forget k).mapHomologicalComplex (ComplexShape.up ℤ) where
  app P :=
    { f n := toNisnevichSheafify k ((singularCochainComplex P q).X n)
      comm' i j _ :=
        (toNisnevichSheafify_naturality k ((singularCochainComplex P q).d i j)).symm }
  naturality P Q η := by
    ext n : 1
    exact toNisnevichSheafify_naturality k (((singularCochainFunctor q).map η).f n)

section OrdinaryComparison

/-- Forgetting transfers commutes with sheafification of the entire singular complex. -/
def singularSheafUnderlyingIso (P : PresheafWithTransfers.{u + 1} k) :
    ((toPresheaf k ⋙ presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (singularComplex P) ≅
    ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (singularSheafComplex k P) :=
  (NatIso.mapHomologicalComplex (nisnevichSheafificationUnderlyingIso k)
    (ComplexShape.down ℕ)).app (singularComplex P)

/-- Forgetting transfers identifies this complex with the pre-existing ordinary
Nisnevich-sheafified singular complex, using the actual product comparison. -/
def singularSheafOrdinaryIso (P : PresheafWithTransfers.{u + 1} k) :
    ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (singularSheafComplex k P) ≅
      SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (_root_.AlgebraicSimplex.cosimplicialSmoothSite k) ((toPresheaf k).obj P) :=
  (singularSheafUnderlyingIso k P).symm ≪≫
    ((presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
        (singularComplexUnderlyingIso P)

end OrdinaryComparison

/-- Actual additive transfer sheafification preserves the signed-shift comparison naturally. -/
def singularSheafCochainShiftNatIso (q : ℕ) :
    singularSheafCochainFunctor k q ≅
      singularSheafCochainFunctor k 0 ⋙ CategoryTheory.shiftFunctor
        (CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) (-(q : ℤ)) :=
  isoWhiskerRight (singularCochainShiftNatIso q)
      ((nisnevichSheafify k).mapHomologicalComplex (ComplexShape.up ℤ)) ≪≫
    isoWhiskerLeft (singularCochainFunctor 0)
      ((nisnevichSheafify k).mapCochainComplexShiftIso (-(q : ℤ)))

/-- Sheafified transfer cochains in weight `q` are the actual signed shift of weight zero. -/
def singularSheafCochainShiftIso (P : PresheafWithTransfers.{u + 1} k) (q : ℕ) :
    singularSheafCochainComplex k P q ≅ (singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧ :=
  (singularSheafCochainShiftNatIso k q).app P

/-- The shifted sheaf term identified with sheafification of singular degree `r`. -/
def singularSheafShiftedCochainXIso (P : PresheafWithTransfers.{u + 1} k) (q r : ℕ) :
    ((singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧).X
        (Indexing.singularDegree q r) ≅
      (nisnevichSheafify k).obj ((singularComplex P).X r) :=
  (nisnevichSheafify k).mapIso (singularShiftedCochainXIso P q r)

/-- The sheafified comparison has precisely the original `(-1)^(q*r)` sign. -/
theorem singularSheafCochainShiftIso_hom_f (P : PresheafWithTransfers.{u + 1} k)
    (q r : ℕ) :
    (singularSheafCochainShiftIso k P q).hom.f (Indexing.singularDegree q r) =
      (-1 : ℤ) ^ (q * r) •
        ((singularSheafCochainXIso k P q r).hom ≫
          (singularSheafShiftedCochainXIso k P q r).inv) := by
  change (nisnevichSheafify k).map
      ((singularCochainShiftIso P q).hom.f (Indexing.singularDegree q r)) ≫ 𝟙 _ = _
  rw [Category.comp_id, singularCochainShiftIso_hom_f,
    CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_comp]
  rfl

/-- The actual shifted differential has exactly the standard shift sign `(-1)^q`. -/
theorem singularSheafShiftedCochain_d (P : PresheafWithTransfers.{u + 1} k) (q r s : ℕ) :
    ((singularSheafCochainComplex k P 0)⟦-(q : ℤ)⟧).d
        (Indexing.singularDegree q r) (Indexing.singularDegree q s) =
      (-1 : ℤ) ^ q •
        ((singularSheafShiftedCochainXIso k P q r).hom ≫
          (nisnevichSheafify k).map ((singularComplex P).d r s) ≫
            (singularSheafShiftedCochainXIso k P q s).inv) := by
  calc
    _ = (nisnevichSheafify k).map
        (((singularCochainComplex P 0)⟦-(q : ℤ)⟧).d
          (Indexing.singularDegree q r) (Indexing.singularDegree q s)) := by
      simp only [CochainComplex.shiftFunctor_obj_d', Units.smul_def,
        CategoryTheory.Functor.map_zsmul]
      rfl
    _ = _ := by
      change (nisnevichSheafify k).map
          ((((singularComplex P).extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
            ((q : ℤ) - r) ((q : ℤ) - s)) =
        (-1 : ℤ) ^ q •
          ((nisnevichSheafify k).map
              (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (singularComplex P) q r
                  rfl).hom ≫
            (nisnevichSheafify k).map ((singularComplex P).d r s) ≫
              (nisnevichSheafify k).map
                (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso (singularComplex P) q s
                    rfl).inv)
      simpa only [Units.smul_def, CategoryTheory.Functor.map_zsmul,
        CategoryTheory.Functor.map_comp, Int.negOnePow_neg, Int.coe_negOnePow_natCast] using
        congrArg (fun f => (nisnevichSheafify k).map f)
          (_root_.HomologicalComplex.ExtensionSignedShift.shifted_d (singularComplex P) q r s)

/-- Weight two retains positive signs after genuine transfer sheafification. -/
theorem singularSheafCochainShiftIso_two_hom_f (P : PresheafWithTransfers.{u + 1} k)
    (r : ℕ) :
    (singularSheafCochainShiftIso k P 2).hom.f (Indexing.singularDegree 2 r) =
      (singularSheafCochainXIso k P 2 r).hom ≫
        (singularSheafShiftedCochainXIso k P 2 r).inv := by
  simp [singularSheafCochainShiftIso_hom_f, pow_mul]

end Motivic.PresheafWithTransfers
