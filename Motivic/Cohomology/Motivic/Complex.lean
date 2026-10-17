/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.SheafifiedSingularComplex

/-!
# The canonical Suslin–Voevodsky motivic complex

For every field `k` and nonnegative weight `q`, `motivicComplex k q` is the
actual signed cochain shift by `-q` of the degreewise Nisnevich sheafification
of the singular complex of `ℤ_tr(𝔾ₘ^∧q)`. The input is the quotient of actual
finite-correspondence representables by all genuine identity-coordinate axes.
Its differential comes from actual algebraic-simplex cofaces.

The sign-preserving placement in degree `q-r` is naturally isomorphic to this
canonical signed shift, with component sign `(-1)^(q*r)`. Both transfer-sheaf
and ordinary Nisnevich-sheaf term dictionaries are provided. These are
constructions and convention comparisons over an arbitrary field; no weight
computation, hypercohomology identification, or higher-Chow comparison is
asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe u

namespace Motivic

open PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The actual signed-shift construction, functorial in the transfer coefficient. -/
def motivicComplexFunctor (q : ℕ) : PresheafWithTransfers.{u + 1} k ⥤
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  singularSheafCochainFunctor k 0 ⋙ CategoryTheory.shiftFunctor
    (CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) (-(q : ℤ))

/-- The Suslin–Voevodsky motivic complex: actual Nisnevich-sheafified singular
chains of the reduced transfer torus, in mathlib's signed shift by `-q`. -/
def motivicComplex (q : ℕ) : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  (motivicComplexFunctor k q).obj (reducedTorus k q)

/-- The defining shift is mathlib's genuine cochain shift, including its sign. -/
theorem motivicComplex_eq (q : ℕ) :
    motivicComplex k q =
      (singularSheafCochainComplex k (reducedTorus k q) 0)⟦-(q : ℤ)⟧ := rfl

/-- Natural signed comparison with the sign-preserving `q-r` placement. -/
def motivicComplexPlacementNatIso (q : ℕ) :
    singularSheafCochainFunctor k q ≅ motivicComplexFunctor k q :=
  singularSheafCochainShiftNatIso k q

/-- The concrete motivic complex is canonically isomorphic to the `q-r` placement. -/
def motivicComplexPlacementIso (q : ℕ) :
    singularSheafCochainComplex k (reducedTorus k q) q ≅ motivicComplex k q :=
  (motivicComplexPlacementNatIso k q).app (reducedTorus k q)

/-- In occupied degree `q-r`, the term is the actual sheafification of
`U ↦ ℤ_tr(𝔾ₘ^∧q)(U × Δʳ)`, retaining all signed transfers. -/
def motivicComplexXIso (q r : ℕ) :
    (motivicComplex k q).X (Indexing.singularDegree q r) ≅
      (nisnevichSheafify k).obj ((singularComplex (reducedTorus k q)).X r) :=
  singularSheafShiftedCochainXIso k (reducedTorus k q) q r

/-- Every occupied comparison component has precisely the sign `(-1)^(q*r)`. -/
theorem motivicComplexPlacementIso_hom_f (q r : ℕ) :
    (motivicComplexPlacementIso k q).hom.f (Indexing.singularDegree q r) =
      (-1 : ℤ) ^ (q * r) •
        ((singularSheafCochainXIso k (reducedTorus k q) q r).hom ≫
          (motivicComplexXIso k q r).inv) :=
  singularSheafCochainShiftIso_hom_f k (reducedTorus k q) q r

/-- The comparison respects all differentials, including the zero extension. -/
theorem motivicComplexPlacementIso_comm (q : ℕ) (i j : ℤ) :
    (motivicComplexPlacementIso k q).hom.f i ≫ (motivicComplex k q).d i j =
      (singularSheafCochainComplex k (reducedTorus k q) q).d i j ≫
        (motivicComplexPlacementIso k q).hom.f j :=
  (motivicComplexPlacementIso k q).hom.comm i j

/-- The actual complex has square-zero differential in all integer degrees. -/
theorem motivicComplex_d_squared (q : ℕ) (i j l : ℤ) :
    (motivicComplex k q).d i j ≫ (motivicComplex k q).d j l = 0 :=
  (motivicComplex k q).d_comp_d i j l

/-- No terms occur in degrees strictly above the weight. -/
theorem isZero_motivicComplex_X (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicComplex k q).X i) := by
  change IsZero ((singularSheafCochainComplex k (reducedTorus k q) 0).X (i + -(q : ℤ)))
  exact isZero_singularSheafCochainComplex_X k (reducedTorus k q) 0 _ (by omega)

/-- Every term is an actual Nisnevich sheaf with transfers, over any field. -/
theorem motivicComplex_X_isNisnevichSheaf (q : ℕ) (i : ℤ) :
    IsNisnevichSheaf k ((motivicComplex k q).X i).obj :=
  ((motivicComplex k q).X i).property

/-- The ordinary presheaf before sheafification uses literal relative simplex products. -/
def motivicSingularPresheaf (q r : ℕ) :
    (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (toPresheaf k).obj ((singularComplex (reducedTorus k q)).X r)

/-- Its sections are literally reduced finite correspondences on `U × Δʳ`. -/
@[simp]
theorem motivicSingularPresheaf_obj (q r : ℕ) (U : SmoothSite (Spec (.of k))) :
    (motivicSingularPresheaf k q r).obj (op U) =
      sections (reducedTorus k q) (Cor.simplexProduct (Cor.mk U) r) := rfl

/-- Ordinary restriction is the original product-map pullback through graph cycles. -/
@[simp]
theorem motivicSingularPresheaf_map (q r : ℕ)
    {U V : SmoothSite (Spec (.of k))} (f : U ⟶ V) :
    (motivicSingularPresheaf k q r).map f.op =
      transfer (reducedTorus k q) ((Cor.graphFunctor k).map
        (SmoothSite.productMap f (𝟙 ((AlgebraicSimplex.cosimplicialSmoothSite k).obj ⦋r⦌)))) := by
  change transfer (reducedTorus k q)
    (Cor.simplexExterior r ((Cor.graphFunctor k).map f)) = _
  rw [Cor.simplexExterior_graph]
  rfl

/-- Forgetting transfers gives genuine ordinary Nisnevich sheafification of the
literal product presheaf, rather than an unspecified sheaf with the same name. -/
def motivicComplexUnderlyingXIso (q r : ℕ) :
    (SheafWithTransfers.toSheaf k).obj
        ((motivicComplex k q).X (Indexing.singularDegree q r)) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj (motivicSingularPresheaf k q r) :=
  (SheafWithTransfers.toSheaf k).mapIso (motivicComplexXIso k q r) ≪≫
    ((nisnevichSheafificationUnderlyingIso k).app
      ((singularComplex (reducedTorus k q)).X r)).symm

/-- The same term agrees with the pre-existing ordinary sheafified singular
complex, through the actual categorical/literal product comparison. -/
def motivicComplexOrdinaryXIso (q r : ℕ) :
    (SheafWithTransfers.toSheaf k).obj
        ((motivicComplex k q).X (Indexing.singularDegree q r)) ≅
      (SingularComplex.sheafObj (SmoothSite.nisnevichTopology (Spec (.of k)))
        (AlgebraicSimplex.cosimplicialSmoothSite k)
          ((toPresheaf k).obj (reducedTorus k q))).X r :=
  (SheafWithTransfers.toSheaf k).mapIso (motivicComplexXIso k q r) ≪≫
    (HomologicalComplex.eval _ _ r).mapIso
      (singularSheafOrdinaryIso k (reducedTorus k q))

/-- Weight zero starts from the actual representable of the base, with no axes.
This is an input identification, not a computation of its cohomology. -/
def motivicComplexZeroInputIso : motivicComplex k 0 ≅
    singularSheafCochainComplex k
      ((representableLarge k).obj (Cor.mk (SmoothSite.base (Spec (.of k))))) 0 :=
  (shiftFunctorZero (CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) ℤ).app
      (singularSheafCochainComplex k (reducedTorus k 0) 0) ≪≫
    (singularSheafCochainFunctor k 0).mapIso (reducedTorusZeroIso k)

/-- Weight one, cochain degree zero, is the sheafified singular chain-one term. -/
def motivicComplexOneXZeroIso : (motivicComplex k 1).X 0 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 1)).X 1) :=
  motivicComplexXIso k 1 1

/-- Weight one, cochain degree one, is the sheafified singular chain-zero term. -/
def motivicComplexOneXOneIso : (motivicComplex k 1).X 1 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 1)).X 0) :=
  motivicComplexXIso k 1 0

/-- The weight-one comparison has the explicit alternating component sign. -/
theorem motivicComplexPlacementIso_one_hom_f (r : ℕ) :
    (motivicComplexPlacementIso k 1).hom.f (Indexing.singularDegree 1 r) =
      (-1 : ℤ) ^ r •
        ((singularSheafCochainXIso k (reducedTorus k 1) 1 r).hom ≫
          (motivicComplexXIso k 1 r).inv) := by
  simpa only [one_mul] using motivicComplexPlacementIso_hom_f k 1 r

/-- Weight two, cochain degree one, is the sheafified singular chain-one term. -/
def motivicComplexTwoXOneIso : (motivicComplex k 2).X 1 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 2)).X 1) :=
  motivicComplexXIso k 2 1

/-- Weight two, cochain degree two, is the sheafified singular chain-zero term. -/
def motivicComplexTwoXTwoIso : (motivicComplex k 2).X 2 ≅
    (nisnevichSheafify k).obj ((singularComplex (reducedTorus k 2)).X 0) :=
  motivicComplexXIso k 2 0

/-- The weight-two comparison has positive sign in every occupied degree. -/
theorem motivicComplexPlacementIso_two_hom_f (r : ℕ) :
    (motivicComplexPlacementIso k 2).hom.f (Indexing.singularDegree 2 r) =
      (singularSheafCochainXIso k (reducedTorus k 2) 2 r).hom ≫
        (motivicComplexXIso k 2 r).inv :=
  singularSheafCochainShiftIso_two_hom_f k (reducedTorus k 2) r

/-- The motivic differential has precisely mathlib's shift sign `(-1)^q`,
followed by sheafification of the original alternating singular differential. -/
theorem motivicComplex_d (q r s : ℕ) :
    (motivicComplex k q).d (Indexing.singularDegree q r)
        (Indexing.singularDegree q s) =
      (-1 : ℤ) ^ q •
        ((motivicComplexXIso k q r).hom ≫
          (nisnevichSheafify k).map ((singularComplex (reducedTorus k q)).d r s) ≫
            (motivicComplexXIso k q s).inv) :=
  singularSheafShiftedCochain_d k (reducedTorus k q) q r s

/-- The exact all-degree alternating-coface dictionary for the canonical complex. -/
theorem motivicComplex_d_faces (q r : ℕ) :
    (motivicComplex k q).d (Indexing.singularDegree q (r + 1))
        (Indexing.singularDegree q r) =
      (-1 : ℤ) ^ q •
        ((motivicComplexXIso k q (r + 1)).hom ≫
          (nisnevichSheafify k).map
            (∑ i : Fin (r + 2), (-1 : ℤ) ^ (i : ℕ) •
              singularFace (reducedTorus k q) r i) ≫
            (motivicComplexXIso k q r).inv) := by
  rw [motivicComplex_d, singularComplex_d]

/-- In weight two, the differential from degree one to degree two is exactly
sheafified `face₀ - face₁`, with no hidden sign. -/
theorem motivicComplex_two_d_one_two :
    (motivicComplex k 2).d 1 2 =
      (motivicComplexTwoXOneIso k).hom ≫
        ((nisnevichSheafify k).map (singularFace (reducedTorus k 2) 0 (0 : Fin 2)) -
          (nisnevichSheafify k).map (singularFace (reducedTorus k 2) 0 (1 : Fin 2))) ≫
        (motivicComplexTwoXTwoIso k).inv := by
  have h := motivicComplex_d k 2 1 0
  change (motivicComplex k 2).d 1 2 = (1 : ℤ) •
    ((motivicComplexTwoXOneIso k).hom ≫
      (nisnevichSheafify k).map ((singularComplex (reducedTorus k 2)).d 1 0) ≫
        (motivicComplexTwoXTwoIso k).inv) at h
  simpa only [one_zsmul, singularComplex_d_one_zero,
    CategoryTheory.Functor.map_sub] using h

/-- In weight one, mathlib's signed shift negates the original two-face
map; the comparison in chain degree one correspondingly has sign minus one. -/
theorem motivicComplex_one_d_zero_one :
    (motivicComplex k 1).d 0 1 =
      -((motivicComplexOneXZeroIso k).hom ≫
        ((nisnevichSheafify k).map (singularFace (reducedTorus k 1) 0 (0 : Fin 2)) -
          (nisnevichSheafify k).map (singularFace (reducedTorus k 1) 0 (1 : Fin 2))) ≫
        (motivicComplexOneXOneIso k).inv) := by
  have h := motivicComplex_d k 1 1 0
  change (motivicComplex k 1).d 0 1 = (-1 : ℤ) •
    ((motivicComplexOneXZeroIso k).hom ≫
      (nisnevichSheafify k).map ((singularComplex (reducedTorus k 1)).d 1 0) ≫
        (motivicComplexOneXOneIso k).inv) at h
  simpa only [neg_one_zsmul, singularComplex_d_one_zero,
    CategoryTheory.Functor.map_sub] using h

end Motivic
