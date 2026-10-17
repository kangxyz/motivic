/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.Hypercohomology
public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.Limits
public import Motivic.Algebra.Homology.FiniteCoefficients

/-!
# Finite coefficients of the canonical motivic complex

`motivicFiniteComplex k q n` is the actual cone of multiplication by `n` on
`motivicComplex k q`, retaining Nisnevich sheaves with signed transfers.
Its coefficient triangle is distinguished after passing to the homotopy
category. The integral and positive Bockstein coordinates satisfy the checked
differential formulas `(a,b) ↦ (da - n b, -db)`. Reduction, insertion and an
actual level-one contraction are inherited from the existing cone algebra.

For positive `n`, these are the chain-level cone formulas associated with the
two-term free-resolution presentation `[ℤ --n--> ℤ]` of `ℤ/n`. The construction
and its signed coordinate identities are the scope proved here; no comparison
with a derived tensor functor is claimed. No invertibility assumption on `n`
is used. Forgetting transfers is canonically isomorphic to forming the same
cone on the actual ordinary motivic sheaf complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic

variable (k : Type u) [Field k]

/-- Finite coefficients remain functorial in the original transfer coefficient. -/
def motivicFiniteComplexFunctor (q n : ℕ) : PresheafWithTransfers.{u + 1} k ⥤
    CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  motivicComplexFunctor k q ⋙ finiteCoefficients.functor n

/-- Finite coefficients of the actual canonical motivic complex, with transfers. -/
def motivicFiniteComplex (q n : ℕ) : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  finiteCoefficients (motivicComplex k q) n

/-- This is literally the existing mapping-cone construction. -/
theorem motivicFiniteComplex_eq (q n : ℕ) :
    motivicFiniteComplex k q n = CochainComplex.mappingCone (n • 𝟙 (motivicComplex k q)) := rfl

/-- The coefficient functor specializes to the actual reduced transfer torus. -/
@[simp]
theorem motivicFiniteComplexFunctor_obj (q n : ℕ) :
    (motivicFiniteComplexFunctor k q n).obj (PresheafWithTransfers.reducedTorus k q) =
      motivicFiniteComplex k q n := rfl

/-- A coefficient term is the actual binary biproduct of adjacent motivic terms. -/
def motivicFiniteComplexXIso (q n : ℕ) (i : ℤ) :
    (motivicFiniteComplex k q n).X i ≅
      (motivicComplex k q).X (i + 1) ⊞ (motivicComplex k q).X i :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (n • 𝟙 (motivicComplex k q)) i (i + 1) rfl

/-- Every finite-coefficient term still has genuine ordinary Nisnevich descent. -/
theorem motivicFiniteComplex_X_isNisnevichSheaf (q n : ℕ) (i : ℤ) :
    PresheafWithTransfers.IsNisnevichSheaf k ((motivicFiniteComplex k q n).X i).obj :=
  ((motivicFiniteComplex k q n).X i).property

/-- Passing to finite coefficients introduces no terms above the weight. -/
theorem isZero_motivicFiniteComplex_X (q n : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicFiniteComplex k q n).X i) := by
  apply (CochainComplex.mappingCone.isZero_X_iff _ i).2
  exact ⟨isZero_motivicComplex_X k q (i + 1) (by omega),
    isZero_motivicComplex_X k q i hi⟩

/-- The finite-coefficient cone on the genuine ordinary motivic sheaf complex. -/
def motivicFiniteSheafComplex (q n : ℕ) :
    CochainComplex (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}) ℤ :=
  finiteCoefficients (motivicSheafComplex k q) n

/-- Forgetting transfers commutes with finite coefficients through an actual cone isomorphism. -/
def motivicFiniteComplexUnderlyingIso (q n : ℕ) :
    ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (.up ℤ)).obj
        (motivicFiniteComplex k q n) ≅ motivicFiniteSheafComplex k q n := by
  let F := (SheafWithTransfers.toSheaf k).mapHomologicalComplex (.up ℤ)
  have hmap : F.map (n • 𝟙 (motivicComplex k q)) = n • 𝟙 (F.obj (motivicComplex k q)) := by
    rw [Functor.map_nsmul]
    exact congrArg (fun f => n • f) (F.map_id (motivicComplex k q))
  exact CochainComplex.mappingCone.mapHomologicalComplexIso
      (n • 𝟙 (motivicComplex k q)) (SheafWithTransfers.toSheaf k) ≪≫
    eqToIso (by change CochainComplex.mappingCone (F.map _) = _; rw [hmap]; rfl)

namespace motivicFiniteComplex

variable (q n : ℕ)

/-- The actual coefficient triangle `ℤ(q) --n--> ℤ(q) --> ℤ/n(q) --> ℤ(q)[1]`. -/
def triangle : CategoryTheory.Pretriangulated.Triangle
    (CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) :=
  finiteCoefficients.triangle (motivicComplex k q) n

/-- Integral-to-finite coefficient map, still natural for all transfers. -/
def integral : motivicComplex k q ⟶ motivicFiniteComplex k q n :=
  finiteCoefficients.integral (motivicComplex k q) n

/-- The connecting morphism of the actual cone triangle. -/
def bockstein : motivicFiniteComplex k q n ⟶ (motivicComplex k q)⟦(1 : ℤ)⟧ :=
  finiteCoefficients.bockstein (motivicComplex k q) n

/-- The integral coordinate in every integer degree. -/
def a (i : ℤ) : (motivicFiniteComplex k q n).X i ⟶ (motivicComplex k q).X i :=
  finiteCoefficients.a (motivicComplex k q) n i

/-- The positive Bockstein coordinate, the negative first cone projection. -/
def b (i : ℤ) : (motivicFiniteComplex k q n).X i ⟶ (motivicComplex k q).X (i + 1) :=
  finiteCoefficients.b (motivicComplex k q) n i

/-- The all-degree signed integral-coordinate differential. -/
@[reassoc]
theorem d_a (i : ℤ) :
    (motivicFiniteComplex k q n).d i (i + 1) ≫ a k q n (i + 1) =
      a k q n i ≫ (motivicComplex k q).d i (i + 1) - n • b k q n i :=
  finiteCoefficients.d_a (motivicComplex k q) n i

/-- The all-degree signed Bockstein-coordinate differential. -/
@[reassoc]
theorem d_b (i : ℤ) :
    (motivicFiniteComplex k q n).d i (i + 1) ≫ b k q n (i + 1) =
      -(b k q n i ≫ (motivicComplex k q).d (i + 1) (i + 1 + 1)) :=
  finiteCoefficients.d_b (motivicComplex k q) n i

/-- The connecting map is exactly the positive coordinate and the genuine shift identification. -/
theorem bockstein_f (i : ℤ) :
    (bockstein k q n).f i = b k q n i ≫
      ((motivicComplex k q).shiftFunctorObjXIso 1 i (i + 1) rfl).inv :=
  finiteCoefficients.bockstein_f (motivicComplex k q) n i

/-- The first arrow of the coefficient triangle is genuine multiplication by the level. -/
@[simp]
theorem triangle_mor₁ : (triangle k q n).mor₁ = n • 𝟙 (motivicComplex k q) := rfl

@[simp]
theorem triangle_mor₂ : (triangle k q n).mor₂ = integral k q n := rfl

@[simp]
theorem triangle_mor₃ : (triangle k q n).mor₃ = bockstein k q n := rfl

/-- This specific coefficient triangle is distinguished in the actual homotopy category. -/
theorem triangle_distinguished :
    (HomotopyCategory.quotient (SheafWithTransfers.{u + 1} k) (.up ℤ)).mapTriangle.obj
        (triangle k q n) ∈
      distTriang
        (HomotopyCategory (SheafWithTransfers.{u + 1} k) (.up ℤ)) :=
  HomotopyCategory.mappingCone_triangleh_distinguished (n • 𝟙 (motivicComplex k q))

/-- Reduction from level `n*m` to level `n`. -/
def reduction (m : ℕ) : motivicFiniteComplex k q (n * m) ⟶ motivicFiniteComplex k q n :=
  finiteCoefficients.reduction (motivicComplex k q) n m

/-- Insertion from level `n` to level `n*m`. -/
def insertion (m : ℕ) : motivicFiniteComplex k q n ⟶ motivicFiniteComplex k q (n * m) :=
  finiteCoefficients.insertion (motivicComplex k q) n m

@[reassoc (attr := simp)]
theorem reduction_a (m : ℕ) (i : ℤ) :
    (reduction k q n m).f i ≫ a k q n i = a k q (n * m) i :=
  finiteCoefficients.reduction_a (motivicComplex k q) n m i

@[reassoc (attr := simp)]
theorem reduction_b (m : ℕ) (i : ℤ) :
    (reduction k q n m).f i ≫ b k q n i = m • b k q (n * m) i :=
  finiteCoefficients.reduction_b (motivicComplex k q) n m i

@[reassoc (attr := simp)]
theorem insertion_a (m : ℕ) (i : ℤ) :
    (insertion k q n m).f i ≫ a k q (n * m) i = m • a k q n i :=
  finiteCoefficients.insertion_a (motivicComplex k q) n m i

@[reassoc (attr := simp)]
theorem insertion_b (m : ℕ) (i : ℤ) :
    (insertion k q n m).f i ≫ b k q (n * m) i = b k q n i :=
  finiteCoefficients.insertion_b (motivicComplex k q) n m i

/-- The two coefficient operations recover scalar multiplication. -/
@[reassoc]
theorem insertion_reduction (m : ℕ) :
    insertion k q n m ≫ reduction k q n m = m • 𝟙 (motivicFiniteComplex k q n) :=
  finiteCoefficients.insertion_reduction (motivicComplex k q) n m

/-- The reverse composite recovers scalar multiplication on the larger level. -/
@[reassoc]
theorem reduction_insertion (m : ℕ) :
    reduction k q n m ≫ insertion k q n m = m • 𝟙 (motivicFiniteComplex k q (n * m)) :=
  finiteCoefficients.reduction_insertion (motivicComplex k q) n m

/-- Level one is contractible by an actual homotopy of complexes with transfers. -/
def contractionOne : Homotopy (𝟙 (motivicFiniteComplex k q 1)) 0 :=
  finiteCoefficients.contractionOne (motivicComplex k q)

end motivicFiniteComplex

/-- Level one is also contractible in the ordinary sheaf coefficient model. -/
def motivicFiniteSheafComplexContractionOne (q : ℕ) :
    Homotopy (𝟙 (motivicFiniteSheafComplex k q 1)) 0 :=
  finiteCoefficients.contractionOne (motivicSheafComplex k q)

/-- Ordinary sheaf cohomology of level one vanishes in every integer degree. -/
theorem isZero_motivicFiniteSheafComplex_homology_one (q : ℕ) (i : ℤ) :
    IsZero ((motivicFiniteSheafComplex k q 1).homology i) :=
  finiteCoefficients.isZero_homology_one (motivicSheafComplex k q) i

end Motivic
