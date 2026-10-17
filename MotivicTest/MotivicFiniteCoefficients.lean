/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.FiniteCoefficients
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Motivic finite-coefficient consumers

These tests use the actual canonical transfer-sheaf complex, its distinguished
coefficient triangle, the ordinary forgetful cone comparison, composite levels,
weight two and the level-one contraction. Characteristic two and level six
explicitly occur together, with no invertibility assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers

universe u

namespace MotivicTest.MotivicFiniteCoefficients

variable (k : Type u) [Field k]

/-- The construction works in every weight and level over an arbitrary field. -/
def overEveryField (q n : ℕ) : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ :=
  motivicFiniteComplex k q n

example (q n : ℕ) : motivicFiniteComplex k q n =
    CochainComplex.mappingCone (n • 𝟙 (motivicComplex k q)) :=
  motivicFiniteComplex_eq k q n

/-- The constructed cone retains Nisnevich descent and actual signed transfers. -/
example (q n : ℕ) (i : ℤ) :
    IsNisnevichSheaf k ((motivicFiniteComplex k q n).X i).obj :=
  motivicFiniteComplex_X_isNisnevichSheaf k q n i

/-- The degreewise biproduct uses adjacent terms of the actual canonical complex. -/
def coefficientTerm (q n : ℕ) (i : ℤ) : (motivicFiniteComplex k q n).X i ≅
    (motivicComplex k q).X (i + 1) ⊞ (motivicComplex k q).X i :=
  motivicFiniteComplexXIso k q n i

example (q n : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero ((motivicFiniteComplex k q n).X i) :=
  isZero_motivicFiniteComplex_X k q n i hi

example (q n : ℕ) (i j l : ℤ) :
    (motivicFiniteComplex k q n).d i j ≫ (motivicFiniteComplex k q n).d j l = 0 :=
  (motivicFiniteComplex k q n).d_comp_d i j l

/-- The source-arrow transfer action commutes with the actual integral coefficient map. -/
example (q n : ℕ) (i : ℤ) {X Y : Cor k} (α : X ⟶ Y) :
    transfer ((motivicComplex k q).X i).obj α ≫
        ((motivicFiniteComplex.integral k q n).f i).hom.hom.app (op X) =
      ((motivicFiniteComplex.integral k q n).f i).hom.hom.app (op Y) ≫
        transfer ((motivicFiniteComplex k q n).X i).obj α :=
  transfer_naturality ((motivicFiniteComplex.integral k q n).f i).hom α

/-- This is the cone on the canonical ordinary motivic sheaf complex, up to an actual iso. -/
def ordinaryCone (q n : ℕ) :
    ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (.up ℤ)).obj
        (motivicFiniteComplex k q n) ≅
      finiteCoefficients (motivicSheafComplex k q) n :=
  motivicFiniteComplexUnderlyingIso k q n

/-- A real composite-level triangle is distinguished in the homotopy category. -/
example :
    (HomotopyCategory.quotient (SheafWithTransfers.{u + 1} k) (.up ℤ)).mapTriangle.obj
        (motivicFiniteComplex.triangle k 2 6) ∈
      distTriang
        (HomotopyCategory (SheafWithTransfers.{u + 1} k) (.up ℤ)) :=
  motivicFiniteComplex.triangle_distinguished k 2 6

example : (motivicFiniteComplex.triangle k 2 6).mor₁ = 6 • 𝟙 (motivicComplex k 2) := rfl
example : (motivicFiniteComplex.triangle k 2 6).mor₂ =
    motivicFiniteComplex.integral k 2 6 := rfl
example : (motivicFiniteComplex.triangle k 2 6).mor₃ =
    motivicFiniteComplex.bockstein k 2 6 := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In weight two, the integral coordinate contains the genuine two-face motivic differential. -/
theorem weightTwoCompositeDifferential :
    (motivicFiniteComplex k 2 6).d 1 2 ≫ motivicFiniteComplex.a k 2 6 2 =
      motivicFiniteComplex.a k 2 6 1 ≫ (motivicComplexTwoXOneIso k).hom ≫
        ((nisnevichSheafify k).map (singularFace (reducedTorus k 2) 0 (0 : Fin 2)) -
          (nisnevichSheafify k).map (singularFace (reducedTorus k 2) 0 (1 : Fin 2))) ≫
        (motivicComplexTwoXTwoIso k).inv - 6 • motivicFiniteComplex.b k 2 6 1 := by
  refine (motivicFiniteComplex.d_a k 2 6 1).trans ?_
  have hd := congrArg (fun f => motivicFiniteComplex.a k 2 6 1 ≫ f)
    (motivicComplex_two_d_one_two k)
  have h := congrArg (fun f => f - 6 •
    (show (motivicFiniteComplex k 2 6).X 1 ⟶ (motivicComplex k 2).X 2 from
      motivicFiniteComplex.b k 2 6 1)) hd
  simpa [Category.assoc] using h

example (i : ℤ) :
    (motivicFiniteComplex k 2 6).d i (i + 1) ≫ motivicFiniteComplex.b k 2 6 (i + 1) =
      -(motivicFiniteComplex.b k 2 6 i ≫ (motivicComplex k 2).d (i + 1) (i + 1 + 1)) :=
  motivicFiniteComplex.d_b k 2 6 i

/-- The degree-one connecting arrow has the integral degree-two term as its signed coordinate. -/
example :
    (motivicFiniteComplex.bockstein k 2 6).f 1 = motivicFiniteComplex.b k 2 6 1 ≫
      ((motivicComplex k 2).shiftFunctorObjXIso 1 1 2 rfl).inv :=
  motivicFiniteComplex.bockstein_f k 2 6 1

/-- Reduction from six to two scales the positive coordinate by three. -/
example (i : ℤ) :
    (motivicFiniteComplex.reduction k 2 2 3).f i ≫ motivicFiniteComplex.b k 2 2 i =
      3 • motivicFiniteComplex.b k 2 6 i :=
  motivicFiniteComplex.reduction_b k 2 2 3 i

example (i : ℤ) :
    (motivicFiniteComplex.insertion k 2 2 3).f i ≫ motivicFiniteComplex.a k 2 6 i =
      3 • motivicFiniteComplex.a k 2 2 i :=
  motivicFiniteComplex.insertion_a k 2 2 3 i

example : motivicFiniteComplex.insertion k 2 2 3 ≫ motivicFiniteComplex.reduction k 2 2 3 =
    3 • 𝟙 (motivicFiniteComplex k 2 2) :=
  motivicFiniteComplex.insertion_reduction k 2 2 3

example : motivicFiniteComplex.reduction k 2 2 3 ≫ motivicFiniteComplex.insertion k 2 2 3 =
    3 • 𝟙 (motivicFiniteComplex k 2 6) :=
  motivicFiniteComplex.reduction_insertion k 2 2 3

/-- Every actual transfer-coefficient morphism is sent to a finite-coefficient chain map. -/
example (q n : ℕ) {P Q R : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) (g : Q ⟶ R) :
    (motivicFiniteComplexFunctor k q n).map (f ≫ g) =
      (motivicFiniteComplexFunctor k q n).map f ≫
        (motivicFiniteComplexFunctor k q n).map g :=
  (motivicFiniteComplexFunctor k q n).map_comp f g

/-- The integral map is natural in the original transfer coefficient. -/
example (q n : ℕ) {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    finiteCoefficients.integral ((motivicComplexFunctor k q).obj P) n ≫
        (motivicFiniteComplexFunctor k q n).map f =
      (motivicComplexFunctor k q).map f ≫
        finiteCoefficients.integral ((motivicComplexFunctor k q).obj Q) n :=
  finiteCoefficients.integral_naturality n ((motivicComplexFunctor k q).map f)

/-- The connecting morphism is natural in the actual transfer coefficient as well. -/
example (q n : ℕ) {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    (motivicFiniteComplexFunctor k q n).map f ≫
        finiteCoefficients.bockstein ((motivicComplexFunctor k q).obj Q) n =
      finiteCoefficients.bockstein ((motivicComplexFunctor k q).obj P) n ≫
        ((motivicComplexFunctor k q).map f)⟦(1 : ℤ)⟧' :=
  finiteCoefficients.bockstein_naturality n ((motivicComplexFunctor k q).map f)

/-- Composite coefficient reduction is natural in every map of the actual integral complex. -/
example (f : motivicComplex k 2 ⟶ motivicComplex k 2) :
    finiteCoefficients.map 6 f ≫ motivicFiniteComplex.reduction k 2 2 3 =
      motivicFiniteComplex.reduction k 2 2 3 ≫ finiteCoefficients.map 2 f :=
  finiteCoefficients.reduction_naturality (motivicComplex k 2) 2 f 3

/-- Level one is included and comes with a real transfer-natural nullhomotopy. -/
def levelOne (q : ℕ) : Homotopy (𝟙 (motivicFiniteComplex k q 1)) 0 :=
  motivicFiniteComplex.contractionOne k q

example (q : ℕ) (i : ℤ) : IsZero ((motivicFiniteSheafComplex k q 1).homology i) :=
  isZero_motivicFiniteSheafComplex_homology_one k q i

/-- An actual characteristic-two, composite-level consumer needs no invertibility evidence. -/
def characteristicTwoComposite :
    CochainComplex (SheafWithTransfers.{1} (ZMod 2)) ℤ :=
  motivicFiniteComplex (ZMod 2) 2 6

open Lean in
run_cmd do
  for name in #[``CategoryTheory.Functor.additive_of_isLimit,
      ``motivicFiniteComplexFunctor, ``motivicFiniteComplex, ``motivicFiniteComplex_eq,
      ``motivicFiniteComplexFunctor_obj, ``motivicFiniteComplexXIso,
      ``motivicFiniteComplex_X_isNisnevichSheaf, ``isZero_motivicFiniteComplex_X,
      ``motivicFiniteSheafComplex, ``motivicFiniteComplexUnderlyingIso,
      ``motivicFiniteComplex.triangle, ``motivicFiniteComplex.integral,
      ``motivicFiniteComplex.bockstein, ``motivicFiniteComplex.a, ``motivicFiniteComplex.b,
      ``motivicFiniteComplex.d_a, ``motivicFiniteComplex.d_b,
      ``motivicFiniteComplex.bockstein_f, ``motivicFiniteComplex.triangle_distinguished,
      ``motivicFiniteComplex.reduction, ``motivicFiniteComplex.insertion,
      ``motivicFiniteComplex.insertion_reduction, ``motivicFiniteComplex.reduction_insertion,
      ``motivicFiniteComplex.contractionOne, ``motivicFiniteSheafComplexContractionOne,
      ``isZero_motivicFiniteSheafComplex_homology_one, ``weightTwoCompositeDifferential,
      ``levelOne, ``characteristicTwoComposite] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Motivic coefficient cones and their transfer enhancement use only standard foundations."

end MotivicTest.MotivicFiniteCoefficients
