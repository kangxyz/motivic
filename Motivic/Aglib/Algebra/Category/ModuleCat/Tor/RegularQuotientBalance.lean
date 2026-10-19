/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.KoszulResolutionTensor
public import Motivic.Aglib.Algebra.Homology.Koszul.TensorQuasiIso
public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteTor

/-!
# Actual Tor balancing against a regular-sequence quotient

For an arbitrary coefficient module and a quotient by a ring-weakly-regular
finite list, the two actual one-sided categorical Tor modules are isomorphic.
Both are compared to the homology of the same constructed tensor of a finite
Koszul resolution and an arbitrary projective resolution. The isomorphism is
proved; no general Tor symmetry or balancing theorem is assumed.

This is a regular-quotient balancing prerequisite for diagonal reduction. It
is not the four-factor to triple-product change-of-ambient theorem.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open _root_.ChainComplex.Koszul

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R]

/-- Coefficient Koszul recursion is precisely the right-associated tensor recursion. -/
theorem coefficientComplex_eq_iteratedKoszulTensor (M : ModuleCat.{u} R) (s : List R) :
    coefficientComplex M s =
      iteratedKoszulTensor s ((ChainComplex.single₀ (ModuleCat R)).obj M) := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [coefficientComplex_cons, iteratedKoszulTensor, ih]

/-- The coefficient complex is the actual tensor with the module in degree zero. -/
def coefficientComplexTensorIso (M : ModuleCat.{u} R) (s : List R) :
    coefficientComplex M s ≅ HomologicalComplex.tensorObj (chainComplex s)
      ((ChainComplex.single₀ (ModuleCat R)).obj M) :=
  eqToIso (coefficientComplex_eq_iteratedKoszulTensor M s) ≪≫
    iteratedKoszulTensorIso s ((ChainComplex.single₀ (ModuleCat R)).obj M)

/-- Genuine balancing of the actual one-sided Tor functor when one module is
an actual regular-sequence quotient. The other module is wholly unrestricted. -/
def regularQuotientTorIso (M : ModuleCat.{u} R) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) :
    ((Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R (R ⧸ Ideal.ofList s)) ≅
      ((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))).obj M :=
  finiteTorIsoHomology M s hs n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (coefficientComplexTensorIso M s) ≪≫
    (tensorResolutionHomologyIso s (projectiveResolution M) n).symm ≪≫
    projectiveResolutionTensorHomologyIso M (projectiveResolution M) s hs n ≪≫
    ((projectiveResolution M).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))) n).symm

end ModuleCat.TorComparison
