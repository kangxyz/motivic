/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor

/-!
# Flat base change for actual categorical Tor

For a flat commutative-ring map `f : R →+* S`, scalar extension of
`Tor_n^R(M,N)` is canonically isomorphic to `Tor_n^S(S ⊗ M,S ⊗ N)`.
Both sides use mathlib's actual one-sided Tor, which resolves its second
argument. The isomorphism is in `ModuleCat S`, with the ordinary scalar
extension actions; it does not assume a quotient action or balanced Tor.

The proof extends an actual projective resolution of `N`. Scalar extension
preserves projectives by its adjunction to exact scalar restriction, and
flatness makes scalar extension exact. The monoidal scalar-extension
isomorphism commutes with the differential, and exactness identifies the
homology after scalar extension. Finally `isoLeftDerivedObj` identifies the
two actual Tor modules with these homologies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Motivic.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Scalar extension is additive, as a zero-preserving left adjoint between
module categories. -/
instance extendScalars_additive (f : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (ModuleCat.extendScalars.{u, u, u} f)
  exact Functor.additive_of_preservesBinaryBiproducts (ModuleCat.extendScalars f)

/-- Extension of scalars preserves projectives for every ring map; no flatness
is required here, because scalar restriction preserves epimorphisms. -/
theorem extendScalars_preservesProjectiveObjects (f : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} f).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj f)

/-- Flat scalar extension carries any genuine projective resolution to a
projective resolution of the scalar-extended module. -/
noncomputable def flatExtendProjectiveResolution (f : R →+* S) (hf : f.Flat)
    {N : ModuleCat.{u} R} (P : ProjectiveResolution N) :
    ProjectiveResolution ((ModuleCat.extendScalars f).obj N) := by
  letI := extendScalars_preservesProjectiveObjects f
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (ModuleCat.extendScalars f).mapProjectiveResolution P

/-- The extended resolution has the literal degreewise scalar-extended complex. -/
theorem flatExtendProjectiveResolution_complex (f : R →+* S) (hf : f.Flat)
    {N : ModuleCat.{u} R} (P : ProjectiveResolution N) :
    (flatExtendProjectiveResolution f hf P).complex =
      ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj P.complex := rfl

/-- Scalar extension commutes with coefficient tensoring as an actual chain
isomorphism. Naturality of the monoidal tensorator proves the chain condition. -/
noncomputable def extendTensorComplexIso (f : R →+* S) (M : ModuleCat.{u} R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj
        ((((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex _).obj K) ≅
      ((tensorLeft ((ModuleCat.extendScalars f).obj M)).mapHomologicalComplex _).obj
        (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K) :=
  (NatIso.mapHomologicalComplex
    (Functor.Monoidal.commTensorLeft (ModuleCat.extendScalars f) M).symm _).app K

/-- In each degree the chain comparison is the actual scalar-extension
comultiplication tensorator, not an assumed abstract comparison map. -/
theorem extendTensorComplexIso_hom_f (f : R →+* S) (M : ModuleCat.{u} R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (extendTensorComplexIso f M K).hom.f n =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars f) M (K.X n) := rfl

/-- Flat scalar extension commutes with the homology of every chain complex,
with the genuine `S`-module scalar action on both sides. -/
noncomputable def flatExtendHomologyIso (f : R →+* S) (hf : f.Flat)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (K.homology n) ≅
      (((ModuleCat.extendScalars f).mapHomologicalComplex _).obj K).homology n := by
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact ((K.sc n).mapHomologyIso (ModuleCat.extendScalars f)).symm

/-- All-degree flat base change for the actual one-sided categorical Tor.
Neither module is assumed flat or projective. The codomain ring acts on
both sides, and the second argument is the one resolved in the proof. -/
noncomputable def flatBaseChangeTorIso (f : R →+* S) (hf : f.Flat)
    (M N : ModuleCat.{u} R) (n : ℕ) :
    (ModuleCat.extendScalars f).obj (((Tor (ModuleCat R) n).obj M).obj N) ≅
      ((Tor (ModuleCat S) n).obj ((ModuleCat.extendScalars f).obj M)).obj
        ((ModuleCat.extendScalars f).obj N) :=
  (ModuleCat.extendScalars f).mapIso
      ((projectiveResolution N).isoLeftDerivedObj ((tensoringLeft (ModuleCat R)).obj M) n) ≪≫
    flatExtendHomologyIso f hf
      ((((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex _).obj
        (projectiveResolution N).complex) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat S) _ n).mapIso
      (extendTensorComplexIso f M (projectiveResolution N).complex) ≪≫
    ((flatExtendProjectiveResolution f hf (projectiveResolution N)).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat S)).obj ((ModuleCat.extendScalars f).obj M)) n).symm

end Motivic.TorComparison
