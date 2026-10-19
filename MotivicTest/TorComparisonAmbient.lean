/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientMiddle

/-! # Consumers of the actual algebraic ambient and middle-diagonal Tor comparisons -/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open HomologicalComplex
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison
open scoped TensorProduct ChangeOfRings Algebra.TensorProduct.MiddleDiagonal

universe u

namespace MotivicTest.TorComparisonAmbient

/-- The scalar adapter has the literal pure-tensor formula for every ring map. -/
theorem scalarPureTensor {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R)
    (s : (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) (m : M) :
    (ambientTensorRestrictExtendIso f).hom.app M (s ⊗ₜ[R] m) = s ⊗ₜ[R,f] m := rfl

/-- The actual coefficient-tensor differential is transported without map-flatness. -/
def arbitraryScalarComplex {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K ≅
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
  ambientTensorRestrictExtendComplexIso f K

variable {k U V Q : Type u} [Field k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V]

/-- Arbitrary quotient supports require no regularity or flatness of their own. -/
def arbitraryQuotients (μ : U ⊗[k] V →+* Q)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat) (I : Ideal U) (J : Ideal V) (n : ℕ) :
    ((Tor (ModuleCat (U ⊗[k] V)) n).obj
      (ExteriorModule.obj k U V (ModuleCat.of U (U ⧸ I)) (ModuleCat.of V (V ⧸ J)))).obj
        ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q)) ≅
      (ModuleCat.restrictScalars μ).obj
        (((Tor (ModuleCat Q) n).obj
          ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj
            (ModuleCat.of U (U ⧸ I)))).obj
          ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj
            (ModuleCat.of V (V ⧸ J)))) :=
  ambientTorIso μ hleft hright _ _ n

/-- The reverse-order source really resolves the exterior module. -/
def reverseOrder (μ : U ⊗[k] V →+* Q)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :
    ((Tor (ModuleCat (U ⊗[k] V)) n).obj
      ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q))).obj
        (ExteriorModule.obj k U V M N) ≅
      (ModuleCat.restrictScalars μ).obj
        (((Tor (ModuleCat Q) n).obj
          ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj M)).obj
            ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj N)) :=
  ambientReverseTorIsoOfResolutions μ hleft hright
    (projectiveResolution M) (projectiveResolution N) n

/-- Every degree, including degree zero, has a genuine ambient-linear inverse. -/
theorem actualInverse (μ : U ⊗[k] V →+* Q)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :
    (ambientTorIso μ hleft hright M N n).hom ≫
      (ambientTorIso μ hleft hright M N n).inv = 𝟙 _ :=
  (ambientTorIso μ hleft hright M N n).hom_inv_id

/-- The isomorphism really preserves the full ambient-ring scalar action. -/
theorem ambientLinear (μ : U ⊗[k] V →+* Q)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) (p : U ⊗[k] V)
    (x : ((Tor (ModuleCat (U ⊗[k] V)) n).obj (ExteriorModule.obj k U V M N)).obj
      ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q))) :
    (ambientTorIso μ hleft hright M N n).hom (p • x) =
      p • (ambientTorIso μ hleft hright M N n).hom x :=
  (ambientTorIso μ hleft hright M N n).hom.hom.map_smul p x

/-- Arbitrary quotient supports in adjacent affine coordinates satisfy the
comparison with all factor-flatness hypotheses discharged over every field. -/
def middleQuotientSupports (k A B C : Type u) [Field k]
    [CommRing A] [CommRing B] [CommRing C] [Algebra k A] [Algebra k B] [Algebra k C]
    (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    ((Tor (ModuleCat (_root_.Algebra.TensorProduct.MiddleDiagonal.ambientRing k A B C)) n).obj
      (ExteriorModule.obj k (A ⊗[k] B) (B ⊗[k] C)
        (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))
        (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)))).obj
      ((ModuleCat.restrictScalars (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom).obj
        (ModuleCat.of (_root_.Algebra.TensorProduct.MiddleDiagonal.tripleRing k A B C)
          (_root_.Algebra.TensorProduct.MiddleDiagonal.tripleRing k A B C))) ≅
      (ModuleCat.restrictScalars (_root_.Algebra.TensorProduct.MiddleDiagonal.quotientMap k A B
          C).toRingHom).obj
        (((Tor (ModuleCat (_root_.Algebra.TensorProduct.MiddleDiagonal.tripleRing k A B C)) n).obj
          ((ModuleCat.extendScalars (_root_.Algebra.TensorProduct.MiddleDiagonal.leftMap k A B
              C).toRingHom).obj
            (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I)))).obj
          ((ModuleCat.extendScalars (_root_.Algebra.TensorProduct.MiddleDiagonal.rightMap k A B
              C).toRingHom).obj
            (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)))) :=
  ambientMiddleTorIso k A B C _ _ n

end MotivicTest.TorComparisonAmbient
