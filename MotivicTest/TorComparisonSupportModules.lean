/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.SupportModulesMiddle

/-! # Consumers of literal support-coordinate module actions and their ambient Tor -/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Motivic.MiddleDiagonal

universe u

namespace Motivic.MotivicTest.TorComparisonSupportModules

open Motivic.TorComparison.SupportModules

section General

variable (k U V : Type u) [CommRing k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V] (I : Ideal U) (J : Ideal V)

/-- The actual exterior quotient module is linear over both ambient factors. -/
def actualExteriorModule :
    Motivic.TorComparison.ExteriorModule.obj k U V
      (ModuleCat.of U (U ⧸ I)) (ModuleCat.of V (V ⧸ J)) ≅
      Motivic.Intersection.specCoordinateModule
        (R := U ⊗[k] V) (A := (U ⧸ I) ⊗[k] (V ⧸ J))
        (quotientTensorMap k U V I J).toRingHom :=
  exteriorQuotientIso k U V I J

/-- The coordinate map is exactly the tensor of the two quotient ring maps. -/
theorem quotient_coordinates (a : U) (b : V) :
    quotientTensorMap k U V I J (a ⊗ₜ[k] b) =
      Ideal.Quotient.mk I a ⊗ₜ[k] Ideal.Quotient.mk J b :=
  quotientTensorMap_tmul k U V I J a b

/-- Every ambient scalar acts via the specified tensor quotient map. -/
theorem ambient_scalar (p : U ⊗[k] V)
    (x : Motivic.TorComparison.ExteriorModule.obj k U V
      (ModuleCat.of U (U ⧸ I)) (ModuleCat.of V (V ⧸ J))) :
    (actualExteriorModule k U V I J).hom (p • x) =
      quotientTensorMap k U V I J p *
        (show (U ⧸ I) ⊗[k] (V ⧸ J) from (actualExteriorModule k U V I J).hom x) :=
  (actualExteriorModule k U V I J).hom.hom.map_smul p x

end General

section Extension

variable {R S : Type u} [CommRing R] [CommRing S]

/-- An arbitrary ring map gives the actual quotient-pullback coordinate module. -/
def arbitraryExtension (f : R →+* S) (I : Ideal R) :
    letI : Algebra R S := f.toAlgebra
    (ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ I)) ≅
      Motivic.Intersection.specCoordinateModule (R := S) (A := S ⊗[R] (R ⧸ I))
        Algebra.TensorProduct.includeLeftRingHom :=
  extendQuotientIso f I

/-- An existing algebra structure is preserved by the quotient-pullback comparison. -/
def prescribedExtension [Algebra R S] (I : Ideal R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (R ⧸ I)) ≅
      Motivic.Intersection.specCoordinateModule (R := S) (A := S ⊗[R] (R ⧸ I))
        Algebra.TensorProduct.includeLeftRingHom :=
  extendQuotientAlgebraIso R S I

end Extension

section ActualMiddle

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))

/-- The complete support-coordinate comparison uses the actual ambient quotient
and arbitrary support ideals, with no flatness hypotheses on either support. -/
def actualMiddleSupportTor (n : ℕ) :
    ((Tor (ModuleCat (Motivic.MiddleDiagonal.ambientRing k A B C)) n).obj
      (Motivic.Intersection.specCoordinateModule
        (R := Motivic.MiddleDiagonal.ambientRing k A B C)
        (A := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
        (Motivic.AffineMiddle.supportRingMap k A B C I J).toRingHom)).obj
      (Motivic.Intersection.specCoordinateModule
        (R := Motivic.MiddleDiagonal.ambientRing k A B C)
        (A := Motivic.MiddleDiagonal.tripleRing k A B C)
        (Motivic.MiddleDiagonal.quotientMap k A B C).toRingHom) ≅
      (ModuleCat.restrictScalars (Motivic.MiddleDiagonal.quotientMap k A B C).toRingHom).obj
        (((Tor (ModuleCat (Motivic.MiddleDiagonal.tripleRing k A B C)) n).obj
          (leftPulledModule k A B C I)).obj (rightPulledModule k A B C J)) :=
  middleSupportTorIso k A B C I J n

end ActualMiddle

end Motivic.MotivicTest.TorComparisonSupportModules
