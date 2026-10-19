/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientMiddle
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.SupportModulesAlgebra
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.AffineMiddleSupports
public import Motivic.Aglib.AlgebraicGeometry.Intersection.ClosedSpecTor

/-!
# Middle-diagonal Tor for the actual support coordinate modules

The generic ambient comparison is here applied to the actual coordinate ring
of the product of two arbitrary quotient supports. Its target uses the literal
coordinate rings of the two supports pulled back to the triple product. Each
module structure is restriction along the same coordinate map used by the
geometric support inclusions. No support flatness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.MiddleDiagonal

universe u

namespace ModuleCat.TorComparison.SupportModules
open _root_.Algebra.TensorProduct
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Products

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
  (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))

/-- The actual module of the left support pulled back to the triple product. -/
abbrev leftPulledModule : ModuleCat (MiddleDiagonal.tripleRing k A B C) :=
  Intersection.specCoordinateModule
    (R := MiddleDiagonal.tripleRing k A B C)
    (A := (MiddleDiagonal.tripleRing k A B C) ⊗[A ⊗[k] B] ((A ⊗[k] B) ⧸ I))
    Algebra.TensorProduct.includeLeftRingHom

/-- The actual module of the right pulled-back support uses the specified
right adjacent coordinate map, exactly as its affine pullback coordinate ring. -/
abbrev rightPulledModule : ModuleCat (MiddleDiagonal.tripleRing k A B C) :=
  letI : Algebra (B ⊗[k] C) (MiddleDiagonal.tripleRing k A B C) :=
    (MiddleDiagonal.rightMap k A B C).toRingHom.toAlgebra
  Intersection.specCoordinateModule
    (R := MiddleDiagonal.tripleRing k A B C)
    (A := (MiddleDiagonal.tripleRing k A B C) ⊗[B ⊗[k] C] ((B ⊗[k] C) ⧸ J))
    Algebra.TensorProduct.includeLeftRingHom

/-- The exterior module equals the actual ambient-coordinate module of the
literal product of the two quotient supports. -/
def middleExteriorQuotientIso :
    ExteriorModule.obj k (A ⊗[k] B) (B ⊗[k] C)
      (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))
      (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)) ≅
      Intersection.specCoordinateModule
        (R := MiddleDiagonal.ambientRing k A B C)
        (A := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
        (MiddleDiagonal.supportRingMap k A B C I J).toRingHom :=
  exteriorQuotientIso k (A ⊗[k] B) (B ⊗[k] C) I J

/-- Left extension of the quotient module has the actual pulled-support ring action. -/
def leftPulledModuleIso :
    (ModuleCat.extendScalars (MiddleDiagonal.leftMap k A B C).toRingHom).obj
      (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I)) ≅ leftPulledModule k A B C I :=
  extendQuotientAlgebraIso (A ⊗[k] B) (MiddleDiagonal.tripleRing k A B C) I

/-- Right extension has the literal action of the corresponding support inclusion. -/
def rightPulledModuleIso :
    (ModuleCat.extendScalars (MiddleDiagonal.rightMap k A B C).toRingHom).obj
      (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)) ≅ rightPulledModule k A B C J :=
  extendQuotientIso (MiddleDiagonal.rightMap k A B C).toRingHom J

/-- All-degree comparison for actual affine support-coordinate modules. The
source is Tor over the full ambient coordinate ring, and the target uses both
actual pulled-support coordinate rings with their literal triple-ring actions. -/
def middleSupportTorIso (n : ℕ) :
    ((Tor (ModuleCat (MiddleDiagonal.ambientRing k A B C)) n).obj
      (Intersection.specCoordinateModule
        (R := MiddleDiagonal.ambientRing k A B C)
        (A := ((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
        (MiddleDiagonal.supportRingMap k A B C I J).toRingHom)).obj
        (Intersection.specCoordinateModule
          (R := MiddleDiagonal.ambientRing k A B C) (A := MiddleDiagonal.tripleRing k A B C)
          (MiddleDiagonal.quotientMap k A B C).toRingHom) ≅
      (ModuleCat.restrictScalars (MiddleDiagonal.quotientMap k A B C).toRingHom).obj
        (((Tor (ModuleCat (MiddleDiagonal.tripleRing k A B C)) n).obj
          (leftPulledModule k A B C I)).obj (rightPulledModule k A B C J)) :=
  ((Tor (ModuleCat (MiddleDiagonal.ambientRing k A B C)) n).mapIso
      (middleExteriorQuotientIso k A B C I J).symm).app
        (Intersection.specCoordinateModule
          (R := MiddleDiagonal.ambientRing k A B C) (A := MiddleDiagonal.tripleRing k A B C)
          (MiddleDiagonal.quotientMap k A B C).toRingHom) ≪≫
    ambientMiddleTorIso k A B C
      (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))
      (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)) n ≪≫
    (ModuleCat.restrictScalars (MiddleDiagonal.quotientMap k A B C).toRingHom).mapIso
      (((Tor (ModuleCat (MiddleDiagonal.tripleRing k A B C)) n).mapIso
        (leftPulledModuleIso k A B C I)).app
          ((ModuleCat.extendScalars (MiddleDiagonal.rightMap k A B C).toRingHom).obj
            (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J))) ≪≫
        ((Tor (ModuleCat (MiddleDiagonal.tripleRing k A B C)) n).obj
          (leftPulledModule k A B C I)).mapIso (rightPulledModuleIso k A B C J))

end ModuleCat.TorComparison.SupportModules
