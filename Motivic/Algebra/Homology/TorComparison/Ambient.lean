/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.AmbientScalar
public import Motivic.Algebra.Homology.TorComparison.ExteriorResolution
public import Motivic.Algebra.Homology.TorComparison.MixedBaseComplex
public import Motivic.Algebra.Homology.TorComparison.Balanced

/-!
# The actual algebraic ambient Tor comparison

Let k be any field and U,V commutative k-algebras. For any map
μ : U tensor_k V → Q whose two induced factor maps U → Q and V → Q
are flat, this file constructs the all-degree ambient Tor comparison.
The left coefficient is the literal exterior tensor module. The result is
an isomorphism of modules over U tensor_k V, with the right side restricted
along μ. In particular, μ itself is not assumed flat.

The proof computes Tor by the actual exterior projective resolution, moves
coefficient tensoring into literal scalar extension and exact restriction,
uses the mixed-base signed total isomorphism, and computes the other Tor
from the two factor-extended projective resolutions. Actual balanced Tor
puts the source arguments in the required order. The modules M,N have no
flatness, projectivity, finiteness, or regularity hypotheses.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

universe u

namespace Motivic.TorComparison

variable {k U V Q : Type u} [Field k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V]

/-- The actual scalar-extended exterior total computes Tor of the two extended
modules, using only flatness of the two induced factor maps. -/
def ambientExtendedExteriorTorIso (μ : U ⊗[k] V →+* Q)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (F : ProjectiveResolution M) (G : ProjectiveResolution N) (n : ℕ) :
    (((ModuleCat.extendScalars μ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (exteriorProjectiveResolution (k := k) F G).complex).homology n ≅
      ((Tor (ModuleCat Q) n).obj
        ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj M)).obj
          ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj N) :=
  (homologyFunctor (ModuleCat Q) (ComplexShape.down ℕ) n).mapIso
      (MixedBase.totalIso k U V Q μ F.complex G.complex) ≪≫
    tensorProjectiveResolutionsTorIso
      (flatExtendProjectiveResolution (MixedBase.leftMap k U V Q μ) hleft F)
      (flatExtendProjectiveResolution (MixedBase.rightMap k U V Q μ) hright G) n

/-- Resolve the exterior module in the actual second Tor argument. No
flatness is required of the ambient map μ. -/
def ambientReverseTorIsoOfResolutions (μ : U ⊗[k] V →+* Q)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (F : ProjectiveResolution M) (G : ProjectiveResolution N) (n : ℕ) :
    ((Tor (ModuleCat (U ⊗[k] V)) n).obj
      ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q))).obj
        (ExteriorModule.obj k U V M N) ≅
      (ModuleCat.restrictScalars μ).obj
        (((Tor (ModuleCat Q) n).obj
          ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj M)).obj
            ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj N)) :=
  (exteriorProjectiveResolution (k := k) F G).isoLeftDerivedObj
      ((tensoringLeft (ModuleCat (U ⊗[k] V))).obj
        ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q))) n ≪≫
    (homologyFunctor (ModuleCat (U ⊗[k] V)) (ComplexShape.down ℕ) n).mapIso
      (ambientTensorRestrictExtendComplexIso μ
        (exteriorProjectiveResolution (k := k) F G).complex) ≪≫
    ambientRestrictHomologyIso μ
      (((ModuleCat.extendScalars μ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (exteriorProjectiveResolution (k := k) F G).complex) n ≪≫
    (ModuleCat.restrictScalars μ).mapIso (ambientExtendedExteriorTorIso μ hleft hright F G n)

/-- The required ambient comparison, with source arguments in the original
one-sided Tor order and its precise ambient-ring action. -/
def ambientTorIsoOfResolutions (μ : U ⊗[k] V →+* Q)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (F : ProjectiveResolution M) (G : ProjectiveResolution N) (n : ℕ) :
    ((Tor (ModuleCat (U ⊗[k] V)) n).obj (ExteriorModule.obj k U V M N)).obj
      ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q)) ≅
      (ModuleCat.restrictScalars μ).obj
        (((Tor (ModuleCat Q) n).obj
          ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj M)).obj
            ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj N)) :=
  torBalanceIso (ExteriorModule.obj k U V M N)
      ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q)) n ≪≫
    ambientReverseTorIsoOfResolutions μ hleft hright F G n

/-- All-degree ambient Tor comparison for arbitrary modules over the two
factors. Only the two factor maps are assumed flat; the ambient map can be
a nonflat quotient. Both sides are actual modules over the full ambient ring. -/
def ambientTorIso (μ : U ⊗[k] V →+* Q)
    (hleft : (MixedBase.leftMap k U V Q μ).Flat)
    (hright : (MixedBase.rightMap k U V Q μ).Flat)
    (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :
    ((Tor (ModuleCat (U ⊗[k] V)) n).obj (ExteriorModule.obj k U V M N)).obj
      ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q)) ≅
      (ModuleCat.restrictScalars μ).obj
        (((Tor (ModuleCat Q) n).obj
          ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj M)).obj
            ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj N)) :=
  ambientTorIsoOfResolutions μ hleft hright
    (projectiveResolution M) (projectiveResolution N) n

end Motivic.TorComparison
