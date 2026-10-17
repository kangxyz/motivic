/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.GenericDetection
/-! Direct original-section detection with no presentation, ideal,
coordinates or dimension input. -/
set_option linter.hashCommand false
public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Motivic
universe u w
namespace Motivic.PresheafWithTransfers
variable (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.Smooth k B]

example {A : SmoothSite (Spec (.of k))} [Nonempty A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) (x : Spec (.of B)) :
    ∃ O : (Spec (.of B)).Opens, x ∈ O ∧ originalAffineZeroOpen k B P v O := by
  exact exists_zero_neighborhood_of_nonempty_open k B a P hP v hv x

example {A : SmoothSite (Spec (.of k))} [Nonempty A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    (⨆ O : {O : (Spec (.of B)).Opens // originalAffineZeroOpen k B P v O}, O.val) = ⊤ := by
  exact iSup_zero_opens_of_nonempty_open k B a P hP v hv

#print axioms exists_zero_neighborhood_of_nonempty_open
#print axioms iSup_zero_opens_of_nonempty_open
#print axioms section_zero_of_trdeg_zero
end Motivic.PresheafWithTransfers
