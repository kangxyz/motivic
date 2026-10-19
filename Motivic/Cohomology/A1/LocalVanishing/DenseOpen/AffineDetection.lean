/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Original.AffineOpenDetection

/-! # Original dense-open detection on smooth integral affine schemes

A nonempty open is dense in the integral original target. The good open need not
be affine: one actual nonempty affine chart suffices, and is chosen internally.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Motivic
universe u w
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
variable (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.Smooth k B]

/-- Vanishing on the original nonempty open implies Zariski-local vanishing everywhere.
All coordinate, dimension, compactification, boundary and homotopy data are constructed. -/
theorem iSup_zero_opens_of_nonempty_open
    {A : SmoothSite (Spec (.of k))} [Nonempty A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    (⨆ O : {O : (Spec (.of B)).Opens // originalAffineZeroOpen k B P v O}, O.val) = ⊤ := by
  obtain ⟨y⟩ := ‹Nonempty A.left›
  obtain ⟨i, t, _⟩ := A.left.affineCover.exists_eq y
  let C := SmoothSite.mk (A.left.affineCover.f i ≫ A.hom)
  let c : C ⟶ A := SmoothSite.homMk (A.left.affineCover.f i) rfl
  have : IsAffine C.left := inferInstanceAs (IsAffine (A.left.affineCover.X i))
  have : Nonempty C.left := ⟨t⟩
  have : IsOpenImmersion (c ≫ a).left :=
    inferInstanceAs (IsOpenImmersion (A.left.affineCover.f i ≫ a.left))
  apply iSup_zero_opens_of_nonempty_affine_open k B (c ≫ a) P hP v
  rw [Functor.map_comp, transfer_comp]
  change P.transfer ((Cor.graphFunctor k).map c)
    (P.transfer ((Cor.graphFunctor k).map a) v) = 0
  rw [hv, map_zero]

/-- The local-zero neighborhood contains the specified original point, with no
closedness assumption and no supplied presentation or auxiliary ideal. -/
theorem exists_zero_neighborhood_of_nonempty_open
    {A : SmoothSite (Spec (.of k))} [Nonempty A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) (x : Spec (.of B)) :
    ∃ O : (Spec (.of B)).Opens, x ∈ O ∧ originalAffineZeroOpen k B P v O := by
  have he := iSup_zero_opens_of_nonempty_open k B a P hP v hv
  have hx : x ∈ ⨆ O : {O : (Spec (.of B)).Opens // originalAffineZeroOpen k B P v O}, O.val := by
    rw [he]
    trivial
  obtain ⟨O, hxO⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨O.val, hxO, O.property⟩

end Motivic.PresheafWithTransfers
