/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.Original.AffineLocalVanishing
public import Motivic.Aglib.Topology.JacobsonOpenCover
/-! # Actual Zariski covering by original-section zero neighborhoods -/
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
local instance : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The genuine affine opens on which the original section is zero. -/
def originalAffineZeroOpen (P : PresheafWithTransfers.{w} k)
    (v : P.sections (Cor.mk (originalAffineObject k B))) (O : (Spec (.of B)).Opens) : Prop :=
  ∃ hO : IsAffineOpen O,
    let : IsAffine O.toScheme := hO
    P.transfer ((Cor.graphFunctor k).map
      (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ (originalAffineObject k B).hom))
        (Y := originalAffineObject k B) O.ι rfl)) v = 0

/-- The constructed neighborhoods cover every original point. The conclusion is
Zariski-local zero for a presheaf, not global zero inferred without separatedness. -/
theorem iSup_original_affine_zero_opens_eq_top
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ originalAffineObject k B) [IsOpenImmersion a.left]
    (ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (originalAffineObject k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    (⨆ O : {O : (Spec (.of B)).Opens // originalAffineZeroOpen k B P v O}, O.val) = ⊤ := by
  have : JacobsonSpace (Spec (.of B)) :=
    LocallyOfFiniteType.jacobsonSpace (Spec.map (CommRingCat.ofHom (algebraMap k B)))
  apply TopologicalSpace.Opens.iSup_eq_top_of_closedPoint_neighborhoods
  intro x hx
  have : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx
  obtain ⟨O, hO, hxO, hz⟩ := exists_original_affine_zero_neighborhood
    k B x J hJ g hg d hd a ha hcover P hP v hv
  exact ⟨⟨O, hO, hz⟩, hxO⟩

end Motivic.PresheafWithTransfers
