/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.FiniteAffineLocalVanishing
public import Motivic.Cohomology.A1.ZeroDimensionalMoving
public import Motivic.Aglib.AlgebraicGeometry.AffineOpenComplementIdeal
public import Motivic.Topology.JacobsonOpenCover
public import Motivic.AlgebraicGeometry.SmoothSiteAffineCoordinates

/-! # Original integral-affine local zeros over finite fields

Actual scalar presentations are constructed at closed points. Jacobson covering
then gives a genuine original affine neighborhood at every point. Neither this
step nor passage through canonical affine coordinates uses sheaf separatedness.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.AffineTorusPolynomialPresentation

universe u w

namespace Motivic.PresheafWithTransfers

/-- Finite-field local zero from a nonempty affine good open, at every original
point. The zero-dimensional and already-good-point cases bypass presentations. -/
theorem exists_finite_zero_neighborhood_of_nonempty_affine_open
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left] [Nonempty A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (affineSite k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) (x : Spec (.of B)) :
    ∃ (O : (Spec (.of B)).Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) v = 0 := by
  classical
  let J := Scheme.openComplementIdeal B a.left.opensRange
  have hJ : J ≠ ⊥ := Scheme.openComplementIdeal_ne_bot B a.left.opensRange
    (Set.range_nonempty a.left)
  have hr : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      (Set.range a.left)ᶜ := by
    simpa only [Scheme.Hom.coe_opensRange] using
      Scheme.range_openComplementIdeal B a.left.opensRange
  have ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    rw [hr]
    exact disjoint_compl_right
  have hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
    intro y
    rw [hr]
    exact Classical.em _
  by_cases hd : Algebra.trdeg k B = 0
  · have hz := section_zero_of_trdeg_zero k B hd J hJ a hcover P v hv
    refine ⟨⊤, isAffineOpen_top _, trivial, ?_⟩
    dsimp only
    erw [hz, map_zero]
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := B))
  cases n with
  | zero => exact (hd (by simpa using hn)).elim
  | succ d =>
    let Z : (Spec (.of B)).Opens → Prop := fun O => ∃ hO : IsAffineOpen O,
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) v = 0
    have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    have : JacobsonSpace (Spec (.of B)) :=
      LocallyOfFiniteType.jacobsonSpace (Spec.map (CommRingCat.ofHom (algebraMap k B)))
    have htop : (⨆ O : {O : (Spec (.of B)).Opens // Z O}, O.val) = ⊤ := by
      apply TopologicalSpace.Opens.iSup_eq_top_of_closedPoint_neighborhoods
      intro y hy
      by_cases hya : y ∈ Set.range a.left
      · exact ⟨⟨a.left.opensRange, isAffineOpen_opensRange a.left,
          P.zero_on_open_image_general a v hv⟩, hya⟩
      have : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
      obtain ⟨O, hO, hyO, hz⟩ := exists_finite_affine_zero_neighborhood_of_positive_trdeg
        k B y J hJ d hn a ha hcover P hP v hv
      exact ⟨⟨O, hO, hz⟩, hyO⟩
    have hx : x ∈ ⨆ O : {O : (Spec (.of B)).Opens // Z O}, O.val := by
      rw [htop]
      trivial
    obtain ⟨O, hxO⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hO, hz⟩ := O.property
    exact ⟨O.val, hO, hxO, hz⟩

/-- The good open need not be affine: one nonempty affine chart supplies the
actual zero input. This introduces no factorization or presentation family. -/
theorem exists_finite_zero_neighborhood_of_nonempty_open
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    {A : SmoothSite (Spec (.of k))} [Nonempty A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (affineSite k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) (x : Spec (.of B)) :
    ∃ (O : (Spec (.of B)).Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) v = 0 := by
  obtain ⟨y⟩ := ‹Nonempty A.left›
  obtain ⟨i, t, _⟩ := A.left.affineCover.exists_eq y
  let C := SmoothSite.mk (A.left.affineCover.f i ≫ A.hom)
  let c : C ⟶ A := SmoothSite.homMk (A.left.affineCover.f i) rfl
  have : IsAffine C.left := inferInstanceAs (IsAffine (A.left.affineCover.X i))
  have : Nonempty C.left := ⟨t⟩
  have : IsOpenImmersion (c ≫ a).left :=
    inferInstanceAs (IsOpenImmersion (A.left.affineCover.f i ≫ a.left))
  apply exists_finite_zero_neighborhood_of_nonempty_affine_open k B (c ≫ a) P hP v ?_ x
  rw [Functor.map_comp, transfer_comp]
  change P.transfer ((Cor.graphFunctor k).map c)
    (P.transfer ((Cor.graphFunctor k).map a) v) = 0
  rw [hv, map_zero]

/-- Actual finite-field integral-affine local vanishing, with arbitrary coefficient
universe. The returned open and section are on the original smooth-site object. -/
theorem exists_finite_zero_neighborhood_of_integral_affine
    {k : Type u} [Field k] [Finite k]
    {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsIntegral X.left]
    [Nonempty A.left] (a : A ⟶ X) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : X.left) :
    ∃ (O : X.left.Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0 := by
  let : Algebra k Γ(X.left, ⊤) := SmoothSiteAffineCoordinates.sectionsAlgebra X
  let e : affineSite k Γ(X.left, ⊤) ≅ X := SmoothSiteAffineCoordinates.affineIso X
  have : IsOpenImmersion (a ≫ e.inv).left :=
    inferInstanceAs (IsOpenImmersion (a.left ≫ X.left.isoSpec.hom))
  have hv' : P.transfer ((Cor.graphFunctor k).map (a ≫ e.inv))
      (P.transfer ((Cor.graphFunctor k).map e.hom) v) = 0 := by
    have he : (a ≫ e.inv) ≫ e.hom = a := by simp
    have hv' := hv
    rw [← he, Functor.map_comp, transfer_comp] at hv'
    exact hv'
  obtain ⟨O, hO, hx, hz⟩ := exists_finite_zero_neighborhood_of_nonempty_open
    k Γ(X.left, ⊤) (a ≫ e.inv) P hP (P.transfer ((Cor.graphFunctor k).map e.hom) v)
      hv' (e.inv.left x)
  let : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ (affineSite k Γ(X.left, ⊤)).hom)
  let j : S ⟶ affineSite k Γ(X.left, ⊤) := SmoothSite.homMk O.ι rfl
  let f := j ≫ e.hom
  have : IsAffine S.left := hO
  have : IsOpenImmersion f.left :=
    inferInstanceAs (IsOpenImmersion (O.ι ≫ X.left.isoSpec.inv))
  have hf : P.transfer ((Cor.graphFunctor k).map f) v = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hz
  refine ⟨f.left.opensRange, isAffineOpen_opensRange f.left, ?_,
    P.zero_on_open_image_general f v hf⟩
  refine ⟨⟨e.inv.left x, hx⟩, ?_⟩
  exact congrArg (fun f => f.left x) e.inv_hom_id

end Motivic.PresheafWithTransfers
