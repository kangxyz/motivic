/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.Moving.OneSided.LocalMoving
public import Motivic.Cohomology.A1.Moving.OneSided
/-! # One given good curve presentation kills an original section locally

This applies to arbitrary homotopy-invariant presheaves with transfers. No sheaf,
sheafification, cohomology acyclicity or already constructed homotopy is assumed.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Hom Scheme.Moving Motivic.OneSidedMovingEndpoints
universe u w
namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) (n : ℕ) (eι : ι ≃ Fin (n + 1)) [Finite ι]
  {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine A.left]
  {C Z D : Scheme.{u}} (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  (x : X.left ⟶ C) [IsOpenImmersion x]
  [SmoothOfRelativeDimension 1 (x ≫ (f ≫ toSpec R ι))]
  (a : A ⟶ X) [IsOpenImmersion a.left]
  (t : Spec (.of R) ⟶ Spec (.of k))
  (hbase : (x ≫ (f ≫ toSpec R ι)) ≫ t = X.hom)
  (z : Z ⟶ X.left) [IsClosedImmersion (z ≫ x)]
  (d : D ⟶ C) [IsClosedImmersion d]
  (hd : Disjoint (Set.range x) (Set.range d))
  (hX : ∀ c : C, c ∈ Set.range x ∨ c ∈ Set.range d)
  (hA : ∀ c : C, c ∈ Set.range (a.left ≫ x) ∨
    c ∈ Set.range d ∨ c ∈ Set.range (z ≫ x))

include eι hbase hd hX hA in
/-- Given a genuine target curve presentation, vanishing on the original good open
implies vanishing on a Zariski neighborhood of the specified original point.
All frames, moving correspondences and finite-flat homotopies are constructed. -/
theorem exists_zero_neighborhood_of_curve_presentation
    [IsFinite (z ≫ (x ≫ f ≫ toSpec R ι))]
    [IsFinite ((coprod.desc d (z ≫ x) ≫ f) ≫ toSpec R ι)]
    (p : X.left) (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (s : P.sections (Cor.mk X)) (hs : P.transfer ((Cor.graphFunctor k).map a) s = 0) :
    ∃ (O : X.left.Opens) (hO : IsAffineOpen O), p ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) s = 0 := by
  obtain ⟨U, hU, hpU, W, hW, hpW, hO, hm⟩ :=
    exists_local_moving_of_curve_presentation R ι n eι f x a t hbase z d hd hX hA p
  let : IsAffine W.toScheme := hW
  let : IsAffine (boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W).toScheme := hO
  refine ⟨boundaryBaseSourceOpen (x ≫ f ≫ toSpec R ι) U W, hO, ⟨hpU, hpW⟩, ?_⟩
  obtain ⟨β, α, h0, h1⟩ := hm
  exact P.section_zero_of_moving_endpoints hP
    (refinedSourceToOriginal X (x ≫ f ≫ toSpec R ι) U W) a β α h0 h1 s hs

end Motivic.PresheafWithTransfers
