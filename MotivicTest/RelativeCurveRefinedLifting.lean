/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.RelativeCurveRefinedLifting
/-! Direct original-presheaf consumer: the retained target is not the smaller parameter open. -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) (m : ℕ) (eι : ι ≃ Fin (m + 1)) [Finite ι]
  {X Y A Z C D T : Scheme.{u}}
  [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine T]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] (a : A ⟶ X) [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f] (j : Y ⟶ C) [IsOpenImmersion j]
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (v : T ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
  (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)

include hs H ha hd hc m eι in
example
    [IsFinite (z ≫ q)]
    [IsFinite ((coprod.desc d (s ≫ j) ≫ f) ≫ toSpec R ι)]
    (x : X) (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      q x ∈ V ∧
      (∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U) ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen q U V),
        let : IsAffine (boundaryBaseSourceOpen q U V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (boundaryBasePencilGraph k R ι t q p a f j hj U V v φ hφ)
          (boundaryBasePencilBeta k R ι t q p a f j hj U V)
          (boundaryBasePencilAlpha k R ι t q p a f j hj U V) :=
  exists_refined_relativeCurve_lifting k R ι m eι t q p a f j hj z s hs H ha d hd
    v hc φ hφ x P hP
#print axioms exists_refined_relativeCurve_lifting
end AlgebraicGeometry.Scheme.RelativeCurvePencil
