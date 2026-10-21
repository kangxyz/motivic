/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.A1.LocalVanishing.FixedTarget.NormalizedLifting
/-! Actual one-target consumer: no source compactification, frame, pencil or section premise. -/
set_option linter.hashCommand false
public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Hom Scheme.EtaleCompactification
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
/-- The smoothness instance used in this module. -/
local instance fixedTargetNormalizedLiftingSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) [Finite ι] (X C : Scheme.{u})
  [IsAffine X] [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsIntegral C] [IsLocallyNoetherian C]
  [∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)]
  {Y A Z D : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ X) [IsOpenImmersion a]
  (j : X ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  (hq : j ≫ (f ≫ toSpec R ι) = q)


example (m : ℕ) (eι : ι ≃ Fin (m + 1))
    (z : Z ⟶ X) [IsFinite (z ≫ q)] (s : Z ⟶ Y) [IsClosedImmersion s]
    (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
    (ha : Disjoint (Set.range a) (Set.range z))
    (hcover : ∀ x : X, x ∈ Set.range a ∨ x ∈ Set.range z)
    (d : D ⟶ C) [IsFinite (d ≫ (f ≫ toSpec R ι))]
    (hbad : (j ''ᵁ finiteLocusOpen X p : Set C)ᶜ ⊆ Set.range d)
    (x : X) (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      q x ∈ V ∧ (∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U) ∧
      ∃ hW : IsAffineOpen (boundaryBaseSourceOpen q U V),
        let : IsAffine (boundaryBaseSourceOpen q U V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (fixedTargetPencilGraph k R ι X C t q p a j f hq U V)
          (fixedTargetPencilBeta k R ι X C t q p a j f hq U V)
          (fixedTargetPencilAlpha k R ι X C t q p a j f hq U V) :=
  exists_fixedTarget_normalized_lifting k R ι X C t q p a j f hq m eι
    z s hs H ha hcover d hbad x P hP
#print axioms exists_fixedTarget_normalized_lifting
#print axioms fixedTarget_retained_cover
#print axioms fixedTargetSourceProjectiveMap_inclusion
end AlgebraicGeometry.Scheme.RelativeCurvePencil
