/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.OneSidedRelativeMoving
public import Motivic.Cohomology.A1.OneSidedMovingAction
/-! Original HI PST section-zero consumer of the actual relative one-sided pencil. -/
set_option linter.hashCommand false
public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Moving Scheme.RelativeCurvePencil
universe u w
namespace Motivic.OneSidedMovingEndpoints
example
    {k : Type u} [Field k] (R : Type u) [CommRing R]
    (ι : Type u) (n : ℕ) (eι : ι ≃ Fin (n + 1)) [Finite ι]
    {S X V : SmoothSite (Spec (.of k))}
    [IsAffine S.left] [IsAffine X.left] [IsAffine V.left]
    [IsNoetherianRing Γ(S.left, ⊤)] {C Z D : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
    (j : S.left ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ (f ≫ toSpec R ι))]
    [IsLocallyNoetherian (pullback (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι))]
    (x : X.left ⟶ C) [IsOpenImmersion x]
    [SmoothOfRelativeDimension 1 (x ≫ (f ≫ toSpec R ι))]
    (v : V ⟶ X) [IsOpenImmersion v.left]
    (φ : S ⟶ X) (hφ : φ.left ≫ x = j)
    (t : Spec (.of R) ⟶ Spec (.of k))
    (hS : (j ≫ (f ≫ toSpec R ι)) ≫ t = S.hom)
    (hXbase : (x ≫ (f ≫ toSpec R ι)) ≫ t = X.hom)
    (s : Z ⟶ S.left) [IsClosedImmersion (s ≫ j)]
    (d : D ⟶ C) [IsClosedImmersion d]
    (hd : Disjoint (Set.range j) (Set.range d))
    (hX : ∀ c : C, c ∈ Set.range x ∨ c ∈ Set.range d)
    (hV : ∀ c : C, c ∈ Set.range (v.left ≫ x) ∨
      c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (e : SheafOfModules.unit
      (pullback (j ≫ (f ≫ toSpec R ι)) (s ≫ (j ≫ (f ≫ toSpec R ι)))).ringCatSheaf ≅
        Scheme.Hom.idealModule
          (Scheme.Hom.boundaryGraphTarget (j ≫ (f ≫ toSpec R ι)) s))
    (eFull : ∀ m : ℕ, (Scheme.Modules.pullback (fullTargetBoundaryMap j s d ≫ f)).obj
      (twistingSheaf R ι (m : ℤ)) ≅ SheafOfModules.unit (D ⨿ Z).ringCatSheaf)
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (a : P.sections (Cor.mk X))
    (ha : P.transfer ((Cor.graphFunctor k).map v) a = 0) :
    P.transfer ((Cor.graphFunctor k).map φ) a = 0 := by
  obtain ⟨β, α, h0, h1⟩ := exists_moving_endpoints_of_relative_frames
    R ι n eι f j x v φ hφ t hS hXbase s d hd hX hV e eFull
  exact P.section_zero_of_moving_endpoints hP φ v β α h0 h1 a ha

#print axioms exists_moving_endpoints_of_relative_frames
#print axioms PresheafWithTransfers.section_zero_of_moving_endpoints
end Motivic.OneSidedMovingEndpoints
