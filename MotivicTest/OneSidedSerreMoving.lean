/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.Moving.OneSided.SerreMoving
public import Motivic.Cohomology.A1.Moving.OneSided
/-! Direct arbitrary HI PST consumer of the constructed one-sided Serre homotopy. -/
set_option linter.hashCommand false
public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open ProjectiveSpace Scheme.Modules Scheme.Modules.Invertible Scheme.Moving
universe u v
namespace Motivic.OneSidedMovingEndpoints
open _root_.AlgebraicGeometry.Scheme
example
    (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
    (bS : Spec (.of R) ⟶ Spec (.of k)) [Smooth bS]
    (ι : Type u) (n : ℕ) (eι : ι ≃ Fin (n + 1))
    {X V : SmoothSite (Spec (.of k))} {C D G B W : Scheme.{u}}
    [IsLocallyNoetherian C] [IsAffine D] [IsAffine G]
    (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
    (z : B ⟶ C) [IsClosedImmersion z] (i : W ⟶ B)
    (j : D ⟶ C) [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ f ≫ toSpec R ι)]
    (w : G ⟶ D) [IsOpenImmersion w]
    [SmoothOfRelativeDimension 1 ((w ≫ j) ≫ f ≫ toSpec R ι)]
    (hX : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range (i ≫ z))
    (hV : ∀ x : C, x ∈ Set.range (w ≫ j) ∨ x ∈ Set.range z)
    (δ : Spec (.of R) ⟶ C) [IsClosedImmersion δ]
    (γ : Spec (.of R) ⟶ D) (hγ : γ ≫ j = δ)
    (hγq : γ ≫ (j ≫ f ≫ toSpec R ι) = 𝟙 _)
    (hI : IsLocallyRankOne C (Scheme.Hom.idealModule δ))
    (E : (Scheme.Modules.pullback z).obj
      (dualLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩).val ≅
        SheafOfModules.unit B.ringCatSheaf)
    (hδ : pullbackSectionMap (i ≫ z)
      (canonicalDualHom C (Scheme.Hom.idealModule δ) (Scheme.Hom.idealInclusion δ)) ≫
      (compositeBoundaryFrame i z
        (dualLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩).val E).hom = 𝟙 _)
    (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor B
      ((Scheme.Modules.pullback z).obj
        ((Scheme.Modules.pullback f).obj (twistingSheaf R ι (d : ℤ))))).obj
        ((Scheme.Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
          SheafOfModules.unit B.ringCatSheaf)
    (g : D ⟶ X.left) (gV : G ⟶ V.left) (v : V ⟶ X) [IsOpenImmersion v.left]
    (hv : w ≫ g = gV ≫ v.left)
    (φ : SmoothSite.mk bS ⟶ X) (hγg : γ ≫ g = φ.left)
    (hbase : (j ≫ f ≫ toSpec R ι) ≫ bS = g ≫ X.hom)
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (s : P.sections (Cor.mk X))
    (hs : P.transfer ((Cor.graphFunctor k).map v) s = 0) :
    P.transfer ((Cor.graphFunctor k).map φ) s = 0 := by
  obtain ⟨β, α, h0, h1⟩ := exists_moving_endpoints_of_boundary_frames k R bS ι n eι
    f z i j w hX hV δ γ hγ hγq hI E hδ eQ g gV v hv φ hγg hbase
  exact P.section_zero_of_moving_endpoints hP φ v β α h0 h1 s hs

#print axioms exists_moving_endpoints_of_boundary_frames
#print axioms PresheafWithTransfers.section_zero_of_moving_endpoints
end Motivic.OneSidedMovingEndpoints
