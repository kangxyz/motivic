/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.OneSidedSectionProducer
/-! # One given split curve presentation produces actual dense-open moving

This is the one-sided MVW 11.9 construction. The original finite presentation,
full boundary, and its prescribed frames are explicit geometric inputs. Serre
sections, finite-flat zeros, beta, and the affine-line homotopy are all produced.
Local existence of these geometric frames is a separate step, not claimed here.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open ProjectiveSpace Scheme.Modules Scheme.Modules.Invertible Scheme.Moving
universe u
namespace Motivic.OneSidedMovingEndpoints

/-- No sections, correspondence maps, zero-flatness, or endpoint equations occur
among the inputs of the given-presentation moving producer. -/
theorem exists_moving_endpoints_of_boundary_frames
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
    (hbase : (j ≫ f ≫ toSpec R ι) ≫ bS = g ≫ X.hom) :
    HasMovingEndpoints φ v := by
  have : IsAffine (SmoothSite.mk bS).left := inferInstanceAs (IsAffine (Spec (.of R)))
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) eι.symm
  have : IsProper (f ≫ toSpec R ι) := inferInstance
  have : Smooth (j ≫ f ≫ toSpec R ι) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth ((j ≫ f ≫ toSpec R ι) ≫ bS) := inferInstance
  obtain ⟨N, hN⟩ := exists_oneSidedSerreSections R k bS ι n eι f z i eQ j (w ≫ j)
    hX hV ⟨Scheme.Hom.idealModule δ, hI⟩ (Scheme.Hom.idealInclusion δ) E hδ
  obtain ⟨s⟩ := hN N le_rfl
  have hc : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range z := by
    intro x
    rcases hX x with hx | ⟨t, rfl⟩
    · exact Or.inl hx
    · exact Or.inr ⟨i t, rfl⟩
  exact exists_moving_endpoints_of_sections (S := SmoothSite.mk bS) (X := X) (V := V)
    (f ≫ toSpec R ι) z i j w hc δ γ hγ hγq hI
    (pullbackLineBundle f (twistingLineBundle R ι (N : ℤ))) E s g gV v hv φ hγg hbase

end Motivic.OneSidedMovingEndpoints
