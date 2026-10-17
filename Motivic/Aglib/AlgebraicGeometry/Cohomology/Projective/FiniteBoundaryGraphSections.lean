/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.PrincipalGraphSections
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.PrincipalBoundaryTwists
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit

/-! # Graph sections with a generating full finite-boundary denominator -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The actual boundary coefficient tensor is the composite pulled-back twist. -/
def boundaryTwistCoefficientIso {P C Z : Scheme.{u}}
    (k : C ⟶ P) (z : Z ⟶ C) (E : P.Modules) :
    (moduleTensorLeftFunctor Z ((Modules.pullback z).obj ((Modules.pullback k).obj E))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
      (Modules.pullback (z ≫ k)).obj E :=
  (moduleTensorLeftFunctor Z _).mapIso (pullbackUnitIso z) ≪≫
    (SheafOfModulesOfCommRing.tensorRightUnitIso Z.sheaf).app _ ≪≫ (Modules.pullbackComp z k).app E

/-- Original open sections in a specified actual unit trivialization. -/
def openUnitSectionsIso {Z : Scheme.{u}} (W : Z.Opens) (M : Z.Modules)
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    Γ(M, W) ≅ AddCommGrpCat.of Γ(W.toScheme, ⊤) :=
  M.presheaf.mapIso (eqToIso (Scheme.Opens.opensRange_ι W)).op ≪≫
    trivializedOpenSectionsIso W.ι M e

/-- A finite full boundary has one principal base neighborhood on which the
actual coefficient sheaf of every positive twist has a unit trivialization. -/
theorem exists_principal_boundaryCoefficient_unitIso
    (R : Type u) [CommRing R] (ι : Type u)
    {C Z : Scheme.{u}} (k : C ⟶ ProjectiveSpace R ι) (z : Z ⟶ C)
    [IsFinite ((z ≫ k) ≫ toSpec R ι)] (s : Spec (CommRingCat.of R)) :
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
      Nonempty ((n : ℕ) →
        let L := (Modules.pullback k).obj (twistingSheaf R ι (n : ℤ))
        let Q := (moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
          ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf))
        let W := ((z ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
        Q.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  obtain ⟨r, hr, ⟨en⟩⟩ := exists_principal_positiveTwist_unitIso R ι (z ≫ k) s
  refine ⟨r, hr, ⟨fun n => ?_⟩⟩
  let W := ((z ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let E := twistingSheaf R ι (n : ℤ)
  exact (Modules.restrictFunctor W.ι).mapIso (boundaryTwistCoefficientIso k z E) ≪≫
    (restrictFunctorIsoPullback W.ι).app ((Modules.pullback (z ≫ k)).obj E) ≪≫
      (Modules.pullbackComp W.ι (z ≫ k)).app E ≪≫ en n

/-- After one principal base shrink, the graph produces actual numerator and
denominator sections with a generating full-boundary denominator. The three
equations are the original boundary and open section maps. -/
theorem exists_finiteBoundary_numerator_denominator
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)]
    [IsFinite (((i ≫ j) ≫ k) ≫ toSpec R ι)]
    (h : Γ(U, ⊤)) (s : Spec (CommRingCat.of R)) :
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r;
      let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι (d : ℤ))
      let Q := (moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).obj
        ((Modules.pullback (i ≫ j)).obj O)
      let W := (((i ≫ j) ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
      ∃ eQ : Q.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf,
      let σ := (openUnitSectionsIso W Q eQ).inv (1 : Γ(W.toScheme, ⊤))
      ∃ s₀ s₁ : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), V),
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app V s₀ = σ ∧
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app V s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward (i ≫ j)).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).map
              (boundaryScalar j i h)))).app V σ) ∧
        (openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app V s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward j).map
            (openTwistScalar j L h))).app V
              ((openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app V s₀)) := by
  obtain ⟨r, hr, ⟨eQ⟩⟩ := exists_principal_boundaryCoefficient_unitIso R ι k (i ≫ j) s
  obtain ⟨B, hB⟩ := exists_prescribed_numerator_denominator_principal R ι n e k j i h
  refine ⟨r, hr, B, fun d hd => ?_⟩
  refine ⟨eQ d, ?_⟩
  exact hB (d : ℤ) (Int.ofNat_le.mpr hd) r
    ((openUnitSectionsIso _ _ (eQ d)).inv
      (1 : Γ(((((i ≫ j) ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme, ⊤)))

end AlgebraicGeometry.Scheme.CoherentGraph
