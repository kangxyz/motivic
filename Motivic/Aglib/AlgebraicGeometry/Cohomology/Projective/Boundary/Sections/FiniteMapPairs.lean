/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.PrescribedLineBundlePair
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.SectionLifting.FiniteMap

/-! # Actual sections representing a prescribed boundary-trivialized line bundle

The boundary is the entire original closed scheme. Its generating positive-twist
section is constructed on one principal base neighborhood. The two lifts use the
maximum of two original Serre bounds. No graph or denominator ideal is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Actual prescribed sections along a finite map to projective space,
without assuming a closed projective embedding. -/
theorem finiteMap_exists_prescribed_graph_pair_principal
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsFinite k]
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)]
    (h : Γ(U, ⊤)) :
    let g := extendGraph j h
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ r : R,
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r;
      let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι d)
      ∀ σ : Γ((Modules.pushforward k).obj ((Modules.pushforward (i ≫ j)).obj
          ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).obj
            ((Modules.pullback (i ≫ j)).obj O))), V),
      ∃ s₀ s₁ : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), V),
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app V s₀ = σ ∧
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app V s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward (i ≫ j)).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).map
              (boundaryGraphRatio j i h g)))).app V σ) ∧
        (openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app V s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward j).map
            (openTwistScalar j L h))).app V
              ((openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app V s₀)) := by
  dsimp only
  let g := extendGraph j h
  let O := SheafOfModules.unit C.ringCatSheaf
  obtain ⟨B, hB⟩ := finite_boundaryRestriction_eventually_principal_app_surjective
    R ι n e k (i ≫ j) g.graph.obj g.graph.property
  refine ⟨B, fun d hd r σ => ?_⟩
  let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι d)
  let T := moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)
  let F := Modules.pushforward (i ≫ j) ⋙ Modules.pushforward k
  let q := boundaryDenominatorIso j i h g
  let eq := F.mapIso (T.mapIso q)
  obtain ⟨t, ht⟩ := hB d hd r (eq.inv.app V σ)
  let a := g.inclusion ≫ biprod.fst
  let b := g.inclusion ≫ biprod.snd
  refine ⟨((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map b)).app V t,
    ((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map a)).app V t, ?_, ?_, ?_⟩
  · rw [boundaryRestriction_section_naturality_at, ht]
    change eq.hom.app V (eq.inv.app V σ) = σ
    simpa only [Modules.Hom.comp_app, ConcreteCategory.comp_apply, Modules.Hom.id_app,
      ConcreteCategory.id_apply] using congrArg (fun f => f.app V σ) eq.inv_hom_id
  · rw [boundaryRestriction_section_naturality_at, ht]
    change (F.map (T.map ((Modules.pullback (i ≫ j)).map a))).app V
      ((F.map (T.map q.inv)).app V σ) =
        (F.map (T.map (q.inv ≫ (Modules.pullback (i ≫ j)).map a))).app V σ
    rw [T.map_comp, F.map_comp, Modules.Hom.comp_app]
    rfl
  · exact graph_section_relation_on_open_at k j L h g V t



/-- Actual prescribed sections along a finite map to projective space,
without assuming a closed projective embedding. -/
theorem finiteMap_exists_prescribed_numerator_denominator_principal
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsFinite k]
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)]
    (h : Γ(U, ⊤)) :
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ r : R,
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r;
      let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι d)
      ∀ σ : Γ((Modules.pushforward k).obj ((Modules.pushforward (i ≫ j)).obj
          ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).obj
            ((Modules.pullback (i ≫ j)).obj O))), V),
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
  simpa only [boundaryGraphRatio_eq_boundaryScalar] using
    finiteMap_exists_prescribed_graph_pair_principal R ι n e k j i h


/-- Actual prescribed sections along a finite map to projective space,
without assuming a closed projective embedding. -/
theorem finiteMap_exists_finiteBoundary_numerator_denominator
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsFinite k]
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
  obtain ⟨B, hB⟩ := finiteMap_exists_prescribed_numerator_denominator_principal R ι n e k j i h
  refine ⟨r, hr, B, fun d hd => ?_⟩
  refine ⟨eQ d, ?_⟩
  exact hB (d : ℤ) (Int.ofNat_le.mpr hd) r
    ((openUnitSectionsIso _ _ (eQ d)).inv
      (1 : Γ(((((i ≫ j) ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme, ⊤)))


/-- Actual prescribed sections along a finite map to projective space,
without assuming a closed projective embedding. -/
theorem finiteMap_exists_prescribed_boundary_section_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (k : C ⟶ ProjectiveSpace R ι) [IsFinite k]
    (z : Z ⟶ C) [IsClosedImmersion z]
    [IsFinite ((z ≫ k) ≫ toSpec R ι)]
    (M : C.Modules) (hM : affineLocallyFiniteType C M)
    (eB : (Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (s : Spec (CommRingCat.of R)) :
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ r : R, s ∈ PrimeSpectrum.basicOpen r ∧
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
      let L := (Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))
      let Q := (moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).obj
        ((Modules.pullback z).obj O)
      let W := ((z ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
      ∃ eQ : Q.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf,
      let σ := (openUnitSectionsIso W Q eQ).inv (1 : Γ(W.toScheme, ⊤))
      ∃ a : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj M), V),
      ∃ b : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), V),
        ((Modules.pushforward k).map (boundaryRestriction z L M)).app V a =
          ((Modules.pushforward k).map ((Modules.pushforward z).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).map
              ((pullbackUnitIso z).hom ≫ eB.inv)))).app V σ ∧
        ((Modules.pushforward k).map (boundaryRestriction z L O)).app V b = σ := by
  let O := SheafOfModules.unit C.ringCatSheaf
  have hO : affineLocallyFiniteType C O := by
    let eO : SheafOfModules.free (R := C.ringCatSheaf) PUnit ≅ O := coproductUniqueIso _
    let := finiteLocallyFree_of_iso eO
    exact coherent_of_finiteLocallyFree _
  obtain ⟨r, hr, ⟨eQ⟩⟩ := exists_principal_boundaryCoefficient_unitIso R ι k z s
  obtain ⟨BM, hBM⟩ := finite_boundaryRestriction_eventually_principal_app_surjective
    R ι n e k z M hM
  obtain ⟨BO, hBO⟩ := finite_boundaryRestriction_eventually_principal_app_surjective
    R ι n e k z O hO
  refine ⟨r, hr, max BM BO, fun d hd => ?_⟩
  refine ⟨eQ d, ?_⟩
  let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let L := (Modules.pullback k).obj (twistingSheaf R ι (d : ℤ))
  let W := ((z ≫ k) ≫ toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let σ := (openUnitSectionsIso W _ (eQ d)).inv (1 : Γ(W.toScheme, ⊤))
  let τ := ((Modules.pushforward k).map ((Modules.pushforward z).map
    ((moduleTensorLeftFunctor Z ((Modules.pullback z).obj L)).map
      ((pullbackUnitIso z).hom ≫ eB.inv)))).app V σ
  obtain ⟨a, ha⟩ := hBM (d : ℤ) (Int.ofNat_le.mpr ((le_max_left BM BO).trans hd)) r τ
  obtain ⟨b, hb⟩ := hBO (d : ℤ) (Int.ofNat_le.mpr ((le_max_right BM BO).trans hd)) r σ
  exact ⟨a, b, ha, hb⟩

end AlgebraicGeometry.Scheme.CoherentGraph
