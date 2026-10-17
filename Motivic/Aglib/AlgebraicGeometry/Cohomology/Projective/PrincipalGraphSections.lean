/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.GraphBoundarySections
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.PrincipalSectionLifting

/-! # Actual graph sections after principal base shrinking

A single original Serre bound supplies sections on every principal inverse-image
open, preserving both boundary equations and the original open graph relation.
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

namespace AlgebraicGeometry.Scheme.Cohomology
/-- Original maps on a principal neighborhood, retaining their section equations. -/
theorem embedded_coherentQuotient_eventually_principal_app_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C : Scheme.{u}} (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    {M N : C.Modules}
    (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (π : M ⟶ N) [Epi π] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ r : R,
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r;
      Function.Surjective
        (((Modules.pushforward k).map
          ((moduleTensorLeftFunctor C ((Modules.pullback k).obj
            (twistingSheaf R ι d))).map π)).app V) := by
  have hM' := FiniteMorphism.affineLocallyFiniteType_pushforward k hM
  have hN' := FiniteMorphism.affineLocallyFiniteType_pushforward k hN
  obtain ⟨B, hB⟩ := projective_coherentQuotient_eventually_principal_app_surjective
    R ι n e hM' hN' ((Modules.pushforward k).map π)
  refine ⟨B, fun d hd r s => ?_⟩
  let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let E := twistingSheaf R ι d
  let eM := closedImmersionProjectionFormulaIso k E M
  let eN := closedImmersionProjectionFormulaIso k E N
  obtain ⟨t, ht⟩ := hB d hd r (eN.inv.app V s)
  refine ⟨eM.hom.app V t, ?_⟩
  have h := closedImmersionProjectionFormulaIso_naturality_right k E π
  have hh := congrArg (fun f => f.app V t) h
  simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hh
  change eN.hom.app V
    (((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map
      ((Modules.pushforward k).map π)).app V t) = _ at hh
  rw [ht] at hh
  have hinv : eN.hom.app V (eN.inv.app V s) = s := by
    simpa only [Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Modules.Hom.id_app, ConcreteCategory.id_apply] using
      congrArg (fun f => f.app V s) eN.inv_hom_id
  exact hh.symm.trans hinv

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.CoherentGraph
/-- Original maps on a principal neighborhood, retaining their section equations. -/
theorem embedded_boundaryRestriction_eventually_principal_app_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (i : Z ⟶ C) [IsClosedImmersion i]
    (G : C.Modules) (hG : affineLocallyFiniteType C G) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d → ∀ r : R,
      let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r;
      Function.Surjective (((Modules.pushforward k).map
        (boundaryRestriction i ((Modules.pullback k).obj
          (ProjectiveSpace.twistingSheaf R ι d)) G)).app V) := by
  let π := (pullbackPushforwardAdjunction i).unit.app G
  let : Epi π := pullbackPushforwardUnit_epi_of_closedImmersion i G
  have hQ := FiniteMorphism.affineLocallyFiniteType_pushforward i
    (affineLocallyFiniteType_pullback i hG)
  obtain ⟨B, hB⟩ := Cohomology.embedded_coherentQuotient_eventually_principal_app_surjective
    R ι n e k hG hQ π
  refine ⟨B, fun d hd r => ?_⟩
  let V := (toSpec R ι) ⁻¹ᵁ PrimeSpectrum.basicOpen r
  have he := ConcreteCategory.bijective_of_isIso
    (((Modules.pushforward k).map
      (closedImmersionProjectionFormulaIso i ((Modules.pullback k).obj
        (ProjectiveSpace.twistingSheaf R ι d)) ((Modules.pullback i).obj G)).hom).app V)
  dsimp only
  intro s
  obtain ⟨t, ht⟩ := he.surjective s
  obtain ⟨t₀, hr⟩ := hB d hd r t
  refine ⟨t₀, ?_⟩
  dsimp only [boundaryRestriction]
  rw [Functor.map_comp, Modules.Hom.comp_app]
  exact (congrArg (fun z => ((Modules.pushforward k).map
    (closedImmersionProjectionFormulaIso i ((Modules.pullback k).obj
      (ProjectiveSpace.twistingSheaf R ι d)) ((Modules.pullback i).obj G)).hom).app V z)
        hr).trans ht


/-- Original maps on a principal neighborhood, retaining their section equations. -/
theorem boundaryRestriction_section_naturality_at {P C Z : Scheme.{u}}
    (k : C ⟶ P) (i : Z ⟶ C) [IsClosedImmersion i] (L : C.Modules)
    {M N : C.Modules} (a : M ⟶ N)
    (V : P.Opens) (t : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj M), V)) :
    ((Modules.pushforward k).map (boundaryRestriction i L N)).app V
      (((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map a)).app V t) =
    (boundaryCoefficient k i L a).app V
      (((Modules.pushforward k).map (boundaryRestriction i L M)).app V t) := by
  have h := congrArg (fun f => ((Modules.pushforward k).map f).app V t)
    (boundaryRestriction_naturality i L a)
  simpa only [Functor.map_comp, Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    boundaryCoefficient] using h


/-- Original maps on a principal neighborhood, retaining their section equations. -/
theorem openSectionRestriction_naturality_at {P C U : Scheme.{u}}
    (k : C ⟶ P) (j : U ⟶ C) [IsOpenImmersion j]
    {M N : C.Modules} (a : M ⟶ N)
    (V : P.Opens) (t : Γ((Modules.pushforward k).obj M, V)) :
    (openSectionRestriction k j N).app V (((Modules.pushforward k).map a).app V t) =
      (((Modules.pushforward k).map ((Modules.pushforward j).map
        ((Modules.restrictFunctor j).map a))).app V
          ((openSectionRestriction k j M).app V t)) := by
  have hn : a ≫ (restrictAdjunction j).unit.app N =
      (restrictAdjunction j).unit.app M ≫
        (Modules.pushforward j).map ((Modules.restrictFunctor j).map a) := by
    simpa only [Functor.id_map, Functor.comp_map] using (restrictAdjunction j).unit.naturality a
  have h := congrArg (fun f => ((Modules.pushforward k).map f).app V t) hn
  simp only [Functor.map_comp, Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  exact h


/-- Original maps on a principal neighborhood, retaining their section equations. -/
theorem graph_section_relation_on_open_at {P C U : Scheme.{u}}
    (k : C ⟶ P) (j : U ⟶ C) [IsOpenImmersion j]
    (L : C.Modules) (h : Γ(U, ⊤)) (g : GraphExtension j h)
    (V : P.Opens)
    (t : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj g.graph.obj), V)) :
    (openSectionRestriction k j
      ((moduleTensorLeftFunctor C L).obj (SheafOfModules.unit C.ringCatSheaf))).app V
        (((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map
          (g.inclusion ≫ biprod.fst))).app V t) =
    (((Modules.pushforward k).map ((Modules.pushforward j).map
      (openTwistScalar j L h))).app V
        ((openSectionRestriction k j
          ((moduleTensorLeftFunctor C L).obj (SheafOfModules.unit C.ringCatSheaf))).app V
            (((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map
              (g.inclusion ≫ biprod.snd))).app V t))) := by
  rw [openSectionRestriction_naturality_at, openSectionRestriction_naturality_at,
    twisted_graph_relation_on_open j L h g, Functor.map_comp, Functor.map_comp,
    Modules.Hom.comp_app]
  rfl


/-- Original maps on a principal neighborhood, retaining their section equations. -/
theorem exists_prescribed_graph_pair_principal
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
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
  obtain ⟨B, hB⟩ := embedded_boundaryRestriction_eventually_principal_app_surjective
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


/-- Original maps on a principal neighborhood, retaining their section equations. -/
theorem exists_prescribed_numerator_denominator_principal
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
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
    exists_prescribed_graph_pair_principal R ι n e k j i h

end AlgebraicGeometry.Scheme.CoherentGraph
