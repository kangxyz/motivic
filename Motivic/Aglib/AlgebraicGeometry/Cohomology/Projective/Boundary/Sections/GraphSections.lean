/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Sections.SectionLifting
public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.Noetherian
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction

/-!
# Coherent extensions of actual function graphs

The graph of `(h,1)` extends inside the rank-two structure sheaf. Its second
projection need not be an invertible ideal away from the prescribed open.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts

universe u
namespace AlgebraicGeometry.Scheme.CoherentGraph

variable {U C : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]

/-- The literal graph inclusion after the original unit restriction comparison. -/
def graphInclusion (h : Γ(U, ⊤)) :
    SheafOfModules.unit U.ringCatSheaf ⟶
      (Modules.restrictFunctor j).obj
        ((SheafOfModules.unit C.ringCatSheaf) ⊞ (SheafOfModules.unit C.ringCatSheaf)) :=
  unitMul U h ≫ (restrictUnitIso j).inv ≫ (Modules.restrictFunctor j).map biprod.inl +
    (restrictUnitIso j).inv ≫ (Modules.restrictFunctor j).map biprod.inr

@[reassoc (attr := simp)]
theorem graphInclusion_fst (h : Γ(U, ⊤)) :
    graphInclusion j h ≫ (Modules.restrictFunctor j).map biprod.fst =
      unitMul U h ≫ (restrictUnitIso j).inv := by
  have hz : (Modules.restrictFunctor j).map
      (0 : SheafOfModules.unit C.ringCatSheaf ⟶ SheafOfModules.unit C.ringCatSheaf) = 0 := by
    ext V x
    rfl
  simp [graphInclusion, Preadditive.add_comp, Category.assoc, ← Functor.map_comp, hz]

@[reassoc (attr := simp)]
theorem graphInclusion_snd (h : Γ(U, ⊤)) :
    graphInclusion j h ≫ (Modules.restrictFunctor j).map biprod.snd =
      (restrictUnitIso j).inv := by
  have hz : (Modules.restrictFunctor j).map
      (0 : SheafOfModules.unit C.ringCatSheaf ⟶ SheafOfModules.unit C.ringCatSheaf) = 0 := by
    ext V x
    rfl
  simp [graphInclusion, Preadditive.add_comp, Category.assoc, ← Functor.map_comp, hz]

instance graphInclusion_mono (h : Γ(U, ⊤)) : Mono (graphInclusion j h) := by
  have : Mono (graphInclusion j h ≫ (Modules.restrictFunctor j).map biprod.snd) := by
    rw [graphInclusion_snd]
    infer_instance
  exact mono_of_mono (graphInclusion j h) ((Modules.restrictFunctor j).map biprod.snd)

/-- An actual coherent graph extension, retaining the exact numerator and
 denominator on the whole specified open. No invertibility claim is made
 about the global denominator's image. -/
theorem exists_coherent_graph_extension [IsNoetherian C] [IsLocallyNoetherian U]
    (h : Γ(U, ⊤)) :
    ∃ (G : FiniteTypeSheaves C)
      (b : G.obj ⟶ ((SheafOfModules.unit C.ringCatSheaf) ⊞
        (SheafOfModules.unit C.ringCatSheaf))), Mono b ∧
      ∃ e : G.obj.restrict j ≅ SheafOfModules.unit U.ringCatSheaf,
        (Modules.restrictFunctor j).map (b ≫ biprod.fst) =
          e.hom ≫ unitMul U h ≫ (restrictUnitIso j).inv ∧
        (Modules.restrictFunctor j).map (b ≫ biprod.snd) =
          e.hom ≫ (restrictUnitIso j).inv := by
  have hunit (X : Scheme.{u}) : affineLocallyFiniteType X
      (SheafOfModules.unit X.ringCatSheaf) := by
    let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅
        SheafOfModules.unit X.ringCatSheaf := coproductUniqueIso _
    let := finiteLocallyFree_of_iso e
    exact coherent_of_finiteLocallyFree _
  let O := SheafOfModules.unit C.ringCatSheaf
  have hOO : affineLocallyFiniteType C (O ⊞ O) :=
    (affineLocallyFiniteType C).prop_of_iso (biprod.isoCoprod O O).symm
      ((affineLocallyFiniteType C).prop_coprod O O (hunit C) (hunit C))
  let : (O ⊞ O).IsQuasicoherent :=
    quasicoherent_of_affineCharts _ (fun A a _ => (hOO A a).1)
  let A : FiniteTypeSheaves U :=
    ⟨SheafOfModules.unit U.ringCatSheaf, hunit U⟩
  let := graphInclusion_mono j h
  obtain ⟨G, b, hb, e, he⟩ :=
    Modules.Coherent.affineLocallyFiniteType_subobject_extension_noetherian j
      (O ⊞ O) A (graphInclusion j h)
  refine ⟨G, b, hb, e, ?_, ?_⟩
  · rw [Functor.map_comp, he, Category.assoc, graphInclusion_fst]
  · rw [Functor.map_comp, he, Category.assoc, graphInclusion_snd]

end AlgebraicGeometry.Scheme.CoherentGraph

namespace AlgebraicGeometry.Scheme.Cohomology

open ProjectiveSpace

/-- The needed embedded-scheme form of Serre lifting, on the original
coefficient map rather than an unidentified isomorphic quotient. -/
theorem embedded_coherentQuotient_eventually_sections_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C : Scheme.{u}} (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    {M N : C.Modules}
    (hM : affineLocallyFiniteType C M) (hN : affineLocallyFiniteType C N)
    (π : M ⟶ N) [Epi π] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      Function.Surjective
        (((Modules.pushforward k).map
          ((moduleTensorLeftFunctor C ((Modules.pullback k).obj
            (twistingSheaf R ι d))).map π)).app ⊤) := by
  have hM' := FiniteMorphism.affineLocallyFiniteType_pushforward k hM
  have hN' := FiniteMorphism.affineLocallyFiniteType_pushforward k hN
  obtain ⟨B, hB⟩ := projective_coherentQuotient_eventually_sections_surjective
    R ι n e hM' hN' ((Modules.pushforward k).map π)
  refine ⟨B, fun d hd s => ?_⟩
  let E := twistingSheaf R ι d
  let eM := closedImmersionProjectionFormulaIso k E M
  let eN := closedImmersionProjectionFormulaIso k E N
  obtain ⟨t, ht⟩ := hB d hd (eN.inv.app ⊤ s)
  refine ⟨eM.hom.app ⊤ t, ?_⟩
  have h := closedImmersionProjectionFormulaIso_naturality_right k E π
  have hh := congrArg (fun f => f.app ⊤ t) h
  simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hh
  change eN.hom.app ⊤
    (((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).map
      ((Modules.pushforward k).map π)).app ⊤ t) = _ at hh
  rw [ht] at hh
  have hinv : eN.hom.app ⊤ (eN.inv.app ⊤ s) = s := by
    simpa only [Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      Modules.Hom.id_app, ConcreteCategory.id_apply] using
      congrArg (fun f => f.app ⊤ s) eN.inv_hom_id
  exact hh.symm.trans hinv

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The graph's original trivialization on a boundary lying in its open.
This is constructed from the open restriction isomorphism, not assumed. -/
def boundaryGraphIso {U C Z : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    (i : Z ⟶ U) (G : C.Modules)
    (e : G.restrict j ≅ SheafOfModules.unit U.ringCatSheaf) :
    (Modules.pullback (i ≫ j)).obj G ≅ SheafOfModules.unit Z.ringCatSheaf :=
  (Modules.pullbackComp i j).symm.app G ≪≫
    (Modules.pullback i).mapIso ((restrictFunctorIsoPullback j).symm.app G ≪≫ e) ≪≫
    pullbackUnitIso i

/-- The genuine whole closed-boundary restriction for an arbitrary twist. -/
def boundaryRestriction {Z C : Scheme.{u}} (i : Z ⟶ C) [IsClosedImmersion i]
    (L M : C.Modules) :
    (moduleTensorLeftFunctor C L).obj M ⟶
      (Modules.pushforward i).obj
        ((moduleTensorLeftFunctor Z ((Modules.pullback i).obj L)).obj
          ((Modules.pullback i).obj M)) :=
  (moduleTensorLeftFunctor C L).map ((pullbackPushforwardAdjunction i).unit.app M) ≫
    (closedImmersionProjectionFormulaIso i L ((Modules.pullback i).obj M)).hom

/-- Coefficient maps commute with the actual whole-boundary restriction. -/
@[reassoc]
theorem boundaryRestriction_naturality {Z C : Scheme.{u}}
    (i : Z ⟶ C) [IsClosedImmersion i] (L : C.Modules)
    {M N : C.Modules} (a : M ⟶ N) :
    (moduleTensorLeftFunctor C L).map a ≫ boundaryRestriction i L N =
      boundaryRestriction i L M ≫ (Modules.pushforward i).map
        ((moduleTensorLeftFunctor Z ((Modules.pullback i).obj L)).map
          ((Modules.pullback i).map a)) := by
  have hn : a ≫ (pullbackPushforwardAdjunction i).unit.app N =
      (pullbackPushforwardAdjunction i).unit.app M ≫
        (Modules.pushforward i).map ((Modules.pullback i).map a) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (pullbackPushforwardAdjunction i).unit.naturality a
  dsimp only [boundaryRestriction]
  rw [← Category.assoc, ← Functor.map_comp, hn, Functor.map_comp,
    Category.assoc, closedImmersionProjectionFormulaIso_naturality_right]
  rfl

/-- The embedded full-boundary lifting needed by the graph construction. -/
theorem embedded_boundaryRestriction_eventually_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C Z : Scheme.{u}} [IsLocallyNoetherian C]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (i : Z ⟶ C) [IsClosedImmersion i]
    (G : C.Modules) (hG : affineLocallyFiniteType C G) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      Function.Surjective (((Modules.pushforward k).map
        (boundaryRestriction i ((Modules.pullback k).obj
          (ProjectiveSpace.twistingSheaf R ι d)) G)).app ⊤) := by
  let π := (pullbackPushforwardAdjunction i).unit.app G
  let : Epi π := pullbackPushforwardUnit_epi_of_closedImmersion i G
  have hQ := FiniteMorphism.affineLocallyFiniteType_pushforward i
    (affineLocallyFiniteType_pullback i hG)
  obtain ⟨B, hB⟩ := Cohomology.embedded_coherentQuotient_eventually_sections_surjective
    R ι n e k hG hQ π
  refine ⟨B, fun d hd => ?_⟩
  have he := ConcreteCategory.bijective_of_isIso
    (((Modules.pushforward k).map
      (closedImmersionProjectionFormulaIso i ((Modules.pullback k).obj
        (ProjectiveSpace.twistingSheaf R ι d)) ((Modules.pullback i).obj G)).hom).app ⊤)
  intro s
  obtain ⟨t, ht⟩ := he.surjective s
  obtain ⟨r, hr⟩ := hB d hd t
  refine ⟨r, ?_⟩
  dsimp only [boundaryRestriction]
  rw [Functor.map_comp, Modules.Hom.comp_app]
  exact (congrArg (fun z => ((Modules.pushforward k).map
    (closedImmersionProjectionFormulaIso i ((Modules.pullback k).obj
      (ProjectiveSpace.twistingSheaf R ι d)) ((Modules.pullback i).obj G)).hom).app ⊤ z)
        hr).trans ht

end AlgebraicGeometry.Scheme.CoherentGraph

namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- Concrete coherent graph extension with its original two coordinate maps. -/
structure GraphExtension {U C : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    (h : Γ(U, ⊤)) where
  /-- The chosen finite type sheaf on `C`. -/
  graph : FiniteTypeSheaves C
  /-- Inclusion into the two coordinate copies of the unit sheaf. -/
  inclusion : graph.obj ⟶
    ((SheafOfModules.unit C.ringCatSheaf) ⊞ (SheafOfModules.unit C.ringCatSheaf))
  mono_inclusion : Mono inclusion
  /-- Identification of the restriction to `U` with its unit sheaf. -/
  trivialization : graph.obj.restrict j ≅ SheafOfModules.unit U.ringCatSheaf
  numerator_eq : (Modules.restrictFunctor j).map (inclusion ≫ biprod.fst) =
    trivialization.hom ≫ unitMul U h ≫ (restrictUnitIso j).inv
  denominator_eq : (Modules.restrictFunctor j).map (inclusion ≫ biprod.snd) =
    trivialization.hom ≫ (restrictUnitIso j).inv

/-- The coherent extension exists by actual subobject extension, without
assuming any global numerator or denominator in advance. -/
def extendGraph {U C : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (j : U ⟶ C) [IsOpenImmersion j] (h : Γ(U, ⊤)) : GraphExtension j h := by
  have hex : Nonempty (GraphExtension j h) := by
    obtain ⟨G, b, hb, e, ha, hc⟩ := exists_coherent_graph_extension j h
    exact ⟨⟨G, b, hb, e, ha, hc⟩⟩
  exact Classical.choice hex

/-- A morphism invertible on the specified open is invertible after
pullback to any scheme mapping into that open. -/
theorem pullback_isIso_of_restrict_isIso {U C Z : Scheme.{u}}
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U)
    {M N : C.Modules} (a : M ⟶ N)
    [IsIso ((Modules.restrictFunctor j).map a)] :
    IsIso ((Modules.pullback (i ≫ j)).map a) := by
  have : IsIso ((Modules.pullback j).map a) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback j) a).mp inferInstance
  apply (NatIso.isIso_map_iff (Modules.pullbackComp i j) a).mp
  change IsIso ((Modules.pullback i).map ((Modules.pullback j).map a))
  infer_instance

/-- The denominator is canonically invertible on every boundary contained
in the prescribed open, even when its image on C is not an invertible ideal. -/
def boundaryDenominatorIso {U C Z : Scheme.{u}}
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) (h : Γ(U, ⊤))
    (g : GraphExtension j h) :
    (Modules.pullback (i ≫ j)).obj g.graph.obj ≅
      (Modules.pullback (i ≫ j)).obj (SheafOfModules.unit C.ringCatSheaf) := by
  let a := g.inclusion ≫ biprod.snd
  have : IsIso ((Modules.restrictFunctor j).map a) := by
    change IsIso ((Modules.restrictFunctor j).map (g.inclusion ≫ biprod.snd))
    rw [g.denominator_eq]
    infer_instance
  let := pullback_isIso_of_restrict_isIso j i a
  exact asIso ((Modules.pullback (i ≫ j)).map a)

end AlgebraicGeometry.Scheme.CoherentGraph

namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The coefficient map on the entire closed boundary, including its
original projective direct image. -/
def boundaryCoefficient {P C Z : Scheme.{u}} (k : C ⟶ P) (i : Z ⟶ C)
    (L : C.Modules) {M N : C.Modules} (a : M ⟶ N) :=
  (Modules.pushforward k).map ((Modules.pushforward i).map
    ((moduleTensorLeftFunctor Z ((Modules.pullback i).obj L)).map
      ((Modules.pullback i).map a)))

/-- Restricting an actual twisted coefficient section commutes with taking
its numerator or denominator. -/
theorem boundaryRestriction_section_naturality {P C Z : Scheme.{u}}
    (k : C ⟶ P) (i : Z ⟶ C) [IsClosedImmersion i] (L : C.Modules)
    {M N : C.Modules} (a : M ⟶ N)
    (t : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj M), ⊤)) :
    ((Modules.pushforward k).map (boundaryRestriction i L N)).app ⊤
      (((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map a)).app ⊤ t) =
    (boundaryCoefficient k i L a).app ⊤
      (((Modules.pushforward k).map (boundaryRestriction i L M)).app ⊤ t) := by
  have h := congrArg (fun f => ((Modules.pushforward k).map f).app ⊤ t)
    (boundaryRestriction_naturality i L a)
  simpa only [Functor.map_comp, Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    boundaryCoefficient] using h

/-- Boundary multiplication by h, represented intrinsically using the
constructed graph. The denominator is inverted only on the prescribed
boundary, where its invertibility was proved from `(h,1)`. -/
def boundaryGraphRatio {U C Z : Scheme.{u}}
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) (h : Γ(U, ⊤))
    (g : GraphExtension j h) :
    (Modules.pullback (i ≫ j)).obj (SheafOfModules.unit C.ringCatSheaf) ⟶
      (Modules.pullback (i ≫ j)).obj (SheafOfModules.unit C.ringCatSheaf) :=
  (boundaryDenominatorIso j i h g).inv ≫
    (Modules.pullback (i ≫ j)).map (g.inclusion ≫ biprod.fst)

/-- Multiplication by h on the actual open restriction of a twisted unit
module, transported through the original tensor comparison. -/
def openTwistScalar {U C : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    (L : C.Modules) (h : Γ(U, ⊤)) :=
  (tensorRestrictionIso j L (SheafOfModules.unit C.ringCatSheaf)).inv ≫
    (moduleTensorLeftFunctor U (L.restrict j)).map
      ((restrictUnitIso j).hom ≫ unitMul U h ≫ (restrictUnitIso j).inv) ≫
    (tensorRestrictionIso j L (SheafOfModules.unit C.ringCatSheaf)).hom

/-- Exact numerator = h times denominator on the whole open, before
choosing any section. This is the pole-clearing relation retained by G. -/
theorem twisted_graph_relation_on_open {U C : Scheme.{u}}
    (j : U ⟶ C) [IsOpenImmersion j] (L : C.Modules) (h : Γ(U, ⊤))
    (g : GraphExtension j h) :
    (Modules.restrictFunctor j).map
        ((moduleTensorLeftFunctor C L).map (g.inclusion ≫ biprod.fst)) =
      (Modules.restrictFunctor j).map
        ((moduleTensorLeftFunctor C L).map (g.inclusion ≫ biprod.snd)) ≫
          openTwistScalar j L h := by
  let a := g.inclusion ≫ biprod.fst
  let b := g.inclusion ≫ biprod.snd
  let H := (restrictUnitIso j).hom ≫ unitMul U h ≫ (restrictUnitIso j).inv
  let T := moduleTensorLeftFunctor U (L.restrict j)
  let E := tensorRestrictionNatIso j L
  have hab : (Modules.restrictFunctor j).map a =
      (Modules.restrictFunctor j).map b ≫ H := by
    change (Modules.restrictFunctor j).map (g.inclusion ≫ biprod.fst) =
      (Modules.restrictFunctor j).map (g.inclusion ≫ biprod.snd) ≫ H
    rw [g.numerator_eq, g.denominator_eq]
    simp [H, Category.assoc]
  change (moduleTensorLeftFunctor C L ⋙ Modules.restrictFunctor j).map a =
    (moduleTensorLeftFunctor C L ⋙ Modules.restrictFunctor j).map b ≫ openTwistScalar j L h
  apply (cancel_epi (E.hom.app g.graph.obj)).mp
  rw [← E.hom.naturality a]
  change T.map ((Modules.restrictFunctor j).map a) ≫ E.hom.app _ = _
  rw [hab, T.map_comp]
  dsimp only [openTwistScalar]
  rw [← Category.assoc, ← Category.assoc, ← E.hom.naturality b]
  simp [E, T, H, tensorRestrictionNatIso, Functor.map_comp, Category.assoc]

/-- Restriction of a section to the original open, through the native
open-restriction adjunction and projective direct image. -/
def openSectionRestriction {P C U : Scheme.{u}} (k : C ⟶ P)
    (j : U ⟶ C) [IsOpenImmersion j] (M : C.Modules) :=
  (Modules.pushforward k).map ((restrictAdjunction j).unit.app M)

/-- Sectionwise naturality of actual open restriction. -/
theorem openSectionRestriction_naturality {P C U : Scheme.{u}}
    (k : C ⟶ P) (j : U ⟶ C) [IsOpenImmersion j]
    {M N : C.Modules} (a : M ⟶ N)
    (t : Γ((Modules.pushforward k).obj M, ⊤)) :
    (openSectionRestriction k j N).app ⊤ (((Modules.pushforward k).map a).app ⊤ t) =
      (((Modules.pushforward k).map ((Modules.pushforward j).map
        ((Modules.restrictFunctor j).map a))).app ⊤
          ((openSectionRestriction k j M).app ⊤ t)) := by
  have hn : a ≫ (restrictAdjunction j).unit.app N =
      (restrictAdjunction j).unit.app M ≫
        (Modules.pushforward j).map ((Modules.restrictFunctor j).map a) := by
    simpa only [Functor.id_map, Functor.comp_map] using (restrictAdjunction j).unit.naturality a
  have h := congrArg (fun f => ((Modules.pushforward k).map f).app ⊤ t) hn
  simp only [Functor.map_comp, Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  exact h

/-- Every actual section of the constructed twisted graph gives a pair
satisfying the original h-relation on U, not merely matching boundary data. -/
theorem graph_section_relation_on_open {P C U : Scheme.{u}}
    (k : C ⟶ P) (j : U ⟶ C) [IsOpenImmersion j]
    (L : C.Modules) (h : Γ(U, ⊤)) (g : GraphExtension j h)
    (t : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj g.graph.obj), ⊤)) :
    (openSectionRestriction k j
      ((moduleTensorLeftFunctor C L).obj (SheafOfModules.unit C.ringCatSheaf))).app ⊤
        (((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map
          (g.inclusion ≫ biprod.fst))).app ⊤ t) =
    (((Modules.pushforward k).map ((Modules.pushforward j).map
      (openTwistScalar j L h))).app ⊤
        ((openSectionRestriction k j
          ((moduleTensorLeftFunctor C L).obj (SheafOfModules.unit C.ringCatSheaf))).app ⊤
            (((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map
              (g.inclusion ≫ biprod.snd))).app ⊤ t))) := by
  rw [openSectionRestriction_naturality, openSectionRestriction_naturality,
    twisted_graph_relation_on_open j L h g, Functor.map_comp, Functor.map_comp,
    Modules.Hom.comp_app]
  rfl

/-- Actual numerator and denominator sections with prescribed whole-boundary
values. The graph is constructed, the global pair is produced by Serre
lifting, and the only supplied section is the desired boundary denominator.
A nowhere-zero boundary denominator can be supplied when the geometric
construction has trivialized the restricted positive twist. -/
theorem exists_prescribed_graph_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)]
    (h : Γ(U, ⊤)) :
    let g := extendGraph j h
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι d)
      ∀ σ : Γ((Modules.pushforward k).obj ((Modules.pushforward (i ≫ j)).obj
          ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).obj
            ((Modules.pullback (i ≫ j)).obj O))), ⊤),
      ∃ s₀ s₁ : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), ⊤),
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app ⊤ s₀ = σ ∧
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app ⊤ s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward (i ≫ j)).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).map
              (boundaryGraphRatio j i h g)))).app ⊤ σ) ∧
        (openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app ⊤ s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward j).map
            (openTwistScalar j L h))).app ⊤
              ((openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app ⊤ s₀)) := by
  dsimp only
  let g := extendGraph j h
  let O := SheafOfModules.unit C.ringCatSheaf
  obtain ⟨B, hB⟩ := embedded_boundaryRestriction_eventually_surjective
    R ι n e k (i ≫ j) g.graph.obj g.graph.property
  refine ⟨B, fun d hd σ => ?_⟩
  let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι d)
  let T := moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)
  let F := Modules.pushforward (i ≫ j) ⋙ Modules.pushforward k
  let q := boundaryDenominatorIso j i h g
  let eq := F.mapIso (T.mapIso q)
  obtain ⟨t, ht⟩ := hB d hd (eq.inv.app ⊤ σ)
  let a := g.inclusion ≫ biprod.fst
  let b := g.inclusion ≫ biprod.snd
  refine ⟨((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map b)).app ⊤ t,
    ((Modules.pushforward k).map ((moduleTensorLeftFunctor C L).map a)).app ⊤ t, ?_, ?_, ?_⟩
  · rw [boundaryRestriction_section_naturality, ht]
    change eq.hom.app ⊤ (eq.inv.app ⊤ σ) = σ
    simpa only [Modules.Hom.comp_app, ConcreteCategory.comp_apply, Modules.Hom.id_app,
      ConcreteCategory.id_apply] using congrArg (fun f => f.app ⊤ σ) eq.inv_hom_id
  · rw [boundaryRestriction_section_naturality, ht]
    change (F.map (T.map ((Modules.pullback (i ≫ j)).map a))).app ⊤
      ((F.map (T.map q.inv)).app ⊤ σ) =
        (F.map (T.map (q.inv ≫ (Modules.pullback (i ≫ j)).map a))).app ⊤ σ
    rw [T.map_comp, F.map_comp, Modules.Hom.comp_app]
    rfl
  · exact graph_section_relation_on_open k j L h g t

end AlgebraicGeometry.Scheme.CoherentGraph

namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The original open restriction/pullback comparison followed by pullback
composition. This retains the coefficient maps, not just the objects. -/
def boundaryOpenComparison {U C Z : Scheme.{u}}
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) :
    Modules.restrictFunctor j ⋙ Modules.pullback i ≅ Modules.pullback (i ≫ j) :=
  Functor.isoWhiskerRight (restrictFunctorIsoPullback j) (Modules.pullback i) ≪≫
    Modules.pullbackComp i j

/-- Actual multiplication by h pulled from the open to the boundary.
This formula is independent of any choice of coherent graph extension. -/
def boundaryScalar {U C Z : Scheme.{u}}
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) (h : Γ(U, ⊤)) :=
  (boundaryOpenComparison j i).inv.app (SheafOfModules.unit C.ringCatSheaf) ≫
    (Modules.pullback i).map
      ((restrictUnitIso j).hom ≫ unitMul U h ≫ (restrictUnitIso j).inv) ≫
    (boundaryOpenComparison j i).hom.app (SheafOfModules.unit C.ringCatSheaf)

/-- The boundary ratio of the constructed graph is exactly multiplication
by the specified function h, independently of the coherent extension. -/
theorem boundaryGraphRatio_eq_boundaryScalar {U C Z : Scheme.{u}}
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) (h : Γ(U, ⊤))
    (g : GraphExtension j h) :
    boundaryGraphRatio j i h g = boundaryScalar j i h := by
  let a := g.inclusion ≫ biprod.fst
  let b := g.inclusion ≫ biprod.snd
  let H := (restrictUnitIso j).hom ≫ unitMul U h ≫ (restrictUnitIso j).inv
  let K := Modules.restrictFunctor j ⋙ Modules.pullback i
  let P := Modules.pullback (i ≫ j)
  let E := boundaryOpenComparison j i
  have hab : (Modules.restrictFunctor j).map a =
      (Modules.restrictFunctor j).map b ≫ H := by
    change (Modules.restrictFunctor j).map (g.inclusion ≫ biprod.fst) =
      (Modules.restrictFunctor j).map (g.inclusion ≫ biprod.snd) ≫ H
    rw [g.numerator_eq, g.denominator_eq]
    simp [H, Category.assoc]
  have hK : K.map a = K.map b ≫ (Modules.pullback i).map H := by
    change (Modules.pullback i).map ((Modules.restrictFunctor j).map a) = _
    rw [hab, Functor.map_comp]
    rfl
  have hP : P.map a = P.map b ≫ boundaryScalar j i h := by
    apply (cancel_epi (E.hom.app g.graph.obj)).mp
    rw [← E.hom.naturality a, hK]
    dsimp only [boundaryScalar]
    rw [← Category.assoc, ← Category.assoc, ← E.hom.naturality b]
    simp [E, K, H, Functor.map_comp, Category.assoc]
  change (boundaryDenominatorIso j i h g).inv ≫ P.map a = _
  rw [hP]
  change (boundaryDenominatorIso j i h g).inv ≫
    (boundaryDenominatorIso j i h g).hom ≫ _ = _
  simp

end AlgebraicGeometry.Scheme.CoherentGraph

namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The final pair has full-boundary values σ and hσ, with h represented
by the original restriction/pullback coefficient comparisons. No graph
sheaf, global section, or invertible denominator ideal is an input. -/
theorem exists_prescribed_numerator_denominator
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C U Z : Scheme.{u}} [IsNoetherian C] [IsLocallyNoetherian U]
    (k : C ⟶ ProjectiveSpace R ι) [IsClosedImmersion k]
    (j : U ⟶ C) [IsOpenImmersion j] (i : Z ⟶ U) [IsClosedImmersion (i ≫ j)]
    (h : Γ(U, ⊤)) :
    let O := SheafOfModules.unit C.ringCatSheaf
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      let L := (Modules.pullback k).obj (ProjectiveSpace.twistingSheaf R ι d)
      ∀ σ : Γ((Modules.pushforward k).obj ((Modules.pushforward (i ≫ j)).obj
          ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).obj
            ((Modules.pullback (i ≫ j)).obj O))), ⊤),
      ∃ s₀ s₁ : Γ((Modules.pushforward k).obj ((moduleTensorLeftFunctor C L).obj O), ⊤),
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app ⊤ s₀ = σ ∧
        ((Modules.pushforward k).map (boundaryRestriction (i ≫ j) L O)).app ⊤ s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward (i ≫ j)).map
            ((moduleTensorLeftFunctor Z ((Modules.pullback (i ≫ j)).obj L)).map
              (boundaryScalar j i h)))).app ⊤ σ) ∧
        (openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app ⊤ s₁ =
          (((Modules.pushforward k).map ((Modules.pushforward j).map
            (openTwistScalar j L h))).app ⊤
              ((openSectionRestriction k j ((moduleTensorLeftFunctor C L).obj O)).app ⊤ s₀)) := by
  simpa only [boundaryGraphRatio_eq_boundaryScalar] using
    exists_prescribed_graph_pair R ι n e k j i h

end AlgebraicGeometry.Scheme.CoherentGraph
