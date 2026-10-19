/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.GlobalBoundaryPencil
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.Cartier.BaseEndpoints

/-! # Signed finite correspondences from actual global boundary pencils -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram

universe u

namespace Motivic.GlobalBoundaryPencil
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite

/-- Isomorphic whole finite-flat spans give exactly the same correspondence,
including all multiplicities of their nonreduced zero schemes. -/
theorem ofFiniteFlatSpan_precompIso {k : Type u} [Field k]
    {X Y : SmoothSite (Spec (.of k))} {D E : Scheme.{u}} (e : E ≅ D)
    (f : D ⟶ X.left) [IsFinite f] [Flat f] (g : D ⟶ Y.left)
    (h : f ≫ X.hom = g ≫ Y.hom) :
    Cor.ofFiniteFlatSpan (X := X) (Y := Y) (e.hom ≫ f) (e.hom ≫ g)
      (by simpa only [Category.assoc] using congrArg (fun z ↦ e.hom ≫ z) h) =
      Cor.ofFiniteFlatSpan f g h := by
  let : IsNoetherian D := isNoetherian_of_finiteType f
  let : IsNoetherian E := isNoetherian_of_finiteType (e.hom ≫ f)
  have : IsFinite (pullback.lift f g h) :=
    FiniteFlatCorrespondence.isFinite_productMap f _ (pullback.lift_fst _ _ _)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [Cor.toIntegralCycle_ofFiniteFlatSpan, Cor.toIntegralCycle_ofFiniteFlatSpan]
  have hm : pullback.lift (e.hom ≫ f) (e.hom ≫ g)
      (by simpa only [Category.assoc] using congrArg (fun z ↦ e.hom ≫ z) h) =
      e.hom ≫ pullback.lift f g h := by
    apply pullback.hom_ext <;> simp
  simp only [hm, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    Scheme.finitePushforward_fundamentalCycle]

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k))) [IsAffine X.left]
  {C B U : Scheme.{u}} (i : B ⟶ C) (q : C ⟶ relativeLine X.hom) [IsProper q]
  (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle C)
  (a b : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) (t : Γ(C, ⊤))
  [IsIso ((Scheme.Modules.pullback i).map a)]
  (h : Hom.pullbackToUnit a i = Hom.pullbackToUnit b i)
  (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)

local instance : IsAffine (relativeLine X.hom) := by
  let : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsAffine X.left)
  let : IsAffine (AffineLineField.line k).left := inferInstanceAs
    (IsAffine (Spec (.of (Polynomial k))))
  have : IsAffineHom (AffineLineField.line k).hom := by
    change IsAffineHom (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    infer_instance
  have : IsAffineHom (pullback.fst X.hom (AffineLineField.line k).hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact isAffine_of_isAffineHom
    (pullback.fst X.hom (AffineLineField.line k).hom)

/-- The actual constructed section on the retained smooth curve. -/
abbrev sectionMap := Hom.pullbackToUnit
  (Scheme.Modules.Invertible.GlobalBoundaryPencil.pencil a b t) j

include h hcover in
/-- Finiteness and flatness are supplied by the genuine boundary construction. -/
theorem family_properties :
    IsFinite (Hom.zeroInclusion (sectionMap j L a b t) ≫ j ≫ q) ∧
      Mono (sectionMap j L a b t) ∧ Flat (Hom.zeroInclusion (sectionMap j L a b t) ≫ j ≫ q) :=
  Scheme.Modules.Invertible.GlobalBoundaryPencil.pencil_finite_flat_on_open i q j L a b t h hcover

/-- The original relative projection as a smooth-site map. -/
def projectionMorphism : relativeLineSite X ⟶ X :=
  SmoothSite.homMk (pullback.fst X.hom (AffineLineField.line k).hom) rfl

omit [IsAffine X.left] in
@[simp] theorem endpoint_projection (c : k) :
    endpointMorphism X c ≫ projectionMorphism X = 𝟙 X := by
  ext : 1
  exact endpoint_fst X.hom c

variable (g : U ⟶ Y.left)
  (hbase : (j ≫ q) ≫ relativeLineHom X.hom = g ≫ Y.hom)

include q h hcover in
/-- The actual Cartier ideal of the constructed map, not an assumed divisor. -/
theorem idealRankOne : IsLocallyRankOne U (Scheme.Hom.idealModule
    (Hom.zeroInclusion (sectionMap j L a b t))) := by
  let E := pullbackLineBundle j L
  let := lineBundle_isLocallyFree C L
  let := lineBundle_isLocallyFree U (pullbackLineBundle j L)
  have : Mono (sectionMap j L a b t) := (family_properties X i q j L a b t h hcover).2.1
  let hloc := Hom.imageIdealLocalizes_of_isQuasicoherent (sectionMap j L a b t)
  have := Hom.zeroIdealFactor_isIso (sectionMap j L a b t) hloc
  exact isLocallyRankOne_of_iso U (asIso (Hom.zeroIdealFactor (sectionMap j L a b t) hloc))
    E.property

/-- The positive zero-family correspondence is constructed from the actual pencil. -/
def correspondence : Cor.mk (relativeLineSite X) ⟶ Cor.mk Y := by
  have hp := family_properties X i q j L a b t h hcover
  let := hp.1
  let := hp.2.2
  exact RelativeCartierDivisor.correspondence (X := relativeLineSite X) (Y := Y)
    (j ≫ q) (Hom.zeroInclusion (sectionMap j L a b t))
    (idealRankOne X i q j L a b t h hcover) (𝟙 U) (by simp) g
    (by simpa using hbase)

/-- The complete original endpoint, including all nilpotents and local lengths. -/
def endpointCorrespondence (c : k) : Cor.mk X ⟶ Cor.mk Y := by
  have hp := family_properties X i q j L a b t h hcover
  let := hp.1
  let := hp.2.2
  exact Cor.relativeFiniteFlatSpanEndpoint
    (Hom.zeroInclusion (sectionMap j L a b t) ≫ j ≫ q)
    (Hom.zeroInclusion (sectionMap j L a b t) ≫ g)
    (by simpa only [Category.assoc] using (congrArg
      (fun e ↦ Hom.zeroInclusion (sectionMap j L a b t) ≫ e) hbase)) c

/-- Graph evaluation is the whole actual zero fibre of the constructed pencil. -/
theorem graph_endpoint_correspondence (c : k) :
    (Cor.graphFunctor k).map (endpointMorphism X c) ≫
      correspondence X Y i q j L a b t h hcover g hbase =
    endpointCorrespondence X Y i q j L a b t h hcover g hbase c := by
  have hp := family_properties X i q j L a b t h hcover
  let := hp.1
  let := hp.2.2
  have hlift : IsOpenImmersion.lift (𝟙 U) (Hom.zeroInclusion (sectionMap j L a b t))
      (by simp) = Hom.zeroInclusion (sectionMap j L a b t) := by
    simpa using IsOpenImmersion.lift_fac (𝟙 U)
      (Hom.zeroInclusion (sectionMap j L a b t)) (by simp)
  simpa only [correspondence, endpointCorrespondence,
    RelativeCartierDivisor.relativeEndpointCorrespondence, RelativeCartierDivisor.targetMap,
    hlift] using RelativeCartierDivisor.graph_relative_endpoint_correspondence X (j ≫ q)
      (𝟙 U) (Hom.zeroInclusion (sectionMap j L a b t))
      (idealRankOne X i q j L a b t h hcover) (by simp) g (by simpa using hbase) c

/-- The constant whole zero-endpoint correspondence. -/
def constantCorrespondence : Cor.mk (relativeLineSite X) ⟶ Cor.mk Y :=
  (Cor.graphFunctor k).map (projectionMorphism X) ≫
    endpointCorrespondence X Y i q j L a b t h hcover g hbase 0

/-- Subtract the constant pole correspondence from the constructed zero family. -/
def signedCorrespondence : Cor.mk (relativeLineSite X) ⟶ Cor.mk Y :=
  correspondence X Y i q j L a b t h hcover g hbase -
    constantCorrespondence X Y i q j L a b t h hcover g hbase

/-- Endpoint cycles of the signed family retain the full scheme-theoretic fibres. -/
theorem graph_endpoint_signedCorrespondence (c : k) :
    (Cor.graphFunctor k).map (endpointMorphism X c) ≫
      signedCorrespondence X Y i q j L a b t h hcover g hbase =
    endpointCorrespondence X Y i q j L a b t h hcover g hbase c -
      endpointCorrespondence X Y i q j L a b t h hcover g hbase 0 := by
  rw [signedCorrespondence, constantCorrespondence, Preadditive.comp_sub,
    graph_endpoint_correspondence,
    ← Category.assoc, ← Functor.map_comp, endpoint_projection,
    CategoryTheory.Functor.map_id,
    Category.id_comp]

@[simp] theorem signedCorrespondence_zero :
    (Cor.graphFunctor k).map (endpointMorphism X 0) ≫
      signedCorrespondence X Y i q j L a b t h hcover g hbase = 0 := by
  rw [graph_endpoint_signedCorrespondence, sub_self]

/-- The one endpoint is the signed original numerator-minus-denominator fibre cycle. -/
theorem signedCorrespondence_one :
    (Cor.graphFunctor k).map (endpointMorphism X 1) ≫
      signedCorrespondence X Y i q j L a b t h hcover g hbase =
    endpointCorrespondence X Y i q j L a b t h hcover g hbase 1 -
      endpointCorrespondence X Y i q j L a b t h hcover g hbase 0 :=
  graph_endpoint_signedCorrespondence X Y i q j L a b t h hcover g hbase 1

end Motivic.GlobalBoundaryPencil
