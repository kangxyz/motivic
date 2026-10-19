/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairNormSpec
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairTargetGenericRatio
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairNormalizedUnit
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairGraphInfinityNorm
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FunctionalProduct.UnitDomainGeneric
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormMarkedChart
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormBoundaryRange
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.FunctionalQuotientAffineChart
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramed.SectionTransport
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.RationalUnitGluing
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.AffineBoundaryScalarRestriction
public import Motivic.Aglib.AlgebraicGeometry.Scheme.Sections.CoproductBoundary
/-! # Original section-pair norm charts on their unchanged good open

The open is formed only after fixing both original pairs. Its source condition
holds on the entire finite inverse image. No affine boundary ambient or
independently extended frame is chosen.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairNormNeighborhood`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.SectionPairNormParameterNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The inverse native source norm is the germ of the actual original graph
coefficient norm on a free affine chart. This comparison is independent of the
marked and infinity boundary arguments. -/
theorem sectionPairSource_genericRatio_inv_eq_chart_germ
    {S C Y T : Scheme.{u}} (π : C ⟶ S) [IsSeparated π]
    (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
    [IsIntegral T] (F : pullback (j ≫ π) π ⟶ T) [IsFinite F]
    (L : LineBundle (pullback (j ≫ π) π))
    (a : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (b : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ L.val)
    (U : T.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
      (tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) a)
      (pullback.fst F hU.fromSpec))]
    [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ L b) (pullback.fst F hU.fromSpec))] :
    let M := tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
    let c := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π j) L
      (Hom.idealInclusion (Hom.compactificationGraph π j)) b
    let af := sectionDualFunctional _ M a
    let cf := sectionDualFunctional _ M c
    ∀ [Mono af] [Mono cf],
    let : Algebra Γ(T, U) Γ(pullback F hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback F hU.fromSpec, ⊤)],
    (genericFiberLineRatioNorm F (dualLineBundle _ M) af cf)⁻¹ =
      T.germToFunctionField U (Algebra.norm Γ(T, U)
        (show Γ(pullback F hU.fromSpec, ⊤) from Modules.Hom.app
        (sectionPairGraphCoefficient π j L a b (pullback.fst F hU.fromSpec)) ⊤
          (1 : Γ(pullback F hU.fromSpec, ⊤)))) := by
  dsimp only
  intro haf hcf
  let M := tensorLineBundle _ L (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))
  let af := sectionDualFunctional _ M a
  let cf := sectionDualFunctional _ M (twistedIdealSection _
    (Hom.relativeCompactificationGraphLine π j) L
    (Hom.idealInclusion (Hom.compactificationGraph π j)) b)
  let : Mono af := haf
  let : Mono cf := hcf
  let : IsIso (pullbackUnitMap (pullback.fst F hU.fromSpec) af) := by
    change IsIso (Hom.pullbackToUnit af (pullback.fst F hU.fromSpec))
    dsimp only [af, M]
    infer_instance
  let : Algebra Γ(T, U) Γ(pullback F hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F hU.fromSpec)).toAlgebra
  intro hfree
  let := hfree
  have h := genericFiberLineRatioNorm_eq_chart_functionalQuotient F
    (dualLineBundle _ M) cf af U hU
  rw [genericFiberLineRatioNorm_swap] at h
  have hθ : sectionPairGraphCoefficient π j L a b (pullback.fst F hU.fromSpec) =
      inv (pullbackUnitMap (pullback.fst F hU.fromSpec) af) ≫
        pullbackUnitMap (pullback.fst F hU.fromSpec) cf :=
    sectionPairIdealFrame_graphCoefficient (pullback.fst F hU.fromSpec)
      (Hom.relativeCompactificationGraphLine π j) L b a
      (Hom.idealInclusion (Hom.compactificationGraph π j))
  rw [← hθ] at h
  exact h

/-- The final association-to-ratio calculation is pure field algebra. -/
theorem normAssociation_ratio_eq_inv {K : Type u} [Field K]
    (x y m : K) (hy : y ≠ 0) (h : x⁻¹ = m * y⁻¹) : x / y = m⁻¹ := by
  apply inv_inj.mp
  rw [inv_div, inv_inv, div_eq_mul_inv, h]
  calc
    y * (m * y⁻¹) = m * (y * y⁻¹) := mul_left_comm y m y⁻¹
    _ = m := by rw [mul_inv_cancel₀ hy, mul_one]

variable {S C P X Y : Scheme.{u}} (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) [IsFinite f] (jB : Y ⟶ C) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (hret : jB ≫ f = p ≫ jA)
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  (LB : LineBundle (pullback (jB ≫ f ≫ π) (f ≫ π)))
  (aB : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶
    (tensorLineBundle _ LB (dualLineBundle _
      (Hom.relativeCompactificationGraphLine (f ≫ π) jB))).val)
  (bB : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶ LB.val)

/-- The exact open defined by the four original section functionals. -/
def sectionPairNormUnitDomain : (pullback (jB ≫ f ≫ π) π).Opens :=
  let κ := Hom.retainedParameterProductMap π f jB jA p hret
  let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let MB := tensorLineBundle _ LB
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
  Scheme.functionalNormProductUnitDomain (Hom.graphProductMap π f jB)
    (dualLineBundle _ MB) (dualLineBundle _ LB)
    (sectionDualFunctional _ MB aB) (sectionDualFunctional _ LB bB)
    (pullbackLineBundle κ (dualLineBundle _ MA)) (pullbackLineBundle κ (dualLineBundle _ LA))
    (pullbackUnitMap κ (sectionDualFunctional _ MA aA))
    (pullbackUnitMap κ (sectionDualFunctional _ LA bA))

omit [Flat p] in
/-- The chart and its entire finite inverse image retain all four original units. -/
theorem sectionPairNormUnitDomain_chart_units {W : Scheme.{u}}
    (w : W ⟶ pullback (jB ≫ f ≫ π) π)
    (hw : Set.range w ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _)) :
    IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LB bB)
      (pullback.fst (Hom.graphProductMap π f jB) w)) ∧
    IsIso (Hom.pullbackToUnit (sectionDualFunctional _
      (tensorLineBundle _ LB (dualLineBundle _
        (Hom.relativeCompactificationGraphLine (f ≫ π) jB))) aB)
      (pullback.fst (Hom.graphProductMap π f jB) w)) ∧
    IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LA bA)
      (w ≫ Hom.retainedParameterProductMap π f jB jA p hret)) ∧
    IsIso (Hom.pullbackToUnit (sectionDualFunctional _
      (tensorLineBundle _ LA (dualLineBundle _
        (Hom.relativeCompactificationGraphLine π jA))) aA)
      (w ≫ Hom.retainedParameterProductMap π f jB jA p hret)) := by
  let κ := Hom.retainedParameterProductMap π f jB jA p hret
  let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let MB := tensorLineBundle _ LB
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
  have hB := Scheme.functionalNormProductUnitDomain_source_isIso (Hom.graphProductMap π f jB)
    (dualLineBundle _ MB) (dualLineBundle _ LB)
    (sectionDualFunctional _ MB aB) (sectionDualFunctional _ LB bB)
    (pullbackLineBundle κ (dualLineBundle _ MA)) (pullbackLineBundle κ (dualLineBundle _ LA))
    (pullbackUnitMap κ (sectionDualFunctional _ MA aA))
    (pullbackUnitMap κ (sectionDualFunctional _ LA bA)) w hw
  have hA := Scheme.functionalNormProductUnitDomain_target_isIso (Hom.graphProductMap π f jB)
    (dualLineBundle _ MB) (dualLineBundle _ LB)
    (sectionDualFunctional _ MB aB) (sectionDualFunctional _ LB bB)
    (pullbackLineBundle κ (dualLineBundle _ MA)) (pullbackLineBundle κ (dualLineBundle _ LA))
    (pullbackUnitMap κ (sectionDualFunctional _ MA aA))
    (pullbackUnitMap κ (sectionDualFunctional _ LA bA)) w hw
  have hcomp (M : LineBundle (pullback (jA ≫ π) π))
      (φ : M.val ⟶ SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf)
      (h : IsIso (pullbackUnitMap w (pullbackUnitMap κ φ))) :
      IsIso (pullbackUnitMap (w ≫ κ) φ) := by
    have : IsIso (((Modules.pullbackComp w κ).app M.val).hom ≫
        pullbackUnitMap (w ≫ κ) φ) := by
      rw [pullbackUnitMap_comp]
      exact h
    exact IsIso.of_isIso_comp_left ((Modules.pullbackComp w κ).app M.val).hom _
  exact ⟨hB.2, hB.1,
    hcomp (dualLineBundle _ LA) (sectionDualFunctional _ LA bA) hA.2,
    hcomp (dualLineBundle _ MA) (sectionDualFunctional _ MA aA) hA.1⟩

/-- Each actual chart in the good open constructs its own association unit from
the original graph quotient. The target frame is induced on this same chart. -/
theorem sectionPairNormUnitDomain_chart_association
    {R : Type u} [CommRing R] [IsDomain R]
    (w : Spec (.of R) ⟶ pullback (jB ≫ f ≫ π) π) [IsOpenImmersion w]
    (hw : Set.range w ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _)) :
    let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB w hw
    letI := h.1
    letI := h.2.1
    letI := h.2.2.1
    letI := h.2.2.2
    let vB := pullback.fst (Hom.graphProductMap π f jB) w
    let vA := w ≫ Hom.retainedParameterProductMap π f jB jA p hret
    let cB : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient (f ≫ π) jB LB aB bB vB) ⊤
      (1 : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤))
    let cA : R := (Scheme.ΓSpecIso (.of R)).hom
      (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA vA) ⊤
        (1 : Γ(Spec (.of R), ⊤)))
    let : Algebra R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (Hom.graphProductMap π f jB) w)).toAlgebra
    ∀ [Module.Free R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤)],
      ∃ μ : Rˣ, Algebra.norm R cB = (μ : R) * cA := by
  let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB w hw
  let := h.1
  let := h.2.1
  let := h.2.2.1
  let := h.2.2.2
  dsimp only
  intro hfree
  let : Algebra R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (Hom.graphProductMap π f jB) w)).toAlgebra
  let := hfree
  let κ := Hom.retainedParameterProductMap π f jB jA p hret
  let vA := w ≫ κ
  let l : Spec (.of R) ⟶ pullback κ vA := pullback.lift w (𝟙 _) (by simp [vA])
  obtain ⟨μ, hμ⟩ := sectionPairGraph_norm_association_spec
    π f jB jA p hret LA aA bA vA w l (pullback.lift_fst _ _ _) LB aB bB
  refine ⟨μ, ?_⟩
  have hlid : l ≫ pullback.snd κ vA = 𝟙 _ := pullback.lift_snd _ _ _
  rw [hlid, Hom.id_appTop, CommRingCat.id_apply] at hμ
  exact hμ

omit [Flat p] in
/-- The free affine neighborhoods are inherited from the original compact map
and refined inside the actual good open, not supplied as a normalized family. -/
theorem sectionPairNormUnitDomain_exists_free_chart
    {ι : Type u} (A : ι → CommRingCat.{u}) (v : ∀ i, Spec (A i) ⟶ P)
    [∀ i, IsOpenImmersion (v i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (v i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (v i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (v i))).toAlgebra
      Module.Free (A i) Γ(pullback f (v i), ⊤))
    (x : (pullback (jB ≫ f ≫ π) π : Scheme.{u}))
    (hx : x ∈ sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB) :
    ∃ (U : (pullback (jB ≫ f ≫ π) π).Opens) (hU : IsAffineOpen U), x ∈ U ∧
      U ≤ sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB ∧
      (let : Algebra Γ(pullback (jB ≫ f ≫ π) π, U)
          Γ(pullback (Hom.graphProductMap π f jB) hU.fromSpec, ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap
          (pullback.snd (Hom.graphProductMap π f jB) hU.fromSpec)).toAlgebra
       Module.Free Γ(pullback (jB ≫ f ≫ π) π, U)
         Γ(pullback (Hom.graphProductMap π f jB) hU.fromSpec, ⊤)) :=
  Hom.normProductMap_exists_free_affine_neighborhood_subset π f (jB ≫ f ≫ π)
    A v hcover hfree _ x hx

omit [Flat p] in
/-- The actual free charts cover exactly the unchanged good open. The index
is its own points, so no prescribed affine boundary neighborhood is involved. -/
theorem sectionPairNormUnitDomain_exists_free_cover
    {ι : Type u} (A : ι → CommRingCat.{u}) (v : ∀ i, Spec (A i) ⟶ P)
    [∀ i, IsOpenImmersion (v i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (v i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (v i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (v i))).toAlgebra
      Module.Free (A i) Γ(pullback f (v i), ⊤)) :
    let V := sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB
    ∃ (U : V → (pullback (jB ≫ f ≫ π) π).Opens) (hU : ∀ x, IsAffineOpen (U x)),
      (∀ x, x.val ∈ U x) ∧ iSup U = V ∧
      (∀ x,
        let : Algebra Γ(pullback (jB ≫ f ≫ π) π, U x)
            Γ(pullback (Hom.graphProductMap π f jB) (hU x).fromSpec, ⊤) :=
          (FiniteSchemeNormBaseChange.scalarMap
            (pullback.snd (Hom.graphProductMap π f jB) (hU x).fromSpec)).toAlgebra
        Module.Free Γ(pullback (jB ≫ f ≫ π) π, U x)
          Γ(pullback (Hom.graphProductMap π f jB) (hU x).fromSpec, ⊤)) := by
  dsimp only
  choose U hU hx hUV hfreeU using fun x :
    sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB =>
      sectionPairNormUnitDomain_exists_free_chart π f jB jA p hret LA aA bA LB aB bB
        A v hcover hfree x.val x.property
  refine ⟨U, hU, hx, le_antisymm (iSup_le hUV) ?_, hfreeU⟩
  intro x hxV
  exact Opens.mem_iSup.mpr ⟨⟨x, hxV⟩, hx ⟨x, hxV⟩⟩

omit [Flat p] in
/-- The canonical affine map of a contained open stays in the original domain.
This named proof also keeps exported chart-coefficient types free of private auxiliaries. -/
theorem sectionPairNormUnitDomain_fromSpec_range
    (U : (pullback (jB ≫ f ≫ π) π).Opens) (hU : IsAffineOpen U)
    (hUV : U ≤ sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB) :
    Set.range hU.fromSpec ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _) := by
  rw [hU.range_fromSpec]
  exact fun _ hx => hUV hx

omit [Flat p] in
/-- The association equation identifies the original native ratio, not a newly
chosen rational function. The source norm is taken on its whole generic algebra. -/
theorem sectionPairNormUnitDomain_chart_native_germ
    [IsIntegral (pullback (jB ≫ f ≫ π) π)]
    (U : (pullback (jB ≫ f ≫ π) π).Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hUV : U ≤ sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB) :
    let T := pullback (jB ≫ f ≫ π) π
    let F := Hom.graphProductMap π f jB
    let κ := Hom.retainedParameterProductMap π f jB jA p hret
    let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let MB := tensorLineBundle _ LB
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB
      (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB)) bB
    let afB := sectionDualFunctional _ MB aB
    let cfB := sectionDualFunctional _ MB cB
    let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
    let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
    ∀ [Mono afB] [Mono cfB] [Mono afA] [Mono cfA],
    let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB
      hU.fromSpec (sectionPairNormUnitDomain_fromSpec_range
        π f jB jA p hret LA aA bA LB aB bB U hU hUV)
    letI := h.1
    letI := h.2.1
    letI := h.2.2.1
    letI := h.2.2.2
    let θB : Γ(pullback F hU.fromSpec, ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient (f ≫ π) jB LB aB bB (pullback.fst F hU.fromSpec)) ⊤
        (1 : Γ(pullback F hU.fromSpec, ⊤))
    let θA : Γ(T, U) := (Scheme.ΓSpecIso Γ(T, U)).hom
      (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA (hU.fromSpec ≫ κ)) ⊤
        (1 : Γ(Spec Γ(T, U), ⊤)))
    let : Algebra Γ(T, U) Γ(pullback F hU.fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F hU.fromSpec)).toAlgebra
    ∀ [Module.Free Γ(T, U) Γ(pullback F hU.fromSpec, ⊤)] (μ : Γ(T, U)ˣ),
      Algebra.norm Γ(T, U) θB = (μ : Γ(T, U)) * θA →
      genericFiberLineRatioNorm F (dualLineBundle _ MB) afB cfB /
        genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA =
      T.germToFunctionField U (↑(μ⁻¹) : Γ(T, U)) := by
  dsimp only
  intro hafB hcfB hafA hcfA
  let T := pullback (jB ≫ f ≫ π) π
  let F := Hom.graphProductMap π f jB
  let κ := Hom.retainedParameterProductMap π f jB jA p hret
  let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let MB := tensorLineBundle _ LB
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
    (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
  let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB
    (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB)) bB
  let afB := sectionDualFunctional _ MB aB
  let cfB := sectionDualFunctional _ MB cB
  let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
  let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
  let : Mono afB := hafB
  let : Mono cfB := hcfB
  let : Mono afA := hafA
  let : Mono cfA := hcfA
  have hw : Set.range hU.fromSpec ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _) :=
    by rw [hU.range_fromSpec]; exact fun _ hx => hUV hx
  let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB hU.fromSpec hw
  let := h.1
  let := h.2.1
  let := h.2.2.1
  let := h.2.2.2
  intro hfree μ hμ
  let : Algebra Γ(T, U) Γ(pullback F hU.fromSpec, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F hU.fromSpec)).toAlgebra
  let := hfree
  let : IsIso (pullbackUnitMap (pullback.fst F hU.fromSpec) afB) := by
    change IsIso (Hom.pullbackToUnit afB (pullback.fst F hU.fromSpec))
    exact h.2.1
  have hi := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB U.ι
    (by rw [Scheme.Opens.range_ι]; exact fun _ hx => hUV hx)
  let := hi.2.2.2
  have hB := sectionPairSource_genericRatio_inv_eq_chart_germ
    (f ≫ π) jB F LB aB bB U hU
  have hA := sectionPairTarget_genericRatio_inv_eq_chart_germ π jA LA aA bA κ U hU
  rw [hμ, map_mul, ← hA] at hB
  have hA0 := genericFiberLineRatioNorm_ne_zero (𝟙 T)
    (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA
  have hinv : T.germToFunctionField U (↑(μ⁻¹) : Γ(T, U)) =
      (T.germToFunctionField U (μ : Γ(T, U)))⁻¹ := by
    exact Units.val_inv_eq_inv_val (Units.map (T.germToFunctionField U).hom.toMonoidHom μ)
  rw [hinv]
  exact normAssociation_ratio_eq_inv _ _ _ hA0 hB

omit [IsSeparated π] in
/-- The two actual affine boundary scalar equalities yield exact value one of
the inverse unit on the full boundary scheme, without reducing either component. -/
theorem normFullBoundaryMap_app_inv_eq_one
    {A I Z : Scheme.{u}} (b : A ⟶ S) (i : I ⟶ P) (z : Z ⟶ P)
    (U : (pullback b π).Opens) (hU : IsAffineOpen U) (μ : Γ(pullback b π, U)ˣ)
    (hi : FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd i (hU.fromSpec ≫ pullback.snd b π)) (μ : Γ(pullback b π, U)) = 1)
    (hz : FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd z (hU.fromSpec ≫ pullback.snd b π)) (μ : Γ(pullback b π, U)) = 1) :
    (Hom.normFullBoundaryMap π b i z).app U (↑(μ⁻¹) : Γ(pullback b π, U)) = 1 := by
  have hcomp {D : Scheme.{u}} (d : D ⟶ P)
      (hd : FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd d (hU.fromSpec ≫ pullback.snd b π))
          (μ : Γ(pullback b π, U)) = 1) :
      (retainedProductInclusion b π d).app U (↑(μ⁻¹) : Γ(pullback b π, U)) = 1 := by
    have hval := FiniteSchemeNormBaseChange.app_eq_one_of_isPullback_affine_scalar_eq_one
      (retainedProductInclusion b π d) (pullback.snd b (d ≫ π)) d (pullback.snd b π)
      (retainedProductInclusion_isPullback b π d) U hU (μ : Γ(pullback b π, U)) hd
    have hunit : Units.map ((retainedProductInclusion b π d).app U).hom.toMonoidHom μ = 1 :=
      Units.ext hval
    change (↑((Units.map ((retainedProductInclusion b π d).app U).hom.toMonoidHom μ)⁻¹) :
      Γ(retainedProduct b π d, (retainedProductInclusion b π d) ⁻¹ᵁ U)) = 1
    rw [hunit]
    rfl
  exact coprod_desc_app_eq_one (retainedProductInclusion b π i)
    (retainedProductInclusion b π z) U _ (hcomp i hi) (hcomp z hz)

section Marked

variable {Z D DA : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (hA : jA ≫ π = q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  [IsClosedImmersion (z ≫ jA)]
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range jB) (Set.range d))
  (hpairB : pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) aB ≫
      pullbackTensorMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) LB.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB)).val =
    tensorUnitSection (pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) bB)
      (Hom.relativeFullBoundaryFrame q (f ≫ π) jB p
        (Hom.retained_source_structure q π f jB jA p hret hA) z s hs H e d hd).inv)
  (bE : (Scheme.residualMarkedFiberOpen f jB (z ≫ jA) s
    (Hom.retainedSectionPair_marked_map f jB jA p hret z s hs)).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f jB (z ≫ jA) s
    (Hom.retainedSectionPair_marked_map f jB jA p hret z s hs))
  (dA : DA ⟶ P) (hdA : Disjoint (Set.range jA) (Set.range dA))
  (hpairA : pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) aA ≫
      pullbackTensorMap (Hom.fullBoundaryProductMap π jA dA z) LA.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA)).val =
    tensorUnitSection (pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) bA)
      (Hom.relativeFullBoundaryFrame q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)

include hpairB hbE hpairA in
/-- The unit is constructed from the actual graph quotient and is one in the
canonical full marked chart ring. All marked chart maps are constructed here. -/
theorem sectionPairNormUnitDomain_chart_marked_association
    {R : Type u} [CommRing R] [IsDomain R]
    (w : Spec (.of R) ⟶ pullback (jB ≫ f ≫ π) π) [IsOpenImmersion w]
    (hw : Set.range w ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _)) :
    let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB w hw
    letI := h.1
    letI := h.2.1
    letI := h.2.2.1
    letI := h.2.2.2
    let vB := pullback.fst (Hom.graphProductMap π f jB) w
    let vA := w ≫ Hom.retainedParameterProductMap π f jB jA p hret
    let cB : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient (f ≫ π) jB LB aB bB vB) ⊤
      (1 : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤))
    let cA : R := (Scheme.ΓSpecIso (.of R)).hom
      (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA vA) ⊤
        (1 : Γ(Spec (.of R), ⊤)))
    let φ := FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd (z ≫ jA) (w ≫ pullback.snd (jB ≫ f ≫ π) π))
    let : Algebra R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (Hom.graphProductMap π f jB) w)).toAlgebra
    ∀ [Module.Free R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤)],
      ∃ μ : Rˣ, Algebra.norm R cB = (μ : R) * cA ∧ φ (μ : R) = 1 := by
  let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB w hw
  let := h.1
  let := h.2.1
  let := h.2.2.1
  let := h.2.2.2
  dsimp only
  intro hfree
  let : Algebra R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (Hom.graphProductMap π f jB) w)).toAlgebra
  let := hfree
  obtain ⟨μ, hμ⟩ := sectionPairNormUnitDomain_chart_association
    π f jB jA p hret LA aA bA LB aB bB w hw
  refine ⟨μ, hμ, ?_⟩
  let F := Hom.graphProductMap π f jB
  let n := pullback.snd F w
  let u := Hom.normChartSourceMap π f (jB ≫ f ≫ π) w
  let t := w ≫ pullback.snd (jB ≫ f ≫ π) π
  let φ := FiniteSchemeNormBaseChange.scalarMap (pullback.snd (z ≫ jA) t)
  let a := (pullback (z ≫ jA) t).isoSpec.inv ≫ pullback.fst (z ≫ jA) t
  have Hz := Scheme.affineMarkedChart_isPullback (z ≫ jA) t
  have hz : Spec.map (CommRingCat.ofHom φ) ≫ t = a ≫ (z ≫ jA) := Hz.w.symm
  have Hf : IsPullback u n f t := Hom.normChartSourceMap_isPullback π f (jB ≫ f ≫ π) w
  have H0 : IsPullback s (𝟙 Z) (jB ≫ f) (z ≫ jA) := by
    rw [hret]
    exact Scheme.marked_isPullback_comp_mono p z s H jA
  let k := pullback.fst u jB
  let σ := Scheme.markedOpenChartSection f jB (z ≫ jA) s H0 n u t Hf
    (Spec.map (CommRingCat.ofHom φ)) a hz
  have hn : (σ ≫ k) ≫ n = Spec.map (CommRingCat.ofHom φ) := by
    simp [σ, k]
  have HN : IsPullback σ (𝟙 _) (k ≫ n) (Spec.map (CommRingCat.ofHom φ)) :=
    Scheme.markedOpenChartSection_isPullback f jB (z ≫ jA) s H0 n u t Hf
      (Spec.map (CommRingCat.ofHom φ)) a hz
  have hj : a ≫ (s ≫ jB) = (σ ≫ k) ≫ u := by
    simp [σ, k]
  let κ := Hom.retainedParameterProductMap π f jB jA p hret
  let vA := w ≫ κ
  let l : Spec (.of R) ⟶ pullback κ vA := pullback.lift w (𝟙 _) (by simp [vA])
  apply Hom.sectionPairGraph_association_marked_eq_one q π f jB jA p hret hA
    z s hs H e d hd LB aB bB hpairB n φ k σ hn HN u t Hf a hz hj
    (pullback.fst F w) rfl bE hbE dA hdA LA aA bA hpairA vA w
    (pullback.condition) l (pullback.lift_fst _ _ _) Hz μ
  have hlid : l ≫ pullback.snd κ vA = 𝟙 _ := pullback.lift_snd _ _ _
  rw [hlid, Hom.id_appTop, CommRingCat.id_apply]
  exact hμ

include hpairB hbE hpairA in
/-- The SAME constructed unit is one on both complete boundary components. -/
theorem sectionPairNormUnitDomain_chart_boundary_association
    {R : Type u} [CommRing R] [IsDomain R]
    [IsAffineHom dA]
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
    (w : Spec (.of R) ⟶ pullback (jB ≫ f ≫ π) π) [IsOpenImmersion w]
    (hw : Set.range w ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _)) :
    let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB w hw
    letI := h.1
    letI := h.2.1
    letI := h.2.2.1
    letI := h.2.2.2
    let vB := pullback.fst (Hom.graphProductMap π f jB) w
    let vA := w ≫ Hom.retainedParameterProductMap π f jB jA p hret
    let cB : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient (f ≫ π) jB LB aB bB vB) ⊤
      (1 : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤))
    let cA : R := (Scheme.ΓSpecIso (.of R)).hom
      (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA vA) ⊤
        (1 : Γ(Spec (.of R), ⊤)))
    let φ := FiniteSchemeNormBaseChange.scalarMap
      (pullback.snd (z ≫ jA) (w ≫ pullback.snd (jB ≫ f ≫ π) π))
    let : Algebra R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (Hom.graphProductMap π f jB) w)).toAlgebra
    ∀ [Module.Free R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤)],
      ∃ μ : Rˣ, Algebra.norm R cB = (μ : R) * cA ∧ φ (μ : R) = 1 ∧
        FiniteSchemeNormBaseChange.scalarMap
          (pullback.snd dA (w ≫ pullback.snd (jB ≫ f ≫ π) π)) (μ : R) = 1 := by
  let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB w hw
  let := h.1
  let := h.2.1
  let := h.2.2.1
  let := h.2.2.2
  dsimp only
  intro hfree
  let : Algebra R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (Hom.graphProductMap π f jB) w)).toAlgebra
  let := hfree
  obtain ⟨μ, hμ, hmarked⟩ := sectionPairNormUnitDomain_chart_marked_association
    π f jB jA p hret LA aA bA LB aB bB q hA z s hs H e d hd hpairB bE hbE dA hdA hpairA w hw
  refine ⟨μ, hμ, hmarked, ?_⟩
  let F := Hom.graphProductMap π f jB
  let n := pullback.snd F w
  let u := Hom.normChartSourceMap π f (jB ≫ f ≫ π) w
  let t := w ≫ pullback.snd (jB ≫ f ≫ π) π
  let Q := Γ(pullback dA t, ⊤)
  let φ := FiniteSchemeNormBaseChange.scalarMap (pullback.snd dA t)
  let τ := (pullback dA t).isoSpec.inv ≫ pullback.fst dA t
  let δ := Spec.map (CommRingCat.ofHom φ)
  have hτ : δ ≫ t = τ ≫ dA := (Scheme.affineMarkedChart_isPullback dA t).w.symm
  have Hf : IsPullback u n f t := Hom.normChartSourceMap_isPullback π f (jB ≫ f ≫ π) w
  have hN := sectionPairGraphCoefficient_norm_infinity
    q (f ≫ π) jB p (Hom.retained_source_structure q π f jB jA p hret hA)
    z s hs H e d hd LB aB bB hpairB f dA bI hbI n φ u t Hf τ hτ (pullback.fst F w) rfl
  let κ := Hom.retainedParameterProductMap π f jB jA p hret
  let vA := w ≫ κ
  have hc : (δ ≫ vA) ≫ pullback.snd (jA ≫ π) π = τ ≫ dA := by
    simpa only [vA, κ, Category.assoc, Hom.retainedParameterProductMap_snd] using hτ
  let r := pullback.lift (δ ≫ vA) τ hc
  have hTA := sectionPairGraphCoefficient_infinity_scalar
    q π jA (𝟙 X) (hA.trans (Category.id_comp q).symm)
    z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA
    LA aA bA hpairA vA δ r (pullback.lift_fst _ _ _).symm
  let c : Γ(Spec (.of R), ⊤) := Modules.Hom.app
    (sectionPairGraphCoefficient π jA LA aA bA vA) ⊤ (1 : Γ(Spec (.of R), ⊤))
  have hnat := congrArg
    (fun m : Γ(Spec (.of R), ⊤) ⟶ CommRingCat.of Q => m c)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  have hT : φ ((Scheme.ΓSpecIso (.of R)).hom c) = 1 := by
    change (Scheme.ΓSpecIso (.of Q)).hom (δ.appTop c) =
      φ ((Scheme.ΓSpecIso (.of R)).hom c) at hnat
    rw [show δ.appTop c = 1 from hTA, map_one] at hnat
    exact hnat.symm
  have hm := congrArg φ hμ
  rw [map_mul, hN, hT, mul_one] at hm
  exact hm.symm

omit [Flat p] [IsClosedImmersion (z ≫ jA)] in
include hbE in
/-- Original full-boundary section units put the ENTIRE target boundary in the
same good open. Set-theoretic containment is used only for this open factor. -/
theorem sectionPairNormUnitDomain_contains_boundary
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) aB)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) bB)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) aA)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) bA)]
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA) :
    Set.range (Hom.normFullBoundaryMap π (jB ≫ f ≫ π) dA (z ≫ jA)) ⊆
      (sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB : Set _) := by
  let κ := Hom.retainedParameterProductMap π f jB jA p hret
  let E := Hom.normFullBoundaryMap π (jB ≫ f ≫ π) dA (z ≫ jA)
  let DA := Hom.fullBoundaryProductMap π jA dA z
  let DB := Hom.fullBoundaryProductMap (f ≫ π) jB d s
  let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let MB := tensorLineBundle _ LB
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
  have htarget : Set.range (E ≫ κ) ⊆ Set.range DA := by
    rintro _ ⟨x, rfl⟩
    rw [Hom.range_fullBoundaryProductMap]
    have hx : E x ∈ Set.range E := ⟨x, rfl⟩
    rw [Hom.range_normFullBoundaryMap] at hx
    change (E ≫ κ ≫ pullback.snd (jA ≫ π) π) x ∈
      Set.range dA ∪ Set.range (z ≫ jA)
    dsimp only [κ]
    rw [Hom.retainedParameterProductMap_snd]
    exact hx
  have hi (M : LineBundle (pullback (jA ≫ π) π))
      (φ : M.val ⟶ SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf)
      [IsIso ((Modules.pullback DA).map φ)] :
      IsIso ((Modules.pullback E).map (pullbackUnitMap κ φ)) := by
    have : IsIso (pullbackUnitMap (E ≫ κ) φ) :=
      isIso_pullbackUnitMap_of_range_subset_unitOpen M φ (E ≫ κ)
        (htarget.trans (range_subset_zeroSupportUnitOpen_of_pullback_isIso M φ DA))
    have : IsIso (pullbackUnitMap E (pullbackUnitMap κ φ)) :=
      pullbackUnitMap_nested_isIso_of_comp κ E φ
    change IsIso ((Modules.pullback E).map (pullbackUnitMap κ φ) ≫
      (pullbackUnitIso E).hom) at this
    exact (isIso_comp_right_iff _ _).mp this
  have : IsIso ((Modules.pullback DA).map (sectionDualFunctional _ MA aA)) :=
    sectionDualFunctional_pullback_map_isIso DA MA aA
  have : IsIso ((Modules.pullback DA).map (sectionDualFunctional _ LA bA)) :=
    sectionDualFunctional_pullback_map_isIso DA LA bA
  have : IsIso ((Modules.pullback E).map (pullbackUnitMap κ (sectionDualFunctional _ MA aA))) :=
    hi (dualLineBundle _ MA) _
  have : IsIso ((Modules.pullback E).map (pullbackUnitMap κ (sectionDualFunctional _ LA bA))) :=
    hi (dualLineBundle _ LA) _
  have : IsIso ((Modules.pullback DB).map (sectionDualFunctional _ MB aB)) :=
    sectionDualFunctional_pullback_map_isIso DB MB aB
  have : IsIso ((Modules.pullback DB).map (sectionDualFunctional _ LB bB)) :=
    sectionDualFunctional_pullback_map_isIso DB LB bB
  have hsource := Hom.graphProductMap_preimage_fullBoundary_subset π f jB (z ≫ jA) s
    (Hom.retainedSectionPair_marked_map f jB jA p hret z s hs) d dA bI hbI bE hbE
  exact Scheme.range_subset_functionalNormProductUnitDomain (Hom.graphProductMap π f jB)
    (dualLineBundle _ MB) (dualLineBundle _ LB)
    (sectionDualFunctional _ MB aB) (sectionDualFunctional _ LB bB)
    (pullbackLineBundle κ (dualLineBundle _ MA)) (pullbackLineBundle κ (dualLineBundle _ LA))
    (pullbackUnitMap κ (sectionDualFunctional _ MA aA))
    (pullbackUnitMap κ (sectionDualFunctional _ LA bA)) E
    (hsource.trans (range_subset_zeroSupportUnitOpen_of_pullback_isIso _ _ DB))
    (hsource.trans (range_subset_zeroSupportUnitOpen_of_pullback_isIso _ _ DB))

include hpairB hbE hpairA in
/-- The original two section pairs construct a regular unit on their exact good
open. Its native germ is the original norm ratio, and its value on the complete
original boundary scheme is one. The affine family and all its units are built
inside this proof, rather than supplied as a normalization premise. -/
theorem sectionPairNormUnitDomain_exists_normalized_ratio
    [IsIntegral (pullback (jB ≫ f ≫ π) π)] [IsAffineHom dA]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) aB)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap (f ≫ π) jB d s) bB)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) aA)]
    [IsIso (pullbackSectionMap (Hom.fullBoundaryProductMap π jA dA z) bA)]
    (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
    {ι : Type u} (A : ι → CommRingCat.{u}) (v : ∀ i, Spec (A i) ⟶ P)
    [∀ i, IsOpenImmersion (v i)]
    (hcover : ∀ x : P, ∃ i, x ∈ Set.range (v i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (v i), ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f (v i))).toAlgebra
      Module.Free (A i) Γ(pullback f (v i), ⊤)) :
    let T := pullback (jB ≫ f ≫ π) π
    let F := Hom.graphProductMap π f jB
    let κ := Hom.retainedParameterProductMap π f jB jA p hret
    let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
    let MB := tensorLineBundle _ LB
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
    let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
      (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
    let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB
      (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB)) bB
    let afB := sectionDualFunctional _ MB aB
    let cfB := sectionDualFunctional _ MB cB
    let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
    let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
    let bfB := sectionDualFunctional _ LB bB
    let bfA := pullbackUnitMap κ (sectionDualFunctional _ LA bA)
    ∀ [Mono afB] [Mono cfB] [Mono afA] [Mono cfA] [Mono bfB] [Mono bfA],
    let V := sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB
    let E := Hom.normFullBoundaryMap π (jB ≫ f ≫ π) dA (z ≫ jA)
    ∃ (hV : Nonempty V) (R : Γ(T, V)) (eV : _ ⟶ V.toScheme),
      eV ≫ V.ι = E ∧ IsUnit R ∧
      (letI := hV
       T.germToFunctionField V R =
        genericFiberLineRatioNorm F (dualLineBundle _ MB) afB cfB /
          genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA) ∧
      E.app V R = 1 := by
  dsimp only
  intro hafB hcfB hafA hcfA hbfB hbfA
  let T := pullback (jB ≫ f ≫ π) π
  let F := Hom.graphProductMap π f jB
  let κ := Hom.retainedParameterProductMap π f jB jA p hret
  let MA := tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))
  let MB := tensorLineBundle _ LB
    (dualLineBundle _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB))
  let cA := twistedIdealSection _ (Hom.relativeCompactificationGraphLine π jA) LA
    (Hom.idealInclusion (Hom.compactificationGraph π jA)) bA
  let cB := twistedIdealSection _ (Hom.relativeCompactificationGraphLine (f ≫ π) jB) LB
    (Hom.idealInclusion (Hom.compactificationGraph (f ≫ π) jB)) bB
  let afB := sectionDualFunctional _ MB aB
  let cfB := sectionDualFunctional _ MB cB
  let afA := pullbackUnitMap κ (sectionDualFunctional _ MA aA)
  let cfA := pullbackUnitMap κ (sectionDualFunctional _ MA cA)
  let : Mono afB := hafB
  let : Mono cfB := hcfB
  let : Mono afA := hafA
  let : Mono cfA := hcfA
  let bfB := sectionDualFunctional _ LB bB
  let bfA := pullbackUnitMap κ (sectionDualFunctional _ LA bA)
  let : Mono bfB := hbfB
  let : Mono bfA := hbfA
  let V := sectionPairNormUnitDomain π f jB jA p hret LA aA bA LB aB bB
  let E := Hom.normFullBoundaryMap π (jB ≫ f ≫ π) dA (z ≫ jA)
  let Rnative := genericFiberLineRatioNorm F (dualLineBundle _ MB) afB cfB /
    genericFiberLineRatioNorm (𝟙 T) (pullbackLineBundle κ (dualLineBundle _ MA)) afA cfA
  have hEV : Set.range E ⊆ (V : Set T) :=
    sectionPairNormUnitDomain_contains_boundary π f jB jA p hret LA aA bA LB aB bB
      z s hs d bE hbE dA bI hbI
  have hV : Nonempty V :=
    Scheme.functionalNormProductUnitDomain_nonempty F (dualLineBundle _ MB)
      (dualLineBundle _ LB) afB bfB (pullbackLineBundle κ (dualLineBundle _ MA))
      (pullbackLineBundle κ (dualLineBundle _ LA)) afA bfA
  let := hV
  obtain ⟨U, hU, hx, hunion, hfreeU⟩ := sectionPairNormUnitDomain_exists_free_cover
    π f jB jA p hret LA aA bA LB aB bB A v hcover hfree
  let (x : V) : Nonempty (U x) := ⟨⟨x.val, hx x⟩⟩
  have hUV (x : V) : U x ≤ V := (le_iSup U x).trans hunion.le
  have hlocal (x : V) : ∃ μ : Γ(T, U x)ˣ,
      T.germToFunctionField (U x) (↑(μ⁻¹) : Γ(T, U x)) = Rnative ∧
      E.app (U x) (↑(μ⁻¹) : Γ(T, U x)) = 1 := by
    have hw : Set.range (hU x).fromSpec ⊆ (V : Set T) := by
      rw [(hU x).range_fromSpec]
      exact fun _ hy => hUV x hy
    let h := sectionPairNormUnitDomain_chart_units π f jB jA p hret LA aA bA LB aB bB
      (hU x).fromSpec hw
    let := h.1
    let := h.2.1
    let := h.2.2.1
    let := h.2.2.2
    let : Algebra Γ(T, U x) Γ(pullback F (hU x).fromSpec, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd F (hU x).fromSpec)).toAlgebra
    let := hfreeU x
    obtain ⟨μ, hμ, hm, hi⟩ := sectionPairNormUnitDomain_chart_boundary_association
      π f jB jA p hret LA aA bA LB aB bB q hA z s hs H e d hd hpairB bE hbE
      dA hdA hpairA bI hbI (hU x).fromSpec hw
    refine ⟨μ, ?_, normFullBoundaryMap_app_inv_eq_one π (jB ≫ f ≫ π) dA (z ≫ jA)
      (U x) (hU x) μ hi hm⟩
    exact (sectionPairNormUnitDomain_chart_native_germ π f jB jA p hret LA aA bA LB aB bB
      (U x) (hU x) (hUV x) μ hμ).symm
  choose μ hμR hμE using hlocal
  have : Nonempty (iSup U : T.Opens) := hunion.symm ▸ hV
  obtain ⟨R, eV, heV, hRunit, hRgerm, _, hRboundary⟩ :=
    Scheme.exists_rationalUnit_boundary_gluing E U Rnative
      (fun x => (↑((μ x)⁻¹) : Γ(T, U x))) (fun x => ((μ x)⁻¹).isUnit)
      hμR hμE (by simpa only [hunion] using hEV)
  have hout : ∃ (hW : Nonempty (iSup U : T.Opens)) (R : Γ(T, iSup U))
      (eW : _ ⟶ (iSup U).toScheme), eW ≫ (iSup U).ι = E ∧ IsUnit R ∧
      (letI := hW; T.germToFunctionField (iSup U) R = Rnative) ∧ E.app (iSup U) R = 1 :=
    ⟨inferInstance, R, eV, heV, hRunit, hRgerm, hRboundary⟩
  have result : ∀ W : T.Opens, W = iSup U →
      ∃ (hW : Nonempty W) (R : Γ(T, W)) (eW : _ ⟶ W.toScheme),
        eW ≫ W.ι = E ∧ IsUnit R ∧
        (letI := hW; T.germToFunctionField W R = Rnative) ∧ E.app W R = 1 := by
    rintro W rfl
    exact hout
  exact result V hunion.symm

end Marked

end AlgebraicGeometry.Scheme.RelativeCurvePencil
