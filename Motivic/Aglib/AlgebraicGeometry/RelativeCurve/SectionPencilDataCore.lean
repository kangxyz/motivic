module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.RetainedPencilFiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CorrespondenceSites
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.SerreDivisorPairs
public import Motivic.AlgebraicGeometry.Correspondences.DiagonalSignedPencilProducer
/-! # Actual relative curve sections fill the original correcting-correspondence data -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
/-- Internal literal assembly; the geometric producer supplies every divisor and family fact. -/
def relativeSectionPencilDataOfSections
    (k : Type u) [Field k] {S X Y A B C V : Scheme.{u}}
    [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
    (t : S ⟶ Spec (.of k)) [Smooth t]
    (q : X ⟶ S) [Smooth q] (π : C ⟶ S) [IsSeparated π]
    (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
    (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (a₀ : A ⟶ X) [Smooth a₀]
    (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a₀)
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
    (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a₀ ≫ q) π))
    (a : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (b : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (n d : SheafOfModules.unit (pullback (a₀ ≫ q) π).ringCatSheaf ⟶ N.val)
    (hFa : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (j ≫ π) π)
      (retainedProductInclusion (j ≫ π) π v)
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) a)
    (hFb : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (j ≫ π) π)
      (retainedProductInclusion (j ≫ π) π v) T b)
    (hFn : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (a₀ ≫ q) π)
      (retainedProductInclusion (a₀ ≫ q) π v) N n)
    (hFd : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (a₀ ≫ q) π)
      (retainedProductInclusion (a₀ ≫ q) π v) N d)
    (hfamily : retainedGraphFamilyFiniteFlat k (commonProjection π j α ≫ t)
      q π j p hq a₀ α β h v φ hφ T N a b n d)
    (hpole : retainedPoleFiniteFlat q π j p hq a₀ α β h v T N b d) :
    DiagonalSignedPencilProducer.Data
      (relativeAlpha k t π j α) (relativeBeta k t q π j a₀ α p hq β h)
      (relativeGraphMap k t π j α v φ hφ) := by
  let qA := j ≫ π
  let qN := a₀ ≫ q
  let qX := commonProjection π j α
  let iA := retainedProductInclusion qA π v
  let iN := retainedProductInclusion qN π v
  have hfa := hFa.2.2.2
  have hfb := hFb.2.2.2
  have hfn := hFn.2.2.2
  have hfd := hFd.2.2.2
  rw [retainedProductInclusion_fst] at hfa hfb hfn hfd
  obtain ⟨hAS, hAE, hAQ⟩ := retainedProduct_site_properties k t π v qA
  obtain ⟨hNS, hNE, hNQ⟩ := retainedProduct_site_properties k t π v qN
  obtain ⟨hXS, hXE, hXQ⟩ := retainedProduct_site_properties k t π v qX
  have hclosed : IsClosedImmersion (relativeRetainedGraph π j α v φ hφ) := by
    have : IsClosedImmersion (Hom.compactificationGraph π j) := by
      dsimp [Hom.compactificationGraph]
      infer_instance
    exact MorphismProperty.of_isPullback
      (relativeRetainedGraph_isPullback π j α v φ hφ) inferInstance
  exact {
    C := retainedProduct qA π v
    E := retainedProduct qN π v
    D := retainedProduct qX π v
    qA := pullback.fst _ _
    rA := pullback.snd _ _
    hA := by
      change pullback.fst qA (v ≫ π) ≫ (qA ≫ t) =
        pullback.snd qA (v ≫ π) ≫ ((v ≫ π) ≫ t)
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ t) (pullback.condition (f := qA) (g := v ≫ π))
    qN := pullback.fst _ _
    rN := pullback.snd _ _
    hN := by
      change pullback.fst qN (v ≫ π) ≫ (qN ≫ t) =
        pullback.snd qN (v ≫ π) ≫ ((v ≫ π) ≫ t)
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ t) (pullback.condition (f := qN) (g := v ≫ π))
    jA := retainedToLambda π j α v
    jN := retainedToPsi q π j p hq a₀ α β h v
    p := pullback.fst _ _
    squareA := retainedToLambda_isPullback π j α v
    squareN := retainedToPsi_isPullback q π j p hq a₀ α β h v
    g := pullback.snd _ _
    targetA := retainedToLambda_target π j α v
    targetN := retainedToPsi_target q π j p hq a₀ α β h v
    base := by
      change pullback.fst qX (v ≫ π) ≫ (qX ≫ t) =
        pullback.snd qX (v ≫ π) ≫ ((v ≫ π) ≫ t)
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ t) (pullback.condition (f := qX) (g := v ≫ π))
    A := pullbackLineBundle iA
      (dualLineBundle _ (tensorLineBundle _ T
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))))
    B := pullbackLineBundle iA (dualLineBundle _ T)
    N := pullbackLineBundle iN (dualLineBundle _ N)
    M := pullbackLineBundle iN (dualLineBundle _ N)
    a := Hom.pullbackToUnit
      (sectionDualFunctional _ (tensorLineBundle _ T
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))) a) iA
    b := Hom.pullbackToUnit (sectionDualFunctional _ T b) iA
    n := Hom.pullbackToUnit (sectionDualFunctional _ N n) iN
    d := Hom.pullbackToUnit (sectionDualFunctional _ N d) iN
    diagonal := relativeRetainedGraph π j α v φ hφ
    diagonal_closed := hclosed
    diagonal_source := relativeRetainedGraph_fst π j α v φ hφ
    diagonal_target := relativeRetainedGraph_snd π j α v φ hφ
    diagonal_line := commonRetainedGraph_locallyRankOne π j α v φ hφ
    alpha_flat := inferInstanceAs (Flat α)
    beta_flat := inferInstanceAs (Flat β)
    a_regular := hfa.2.1
    b_regular := hfb.2.1
    n_regular := hfn.2.1
    d_regular := hfd.2.1
    a_finite := hfa.1
    a_flat := hfa.2.2
    b_finite := hfb.1
    b_flat := hfb.2.2
    n_finite := hfn.1
    n_flat := hfn.2.2
    d_finite := hfd.1
    d_flat := hfd.2.2
    qA_smooth := hAS
    qA_separated := hAE
    qA_quasiCompact := hAQ
    qN_smooth := hNS
    qN_separated := hNE
    qN_quasiCompact := hNQ
    p_smooth := hXS
    p_separated := hXE
    p_quasiCompact := hXQ
    lineIso := retainedPencilLineIso q π j p hq a₀ α β h v φ hφ T N
    pole_finite := hpole.1
    pole_flat := hpole.2
    family_finite := hfamily.1
    family_flat := hfamily.2
  }
end AlgebraicGeometry.Scheme.RelativeCurvePencil
