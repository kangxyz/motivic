module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualRetainedPencilFiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualPencilSiteMaps
public import Motivic.AlgebraicGeometry.Correspondences.DiagonalSignedPencilProducer
/-! # Constructing the actual correcting correspondence data from the original curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
/-- The original geometric and section maps fill the correspondence data literally. -/
def actualSectionPencilDataOfSections
    (k : Type u) [Field k] {Y S A X : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (r : S ⟶ Y) [IsOpenImmersion r] [QuasiCompact r]
    (v : A ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion v]
    (α : X ⟶ S) [IsOpenImmersion α] [QuasiCompact α]
    (β : X ⟶ A) [Etale β] (h : α ≫ r ≫ p = β ≫ v)
    (U : (Spec (.of (Polynomial k))).Opens)
    (φ : X ⟶ pullback U.ι p)
    (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p)
    (T : LineBundle (diagonalAmbient k p r)) (N : LineBundle (fixedAmbient k p v))
    (a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)).val)
    (b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val)
    (n d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val)
    (hFa : RetainedSectionFiniteFlat k p r U
      (tensorLineBundle _ T (actualDivisorLineBundle k p r)) a)
    (hFb : RetainedSectionFiniteFlat k p r U T b)
    (hFn : FixedRetainedSectionFiniteFlat k p v U N n)
    (hFd : FixedRetainedSectionFiniteFlat k p v U N d)
    (hfamily : retainedGraphFamilyFiniteFlat k p r v α β h U φ hφ T N a b n d)
    (hpole : retainedPoleFiniteFlat k p r v α β h U T N b d) :
    DiagonalSignedPencilProducer.Data
      (pencilAlpha k p r α) (pencilBeta k p r v α β h) (pencilGraphMap k p r α U φ hφ) := by
  let qA := (r ≫ inclusion k p) ≫ projection k p
  let qN := v ≫ Hom.boundaryLineProjection k
  let qX := commonSourceProjection k p r α
  let iA := constantRetainedInclusion k p U qA
  let iN := constantRetainedInclusion k p U qN
  have hfa := hFa
  have hfb := hFb
  have hfn := hFn
  have hfd := hFd
  dsimp only [RetainedSectionFiniteFlat] at hfa hfb
  dsimp only [FixedRetainedSectionFiniteFlat] at hfn hfd
  rw [constantRetainedInclusion_fst] at hfa hfb hfn hfd
  have : Smooth qA := inferInstanceAs (Smooth (diagonalSourceSite k p r).hom)
  have : IsSeparated qA := inferInstanceAs (IsSeparated (diagonalSourceSite k p r).hom)
  have : QuasiCompact qA := inferInstanceAs (QuasiCompact (diagonalSourceSite k p r).hom)
  have : Smooth qN := inferInstanceAs (Smooth (fixedSourceSite k v).hom)
  have : IsSeparated qN := inferInstanceAs (IsSeparated (fixedSourceSite k v).hom)
  have : QuasiCompact qN := inferInstanceAs (QuasiCompact (fixedSourceSite k v).hom)
  have : Smooth qX := inferInstanceAs (Smooth (commonSourceSite k p r α).hom)
  have : IsSeparated qX := inferInstanceAs (IsSeparated (commonSourceSite k p r α).hom)
  have : QuasiCompact qX := inferInstanceAs (QuasiCompact (commonSourceSite k p r α).hom)
  obtain ⟨hAS, hAE, hAQ⟩ := constantRetainedTarget_site_properties k p U qA
  obtain ⟨hNS, hNE, hNQ⟩ := constantRetainedTarget_site_properties k p U qN
  obtain ⟨hXS, hXE, hXQ⟩ := constantRetainedTarget_site_properties k p U qX
  have hclosed : IsClosedImmersion (commonRetainedGraph k p r α U φ hφ) := by
    have : IsClosedImmersion (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p)) := by
      dsimp [Hom.compactificationGraph]
      infer_instance
    exact MorphismProperty.of_isPullback
      (commonRetainedGraph_isPullback k p r α U φ hφ) inferInstance
  exact {
    C := constantRetainedTarget k p U qA
    E := constantRetainedTarget k p U qN
    D := constantRetainedTarget k p U qX
    qA := pullback.fst _ _
    rA := pullback.snd _ _
    hA := pullback.condition
    qN := pullback.fst _ _
    rN := pullback.snd _ _
    hN := pullback.condition
    jA := retainedToDiagonal k p r α U
    jN := retainedToFixed k p r v α β h U
    p := pullback.fst _ _
    squareA := retainedToDiagonal_isPullback k p r α U
    squareN := retainedToFixed_isPullback k p r v α β h U
    g := pullback.snd _ _
    targetA := retainedToDiagonal_target k p r α U
    targetN := retainedToFixed_target k p r v α β h U
    base := pullback.condition
    A := pullbackLineBundle iA
      (dualLineBundle _ (tensorLineBundle _ T (actualDivisorLineBundle k p r)))
    B := pullbackLineBundle iA (dualLineBundle _ T)
    N := pullbackLineBundle iN (dualLineBundle _ N)
    M := pullbackLineBundle iN (dualLineBundle _ N)
    a := Hom.pullbackToUnit
      (sectionDualFunctional _ (tensorLineBundle _ T (actualDivisorLineBundle k p r)) a) iA
    b := Hom.pullbackToUnit (sectionDualFunctional _ T b) iA
    n := Hom.pullbackToUnit (sectionDualFunctional _ N n) iN
    d := Hom.pullbackToUnit (sectionDualFunctional _ N d) iN
    diagonal := commonRetainedGraph k p r α U φ hφ
    diagonal_closed := hclosed
    diagonal_source := commonRetainedGraph_fst k p r α U φ hφ
    diagonal_target := commonRetainedGraph_snd k p r α U φ hφ
    diagonal_line := commonRetainedGraph_locallyRankOne k p r α U φ hφ
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
    lineIso := retainedPencilLineIso k p r v α β h U φ hφ T N
    pole_finite := hpole.1
    pole_flat := hpole.2
    family_finite := hfamily.1
    family_flat := hfamily.2
  }
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
