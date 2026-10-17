module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualCommonPencilFiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ActualCommonPoleDivisor
/-! # Constructed correcting pencil with its whole finite flat zero family -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

/-- Original affine lambda and unchanged affine-U sources produce four genuine sections,
whole regular finite-flat factor zeros, and the literal common-boundary pencil equation.
Neither sections nor the boundary equality are hypotheses. -/
theorem exists_actualCommonFiniteFlatPencil
    (k : Type u) [Field k] {Y X : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    {R Q : Type u} [CommRing R] [IsNoetherianRing R] [CommRing Q] [IsNoetherianRing Q]
    (r : Spec (.of R) ⟶ Y) [IsOpenImmersion r]
    (v : Spec (.of Q) ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion v]
    (α : X ⟶ Spec (.of R)) (β : X ⟶ Spec (.of Q)) (h : α ≫ r ≫ p = β ≫ v)
    (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    [IsClosedImmersion (Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)]
    (hd : Disjoint (Set.range v) (Set.range (Hom.boundaryCoordinateMap k B z)))
    (s : Spec (.of B) ⟶ Spec (.of R))
    (hs : s ≫ r ≫ p = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) (r ≫ p) (Hom.boundaryCoordinateMap k B z))
    (U : (Spec (.of (Polynomial k))).Opens)
    (H0 : IsPullback (s ≫ r) (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    ∃ degree : ℕ,
    let T := diagonalTwistBundle k p r degree
    let N := fixedTwistBundle k p v degree
    let M := actualDivisorLineBundle k p r
    let zA := diagonalBoundaryMap k p r s
    let zN := fixedBoundaryMap k p v B z (s ≫ r) (by simpa only [Category.assoc] using hs)
    let f := commonBoundaryToDiagonal k p r α B s ≫ zA
    let g := commonBoundaryToFixed k p r v α β h B z s hs ≫ zN
    ∃ a : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶
      (tensorLineBundle _ T M).val,
    ∃ b : SheafOfModules.unit (diagonalAmbient k p r).ringCatSheaf ⟶ T.val,
    ∃ n d : SheafOfModules.unit (fixedAmbient k p v).ringCatSheaf ⟶ N.val,
      IsIso (pullbackSectionMap zA a) ∧ IsIso (pullbackSectionMap zA b) ∧
      IsIso (pullbackSectionMap zN n) ∧ IsIso (pullbackSectionMap zN d) ∧
      RetainedSectionFiniteFlat k p r U (tensorLineBundle _ T M) a ∧
      RetainedSectionFiniteFlat k p r U T b ∧
      FixedRetainedSectionFiniteFlat k p v U N n ∧
      FixedRetainedSectionFiniteFlat k p v U N d ∧
      tensorSectionMap _ (pullbackSectionMap f a) (pullbackSectionMap g n) =
        tensorSectionMap _
          (pullbackSectionMap f (twistedIdealSection _ (actualIdealLineBundle k p r) T
            (Hom.idealInclusion
              (Hom.compactificationGraph (projection k p) (r ≫ inclusion k p))) b))
          (pullbackSectionMap g d) ∧
      (let qX := commonSourceProjection k p r α
       let j := constantRetainedInclusion k p U qX
       let qD := pullback.fst qX (retainedProjection k p U)
       let f := PolynomialBoundaryPencil.familyMap (qD ≫ qX)
         (pullbackLineBundle j (commonPencilBundle k p r v α β h T N))
         (Hom.pullbackToUnit (commonPencilStart k p r v α β h T N b d) j)
         (Hom.pullbackToUnit (commonPencilEnd k p r v α β h T N a n) j)
       IsFinite (Hom.zeroInclusion f ≫ PolynomialBoundaryPencil.parameterMap qX qD) ∧
         Flat (Hom.zeroInclusion f ≫ PolynomialBoundaryPencil.parameterMap qX qD)) ∧
      (let j := constantRetainedInclusion k p U (commonSourceProjection k p r α)
       let qD := pullback.fst (commonSourceProjection k p r α) (retainedProjection k p U)
       let pole := Hom.pullbackToUnit
         (mixedProductFunctional (commonToDiagonal k p r α)
           (commonToFixed k p r v α β h) T N b d) j
       IsFinite (Hom.zeroInclusion pole ≫ qD) ∧ Mono pole ∧
         Flat (Hom.zeroInclusion pole ≫ qD)) := by
  obtain ⟨degree, a, b, n, d, hIa, hIb, hIn, hId, hFa, hFb, hFn, hFd, hT⟩ :=
    exists_actualCommonSectionBoundary k p r v α β h B z hd s hs H U H0 hz
  let T := diagonalTwistBundle k p r degree
  let N := fixedTwistBundle k p v degree
  have := hIa
  have := hIn
  have := hIb
  have := hId
  refine ⟨degree, a, b, n, d, hIa, hIb, hIn, hId, hFa, hFb, hFn, hFd, hT, ?_⟩
  constructor
  · exact commonPencil_finite_flat k p r v α β h T N B z s hs U H0 hz a b n d
      (commonPencil_boundary k p r v α β h T N B z s hs a b n d hT)
  · exact commonPole_finite_mono_flat k p r v α β h T N B z s hs U H0 hz b d
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
