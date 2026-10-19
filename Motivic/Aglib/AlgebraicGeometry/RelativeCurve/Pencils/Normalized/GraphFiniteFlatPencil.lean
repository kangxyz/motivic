module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Normalized.Retained.PencilFiniteFlat
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
theorem exists_actualGraphFiniteFlatPencil
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
    (φ : X ⟶ pullback U.ι p)
    (hφ : φ ≫ retainedInclusion k p U = α ≫ r ≫ inclusion k p) [Flat α]
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
      retainedGraphFamilyFiniteFlat k p r v α β h U φ hφ T N a b n d ∧
      retainedPoleFiniteFlat k p r v α β h U T N b d := by
  obtain ⟨degree, a, b, n, d, hIa, hIb, hIn, hId, hFa, hFb, hFn, hFd, hT, hf, hp⟩ :=
    exists_actualCommonFiniteFlatPencil k p r v α β h B z hd s hs H U H0 hz
  let T := diagonalTwistBundle k p r degree
  let N := fixedTwistBundle k p v degree
  have hf' := retainedGraphFamily_finite_flat k p r v α β h U φ hφ T N a b n d hf
  have hp' := retainedPole_finite_flat k p r v α β h U T N b d hp
  exact ⟨degree, a, b, n, d, hIa, hIb, hIn, hId, hFa, hFb, hFn, hFd, hT, hf', hp'⟩
end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
