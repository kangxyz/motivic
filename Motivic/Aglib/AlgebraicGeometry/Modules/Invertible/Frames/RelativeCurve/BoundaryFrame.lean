module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleBoundaryIdeal
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteBaseNeighborhood
/-! # Actual boundary graph frames for arbitrary smooth relative curves

The frame is constructed near the original source point on the whole finite boundary.
There is no polynomial-coordinate, reduced-boundary, or smooth compactification hypothesis.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S X Z : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (z : Z ⟶ X)

omit [SmoothOfRelativeDimension 1 q] in
/-- The original full-boundary graph is a closed section of the smooth curve over Z. -/
lemma relativeBoundaryGraph_closed : IsClosedImmersion (boundaryGraphTarget q z) := by
  have h : boundaryGraphTarget q z =
      pullback.lift (𝟙 Z) z (Category.id_comp (z ≫ q)) ≫
        (pullbackSymmetry (z ≫ q) q).hom := by
    apply pullback.hom_ext <;> simp [boundaryGraphTarget]
  rw [h]
  infer_instance

/-- The actual ideal, with no replacement by a line-bundle class. -/
def relativeBoundaryGraphLine : LineBundle (pullback q (z ≫ q)) := by
  have := relativeBoundaryGraph_closed q z
  have : SmoothOfRelativeDimension 1 (pullback.snd q (z ≫ q)) :=
    MorphismProperty.pullback_snd q (z ≫ q) inferInstance
  have : SmoothOfRelativeDimension 1
      ((⊤ : (pullback q (z ≫ q)).Opens).ι ≫ pullback.snd q (z ≫ q)) :=
    smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
  exact ⟨idealModule (boundaryGraphTarget q z),
    section_idealModule_isLocallyRankOne (pullback.snd q (z ≫ q))
      (boundaryGraphTarget q z) (by simp [boundaryGraphTarget]) ⊤ (by simp)⟩

/-- Finiteness of the whole boundary constructs a frame over one source neighborhood. -/
theorem exists_relativeBoundaryFrame [IsFinite (z ≫ q)] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((idealModule (boundaryGraphTarget q z)).restrict
        ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
          SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  exists_base_open_unitIso_of_isFinite (pullback.fst q (z ≫ q)) x
    (relativeBoundaryGraphLine q z)

/-- One genuine frame works above every point of a specified finite source set. -/
theorem exists_relativeBoundaryFrame_around_finite [IsAffine X] [IsFinite (z ≫ q)]
    (points : Set X) (hpoints : points.Finite) :
    ∃ U : X.Opens, points ⊆ U ∧
      Nonempty ((idealModule (boundaryGraphTarget q z)).restrict
        ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
          SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  let f := pullback.fst q (z ≫ q)
  have : IsFinite f := inferInstanceAs (IsFinite (pullback.fst q (z ≫ q)))
  have : IsAffine (pullback q (z ≫ q)) := isAffine_of_isAffineHom f
  have ht : (f ⁻¹' points).Finite := by
    convert hpoints.biUnion (fun x _ => f.finite_preimage_singleton x) using 1
    ext x
    simp
  obtain ⟨V, hV, ⟨e⟩⟩ := exists_open_unitIso_around_finite _
    (relativeBoundaryGraphLine q z) (f ⁻¹' points) ht
  let U : X.Opens := ⟨(f '' (V : Set _)ᶜ)ᶜ,
    (f.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hUV : f ⁻¹ᵁ U ≤ V := by
    intro x hx
    change f x ∉ f '' (V : Set _)ᶜ at hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩
  refine ⟨U, ?_, ⟨restrictUnitIsoOfLE (relativeBoundaryGraphLine q z).val hUV e⟩⟩
  rintro x hx ⟨y, hy, rfl⟩
  exact hy (hV hx)

end AlgebraicGeometry.Scheme.Hom
