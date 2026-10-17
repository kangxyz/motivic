module

public import Motivic.AlgebraicGeometry.SmoothSiteAffineSheafIso
public import Motivic.AlgebraicGeometry.SmoothSiteNormal
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! # Integral affine covers of the genuine smooth site -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.SmoothSite

variable (k : Type u) [Field k]

/-- The componentwise affine cover, with a nonempty chosen member at every point. -/
def integralAffineCover (X : SmoothSite (Spec (.of k))) : X.left.OpenCover := by
  let C := (componentOpenCover k X).bind fun i =>
    ((componentOpenCover k X).X i).affineCover
  exact {
    I₀ := X.left
    X x := C.X (Scheme.Cover.idx C x)
    f x := C.f (Scheme.Cover.idx C x)
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨x, Scheme.Cover.covers C x⟩, fun _ => inferInstance⟩ }

instance isAffine_integralAffineCover_obj (X : SmoothSite (Spec (.of k)))
    (i : (integralAffineCover k X).I₀) : IsAffine ((integralAffineCover k X).X i) := by
  dsimp [integralAffineCover]
  infer_instance

instance isIntegral_integralAffineCover_obj (X : SmoothSite (Spec (.of k)))
    (i : (integralAffineCover k X).I₀) : IsIntegral ((integralAffineCover k X).X i) := by
  let C := (componentOpenCover k X).bind fun j =>
    ((componentOpenCover k X).X j).affineCover
  have hn : Nonempty (C.X (Scheme.Cover.idx C i)) := by
    obtain ⟨x, _⟩ := Scheme.Cover.covers C i
    exact ⟨x⟩
  let : Nonempty (((componentOpenCover k X).X (Scheme.Cover.idx C i).1).affineCover.X
    (Scheme.Cover.idx C i).2) := hn
  change IsIntegral (((componentOpenCover k X).X (Scheme.Cover.idx C i).1).affineCover.X
    (Scheme.Cover.idx C i).2)
  apply isIntegral_of_isOpenImmersion
    (((componentOpenCover k X).X (Scheme.Cover.idx C i).1).affineCover.f (Scheme.Cover.idx C i).2)

/-- Integral affine sources suffice to generate a genuine Nisnevich covering sieve. -/
theorem sieve_mem_of_integral_affine_arrows (X : SmoothSite (Spec (.of k))) (T : Sieve X)
    (h : ∀ (U : SmoothSite (Spec (.of k))) [IsAffine U.left] [IsIntegral U.left]
      (f : U ⟶ X), T f) : T ∈ nisnevichTopology (Spec (.of k)) X := by
  let C := integralAffineCover k X
  let U (i : C.I₀) : SmoothSite (Spec (.of k)) := mk (C.f i ≫ X.hom)
  let f (i : C.I₀) : U i ⟶ X := homMk (C.f i) rfl
  apply (mem_nisnevichTopology_iff).mpr
  refine ⟨Presieve.ofArrows U f, ?_, ?_⟩
  · change (Presieve.ofArrows U f).map (forgetScheme _) ∈ Nisnevich.precoverage X.left
    rw [Presieve.map_ofArrows]
    exact Nisnevich.zariskiPrecoverage_le_precoverage _ C.mem₀
  · rw [Presieve.ofArrows_le_iff]
    intro i
    let : IsAffine (U i).left := by dsimp [U, C]; infer_instance
    let : IsIntegral (U i).left := by dsimp [U, C]; infer_instance
    exact h (U i) (f i)

/-- Isomorphisms of genuine Nisnevich sheaves can be detected on integral affine sources. -/
theorem isIso_of_integral_affine_app
    {F G : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      IsIso (φ.hom.app (op X))) : IsIso φ := by
  have hi : Presheaf.IsLocallyInjective (nisnevichTopology (Spec (.of k))) φ.hom := by
    constructor
    intro X x y hxy
    apply sieve_mem_of_integral_affine_arrows k
    intro U _ _ f
    have := h U
    apply (ConcreteCategory.bijective_of_isIso (φ.hom.app (op U))).injective
    change φ.hom.app (op U) (F.obj.map f.op x) =
      φ.hom.app (op U) (F.obj.map f.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  have hs : Presheaf.IsLocallySurjective (nisnevichTopology (Spec (.of k))) φ.hom := by
    constructor
    intro X x
    apply sieve_mem_of_integral_affine_arrows k
    intro U _ _ f
    have := h U
    exact (ConcreteCategory.bijective_of_isIso (φ.hom.app (op U))).surjective
      (G.obj.map f.op x)
  exact (Sheaf.isLocallyBijective_iff_isIso φ).mp ⟨hi, hs⟩

/-- The genuine integral affine objects form a full subcategory of the smooth site. -/
def integralAffineProperty : ObjectProperty (SmoothSite (Spec (.of k))) :=
  fun X => IsAffine X.left ∧ IsIntegral X.left

/-- The inclusion of actual integral affine smooth schemes. -/
abbrev integralAffineInclusion := (integralAffineProperty k).ι

instance integralAffineInclusion_isCoverDense :
    (integralAffineInclusion k).IsCoverDense (nisnevichTopology (Spec (.of k))) where
  is_cover X := by
    apply sieve_mem_of_integral_affine_arrows k
    intro U _ _ f
    exact Presieve.in_coverByImage (integralAffineInclusion k)
      (Y := ⟨U, inferInstance, inferInstance⟩) f

/-- A natural map on genuine integral affine sources extends uniquely into an
ordinary Nisnevich sheaf, by the native dense-subsite gluing construction. -/
def extendIntegralAffineHom
    {F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    {G : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj) : F ⟶ G.obj :=
  Functor.IsCoverDense.sheafHom α

end Motivic.SmoothSite
