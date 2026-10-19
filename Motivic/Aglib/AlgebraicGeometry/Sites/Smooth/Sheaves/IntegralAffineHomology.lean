module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso
public import Motivic.Aglib.Algebra.Homology.Sheafification.Singular
public import Motivic.Aglib.CategoryTheory.SheafifyAdditive
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Abelian

/-! # Detecting zero homology sheaves on integral affine smooth objects -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- A presheaf vanishing on integral affine sources has zero ordinary Nisnevich sheafification. -/
theorem isZero_sheafify_of_integral_affine
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      IsZero (F.obj (op X))) :
    IsZero ((presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj F) := by
  let J := nisnevichTopology (Spec (.of k))
  let z : F ⟶ 0 := 0
  have hi : Presheaf.IsLocallyInjective J z := by
    constructor
    intro X x y _
    apply sieve_mem_of_integral_affine_arrows k
    intro U _ _ f
    have := AddCommGrpCat.subsingleton_of_isZero (h U)
    exact Subsingleton.elim _ _
  have hs : Presheaf.IsLocallySurjective J z := by
    constructor
    intro X x
    apply sieve_mem_of_integral_affine_arrows k
    intro U _ _ f
    have hz : IsZero ((0 : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤
        AddCommGrpCat.{u + 1}).obj (op U)) :=
      ((_root_.CategoryTheory.evaluation _ _).obj (op U)).map_isZero (isZero_zero _)
    have := AddCommGrpCat.subsingleton_of_isZero hz
    exact ⟨0, Subsingleton.elim _ _⟩
  have hz : IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map z) :=
    (J.W_iff z).mp (J.W_of_isLocallyBijective z)
  exact ((presheafToSheaf J AddCommGrpCat.{u + 1}).map_isZero (isZero_zero _)).of_iso
    (asIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map z))

/-- Vanishing of evaluated homology on integral affines implies vanishing of
ordinary homology sheaves, in every chain degree. -/
theorem isZero_sheafified_homology_of_integral_affine
    (K : ChainComplex ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ)
    (n : ℕ)
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      IsZero ((K.homology n).obj (op X))) :
    IsZero ((Sheafification.obj (nisnevichTopology (Spec (.of k))) K).homology n) :=
  (isZero_sheafify_of_integral_affine k (K.homology n) h).of_iso
    (Sheafification.homologyIso (nisnevichTopology (Spec (.of k))) K n)

end AlgebraicGeometry.Scheme.SmoothSite
