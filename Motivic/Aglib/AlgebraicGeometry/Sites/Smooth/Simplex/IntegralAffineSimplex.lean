module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Units.BoundaryOneComplex
public import Motivic.Aglib.AlgebraicGeometry.Simplex.ExteriorGeometry

/-! # Actual categorical simplex products preserve integral affine sources -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]

instance isAffine_categoricalSimplexProduct (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] (n : ℕ) :
    IsAffine (X ⨯ _root_.AlgebraicSimplex.smoothSiteObj k n).left := by
  let e := (forgetScheme (Spec (.of k))).mapIso
    (categoricalProductIso X (_root_.AlgebraicSimplex.smoothSiteObj k n))
  let p : X.left ⟶ Spec (.of k) := X.hom
  have h : IsAffine (product X (_root_.AlgebraicSimplex.smoothSiteObj k n)).left :=
    inferInstanceAs (IsAffine (pullback p (_root_.AlgebraicSimplex.structureMap k n)))
  exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom h

instance isIntegral_categoricalSimplexProduct (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (n : ℕ) :
    IsIntegral (X ⨯ _root_.AlgebraicSimplex.smoothSiteObj k n).left := by
  let e := (forgetScheme (Spec (.of k))).mapIso
    (categoricalProductIso X (_root_.AlgebraicSimplex.smoothSiteObj k n))
  let p : X.left ⟶ Spec (.of k) := X.hom
  have h : IsIntegral (product X (_root_.AlgebraicSimplex.smoothSiteObj k n)).left :=
    inferInstanceAs (IsIntegral (pullback p (_root_.AlgebraicSimplex.structureMap k n)))
  exact @IsIntegral.of_isIso _ _ h e.inv e.isIso_inv

end AlgebraicGeometry.Scheme.SmoothSite
