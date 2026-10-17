/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.AbelianSquareDescent
public import Motivic.Cohomology.SheafCohomologyH1Descent

/-!
# A square criterion for the vanishing of an ordinary H1 boundary

On a square with vertices `B, A, Y, X`, surjectivity of the coefficient
difference map `F(A) × F(Y) → F(B)` corrects local quotient lifts. Actual
square gluing for the middle and quotient sheaves gives a global lift and
kills the original extension-class boundary.

The geometric square gluing statements are explicit inputs. No derived
Mayer-Vietoris construction, cover acyclicity or homotopy invariance is
assumed. Coefficient and Ext universes are independent.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w t v u

namespace Motivic.SheafCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- A surjective coefficient difference map on a genuine gluing square kills
the boundary of any quotient section which lifts on its two covering vertices. -/
theorem boundary_eq_zero_of_square_difference_surjective
    {E : ShortComplex (Sheaf J AddCommGrpCat.{max v t})} (hE : E.ShortExact)
    (sq : Square C)
    (h₂ : (sq.op.map (E.X₂.obj ⋙ forget AddCommGrpCat.{max v t})).IsPullback)
    (h₃ : (sq.op.map (E.X₃.obj ⋙ forget AddCommGrpCat.{max v t})).IsPullback)
    (hsurj : Function.Surjective (fun a :
        E.X₁.obj.obj (op sq.X₂) × E.X₁.obj.obj (op sq.X₃) =>
      E.X₁.obj.map sq.f₁₂.op a.1 - E.X₁.obj.map sq.f₁₃.op a.2))
    (y : H J E.X₃ 0 sq.X₄)
    (lA : E.X₂.obj.obj (op sq.X₂)) (lY : E.X₂.obj.obj (op sq.X₃))
    (hA : E.g.hom.app (op sq.X₂) lA =
      E.X₃.obj.map sq.f₂₄.op (zeroSections J E.X₃ sq.X₄ y))
    (hY : E.g.hom.app (op sq.X₃) lY =
      E.X₃.obj.map sq.f₃₄.op (zeroSections J E.X₃ sq.X₄ y)) :
    y.comp hE.extClass rfl = 0 := by
  obtain ⟨l, hl⟩ := Sheaf.exists_section_lift_of_square_difference_surjective J hE
    sq h₂ h₃ hsurj (zeroSections J E.X₃ sq.X₄ y) lA lY hA hY
  have h := boundary_restriction_eq_zero_of_imageSieve J hE y (𝟙 sq.X₄)
    ⟨l, by simpa using hl⟩
  simpa using h

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max v t})]

/-- For the actual ordinary-injective presentation, a surjective square
difference map kills a represented H1 class with the displayed local lifts. -/
theorem h_one_eq_zero_of_square_difference_surjective
    (F : Sheaf J AddCommGrpCat.{max v t}) (sq : Square C)
    (hI : (sq.op.map ((Injective.under F).obj ⋙
      forget AddCommGrpCat.{max v t})).IsPullback)
    (hQ : (sq.op.map ((cokernel (Injective.ι F)).obj ⋙
      forget AddCommGrpCat.{max v t})).IsPullback)
    (hsurj : Function.Surjective (fun a : F.obj.obj (op sq.X₂) × F.obj.obj (op sq.X₃) =>
      F.obj.map sq.f₁₂.op a.1 - F.obj.map sq.f₁₃.op a.2))
    (x : H J F 1 sq.X₄) (s : (cokernel (Injective.ι F)).obj.obj (op sq.X₄))
    (hs : injectiveSectionBoundary J F sq.X₄ s = x)
    (lA : (Injective.under F).obj.obj (op sq.X₂))
    (lY : (Injective.under F).obj.obj (op sq.X₃))
    (hA : (cokernel.π (Injective.ι F)).hom.app (op sq.X₂) lA =
      (cokernel (Injective.ι F)).obj.map sq.f₂₄.op s)
    (hY : (cokernel.π (Injective.ι F)).hom.app (op sq.X₃) lY =
      (cokernel (Injective.ι F)).obj.map sq.f₃₄.op s) :
    x = 0 := by
  rw [← hs, injectiveSectionBoundary_apply]
  apply boundary_eq_zero_of_square_difference_surjective J
    (injectivePresentation_shortExact J F) sq hI hQ hsurj _ lA lY
  · change (cokernel.π (Injective.ι F)).hom.app (op sq.X₂) lA =
      (cokernel (Injective.ι F)).obj.map sq.f₂₄.op
        ((zeroSections.{w, t, v, u} J (cokernel (Injective.ι F)) sq.X₄)
          ((zeroSections.{w, t, v, u} J (cokernel (Injective.ι F)) sq.X₄).symm s))
    rw [AddEquiv.apply_symm_apply]
    exact hA
  · change (cokernel.π (Injective.ι F)).hom.app (op sq.X₃) lY =
      (cokernel (Injective.ι F)).obj.map sq.f₃₄.op
        ((zeroSections.{w, t, v, u} J (cokernel (Injective.ι F)) sq.X₄)
          ((zeroSections.{w, t, v, u} J (cokernel (Injective.ι F)) sq.X₄).symm s))
    rw [AddEquiv.apply_symm_apply]
    exact hY

end Motivic.SheafCohomology
