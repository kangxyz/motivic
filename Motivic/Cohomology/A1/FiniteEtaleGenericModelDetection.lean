/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.PresheafGenericModelDetection
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleNisnevich

/-! # Generic-model vanishing on the actual small Nisnevich site

The same original affine zero neighborhoods are actual small étale objects.
Their literal pointwise covering family kills the ordinary sheafification of
the restricted original presheaf. No big-to-small sheafification exchange is
assumed, and the restriction functor is the existing `toSmoothSite`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

variable {k : Type u} [Field k] [Infinite k]

/-- The original zero restrictions form a covering sieve on each actual small
étale object. Affine zero neighborhoods are viewed over the unchanged base. -/
theorem zeroSieve_mem_of_genericModelGerm_eq_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hG : ∀ (T : SmoothSite (Spec (.of k))) [IsAffine T.left] [IsIntegral T.left]
      (s : PresheafWithTransfers.genericModelGerm.{0, u} P T), s = 0)
    (X : SmoothSite (Spec (.of k))) (T : FiniteEtaleSite X.left)
    (s : ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj P).obj (op T)) :
    Presheaf.equalizerSieve s 0 ∈ nisnevichTopology X.left T := by
  choose O hx hO using fun x =>
    P.exists_zero_neighborhood_of_genericModelGerm_eq_zero hP hG ((toSmoothSite X).obj T) s x
  have : IsNoetherian T.left :=
    inferInstanceAs (IsNoetherian ((toSmoothSite X).obj T).left)
  let (x : T.left) : IsAffine (O x).toScheme := (hO x).1
  let U (x : T.left) : FiniteEtaleSite X.left :=
    MorphismProperty.Over.mk ⊤ ((O x).ι ≫ T.hom)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  let f (x : T.left) : U x ⟶ T := MorphismProperty.Over.homMk (O x).ι rfl
  let (x : T.left) : IsOpenImmersion (f x).left :=
    inferInstanceAs (IsOpenImmersion (O x).ι)
  apply Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mpr
  refine ⟨Presieve.ofArrows U f, ?_, ?_⟩
  · apply (ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    exact ⟨fun _ => inferInstance, fun x => ⟨x, ⟨x, hx x⟩, rfl, inferInstance⟩⟩
  · rw [Presieve.ofArrows_le_iff]
    intro x
    let A := SmoothSite.mk ((O x).ι ≫ (T.hom ≫ X.hom))
    let a : A ⟶ (toSmoothSite X).obj T := SmoothSite.homMk (O x).ι rfl
    let e : (toSmoothSite X).obj (U x) ⟶ A :=
      SmoothSite.homMk (𝟙 _) (by simp [A, U, toSmoothSite, Category.assoc])
    have he : e ≫ a = (toSmoothSite X).map (f x) := by
      apply MorphismProperty.Over.Hom.ext
      exact Category.id_comp _
    change P.transfer ((Cor.graphFunctor k).map ((toSmoothSite X).map (f x))) s =
      P.transfer ((Cor.graphFunctor k).map ((toSmoothSite X).map (f x))) 0
    rw [map_zero, ← he, Functor.map_comp, PresheafWithTransfers.transfer_comp]
    have hz : P.transfer ((Cor.graphFunctor k).map a) s = 0 := (hO x).2
    rw [ConcreteCategory.comp_apply, hz, map_zero]

/-- The literal small-site sheafification of the restricted original HI presheaf
is zero. This is a separate local-cover proof, not a sheafification comparison. -/
theorem isZero_sheafify_of_genericModelGerm_eq_zero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hG : ∀ (T : SmoothSite (Spec (.of k))) [IsAffine T.left] [IsIntegral T.left]
      (s : PresheafWithTransfers.genericModelGerm.{0, u} P T), s = 0)
    (X : SmoothSite (Spec (.of k))) :
    IsZero ((presheafToSheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}).obj
      ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj P)) :=
  Presheaf.isZero_sheafify_of_locally_zero _ _
    (zeroSieve_mem_of_genericModelGerm_eq_zero P hP hG X)

end Motivic.FiniteEtaleSite
