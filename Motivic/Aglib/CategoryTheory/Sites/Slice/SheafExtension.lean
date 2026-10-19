module

public import Motivic.Aglib.CategoryTheory.Sites.Slice.PresheafExtension
public import Mathlib.CategoryTheory.Sites.Pullback

/-! Exact extension for ordinary abelian sheaves from a slice site. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

universe v u w z
namespace CategoryTheory.SliceSheaf
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (X : C)
  (A : Type z) [Category.{w} A] [HasCoproducts.{v} A]
  [HasSheafify J A] [HasSheafify (J.over X) A]

/-- Sheafification of the actual sum over structure morphisms. -/
def extension : Sheaf (J.over X) A ⥤ Sheaf J A :=
  sheafToPresheaf (J.over X) A ⋙ SlicePresheaf.extension X ⋙ presheafToSheaf J A

/-- The sum extension is left adjoint to the original restriction functor. -/
def adjunction : extension J X A ⊣ (Over.forget X).sheafPushforwardContinuous A (J.over X) J :=
  ((SlicePresheaf.adjunction X).comp (sheafificationAdjunction J A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (J.over X) A) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

instance : (extension J X A).IsLeftAdjoint := (adjunction J X A).isLeftAdjoint

instance [HasFiniteLimits A] [AB4OfSize.{v} A] :
    PreservesFiniteLimits (extension J X A) := by
  unfold extension
  infer_instance

/-- Identification with the native continuous-site left adjoint. -/
def nativeExtensionIso
    [((Over.forget X).sheafPushforwardContinuous A (J.over X) J).IsRightAdjoint] :
    (Over.forget X).sheafPullback A (J.over X) J ≅ extension J X A :=
  ((Over.forget X).sheafAdjunctionContinuous A (J.over X) J).leftAdjointUniq
    (adjunction J X A)

/-- The native slice extension is exact on additive coefficients with exact coproducts,
although the underlying forgetful site functor does not preserve terminal objects. -/
instance [HasFiniteLimits A] [AB4OfSize.{v} A]
    [((Over.forget X).sheafPushforwardContinuous A (J.over X) J).IsRightAdjoint] :
    PreservesFiniteLimits ((Over.forget X).sheafPullback A (J.over X) J) :=
  preservesFiniteLimits_of_natIso (nativeExtensionIso J X A).symm

end CategoryTheory.SliceSheaf
