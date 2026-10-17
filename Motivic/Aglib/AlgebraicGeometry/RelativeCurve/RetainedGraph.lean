module
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.GraphBoundaryRestriction
/-! # The original graph ideal of a smooth open in any separated relative curve -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable {S C Y : Scheme.{u}} (q : C ⟶ S) (j : Y ⟶ C)

def retainedGraphProductMap : pullback (j ≫ q) (j ≫ q) ⟶ pullback (j ≫ q) q :=
  (IsPullback.of_hasPullback (j ≫ q) q).flip.lift
    (pullback.snd _ _ ≫ j) (pullback.fst _ _)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := j ≫ q) (g := j ≫ q)).symm)

@[reassoc (attr := simp)]
lemma retainedGraphProductMap_fst :
    retainedGraphProductMap q j ≫ pullback.fst (j ≫ q) q = pullback.fst _ _ :=
  (IsPullback.of_hasPullback _ _).flip.lift_snd _ _ _
@[reassoc (attr := simp)]
lemma retainedGraphProductMap_snd :
    retainedGraphProductMap q j ≫ pullback.snd (j ≫ q) q = pullback.snd _ _ ≫ j :=
  (IsPullback.of_hasPullback _ _).flip.lift_fst _ _ _

lemma retainedGraphProductMap_isPullback :
    IsPullback (pullback.snd (j ≫ q) (j ≫ q)) (retainedGraphProductMap q j)
      j (pullback.snd (j ≫ q) q) :=
  (IsPullback.of_hasPullback (j ≫ q) (j ≫ q)).flip.of_bot'
    (IsPullback.of_hasPullback (j ≫ q) q).flip

instance [IsOpenImmersion j] : IsOpenImmersion (retainedGraphProductMap q j) :=
  MorphismProperty.of_isPullback (retainedGraphProductMap_isPullback q j) inferInstance

lemma compactificationGraph_mem_retained :
    Set.range (compactificationGraph q j) ⊆ Set.range (retainedGraphProductMap q j) := by
  have h : pullback.diagonal (j ≫ q) ≫ retainedGraphProductMap q j =
      compactificationGraph q j := by
    apply pullback.hom_ext <;> simp [compactificationGraph]
  rintro x ⟨y, rfl⟩
  exact ⟨(pullback.diagonal (j ≫ q)) y, congrArg (fun f => f y) h⟩

lemma retainedGraphProduct_smooth [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)] :
    SmoothOfRelativeDimension 1 ((retainedGraphProductMap q j).opensRange.ι ≫
      pullback.fst (j ≫ q) q) := by
  rw [← (retainedGraphProductMap q j).isoOpensRange_inv_comp, Category.assoc,
    retainedGraphProductMap_fst]
  have : SmoothOfRelativeDimension 1 (pullback.fst (j ≫ q) (j ≫ q)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- The ideal stays literal; smoothness is required only of the retained open. -/
def relativeCompactificationGraphLine [IsSeparated q] [IsOpenImmersion j]
    [SmoothOfRelativeDimension 1 (j ≫ q)] : LineBundle (pullback (j ≫ q) q) := by
  have := retainedGraphProduct_smooth q j
  exact ⟨idealModule (compactificationGraph q j),
    graph_idealModule_isLocallyRankOne j q (retainedGraphProductMap q j).opensRange
      (compactificationGraph_mem_retained q j)⟩
end AlgebraicGeometry.Scheme.Hom
