/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyAllGenericOpen
public import Motivic.Cohomology.SheafCohomologyNisnevichOverlapShrink
public import Motivic.Aglib.AlgebraicGeometry.OpenImmersionCurveShrinking
public import Motivic.Aglib.AlgebraicGeometry.OpenFiberShrinking
public import Motivic.Aglib.AlgebraicGeometry.EtaleCurveDimension
public import Motivic.Aglib.AlgebraicGeometry.AffineLineReducedComplement

/-! # Killing positive overlap classes while retaining the original Nisnevich complement -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
namespace Motivic.SheafCohomology
open AffineLineReducedComplement
variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local instance (U : (line k).Opens) : IsOpenImmersion (openInclusion U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- The refined étale leg is constructed by deleting the finite closed support
of an actual positive overlap class. No higher-cohomology sheaf condition is used. -/
theorem exists_affineLine_overlap_refinement_zero
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (U : (line k).Opens) {V : SmoothSite (Spec (.of k))}
    (p : V ⟶ SmoothSite.affineLine (.of k)) [Etale p.left]
    [IsIso (pullback.snd p.left (inclusion U))] (n : ℕ)
    (f : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 1) (pullback (openInclusion U) p)) :
    ∃ T : V.left.Opens,
      IsIso (pullback.snd ((SmoothSite.openInclusion V T) ≫ p).left (inclusion U)) ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (n + 1)).map (ordinaryOverlapMap (openInclusion U) p
          (SmoothSite.openInclusion V T)).op f = 0 := by
  let j := openInclusion U
  let W := pullback j p
  let i : W ⟶ V := pullback.snd j p
  let : IsOpenImmersion ((SmoothSite.forgetScheme _).map j) :=
    inferInstanceAs (IsOpenImmersion U.ι)
  let : JacobsonSpace (SmoothSite.affineLine (.of k)).left :=
    inferInstanceAs (JacobsonSpace (Spec (.of (Polynomial k))))
  have hpb := (SmoothSite.forgetScheme _).map_isPullback (IsPullback.of_hasPullback j p)
  let : IsOpenImmersion i.left := MorphismProperty.of_isPullback hpb inferInstance
  let : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace p.left
  obtain ⟨O, hO, hf⟩ := exists_all_generic_open_restriction_eq_zero F n W f
  have hdim : topologicalKrullDim W.left ≤ 1 :=
    Scheme.topologicalKrullDim_le_one_of_etale_affineLine (i.left ≫ p.left)
  obtain ⟨T, hT, hTO, _⟩ := Scheme.exists_open_shrinking_of_openImmersion i.left O hO hdim
  let r := SmoothSite.openInclusion V T
  have hretain : p.left ⁻¹' Set.range (inclusion U) ⊆ (T : Set V.left) := by
    intro v hv
    apply hT
    rintro ⟨w, rfl⟩
    rw [range_inclusion] at hv
    apply hv
    have hc := congrArg (fun a : W ⟶ SmoothSite.affineLine (.of k) => a.left w)
      (pullback.condition (f := j) (g := p))
    exact hc ▸ ((pullback.fst j p).left w).property
  have hiso : IsIso (pullback.snd (r ≫ p).left (inclusion U)) :=
    Scheme.Hom.isIso_pullback_snd_of_open_retains_fiber p.left (inclusion U) T hretain
  let a := ordinaryOverlapMap j p r
  have ha : Set.range a.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι, ← hTO]
    rintro _ ⟨x, rfl⟩
    have hc := congrArg (fun b => b.left x) (ordinaryOverlapMap_snd j p r)
    change i.left (a.left x) ∈ T
    rw [show i.left (a.left x) = r.left ((pullback.snd j (r ≫ p)).left x) from hc]
    exact ((pullback.snd j (r ≫ p)).left x).property
  let b₀ := IsOpenImmersion.lift O.ι a.left ha
  have hb₀ : b₀ ≫ O.ι = a.left := IsOpenImmersion.lift_fac _ _ _
  let b : pullback j (r ≫ p) ⟶ (SmoothSite.opensFunctor W).obj O :=
    SmoothSite.homMk b₀ (by
      change b₀ ≫ (O.ι ≫ W.hom) = _
      rw [← Category.assoc, hb₀, MorphismProperty.Over.w])
  have hb : b ≫ SmoothSite.openInclusion W O = a := by
    apply MorphismProperty.Over.Hom.ext
    exact hb₀
  refine ⟨T, hiso, ?_⟩
  change (presheaf _ F (n + 1)).map a.op f = 0
  rw [← hb, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hf, map_zero]

end Motivic.SheafCohomology
