/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.RelativeMonicZeroSquare
public import Motivic.Cohomology.Sheaf.AllGenericOpen
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.Ordinary.OpenBaseRefinement
public import Motivic.Cohomology.Sheaf.NisnevichSquareRefinement
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Open.RelativeOpenImmersionOverlapShrinking
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientComplement

/-! # Higher ordinary relative-line classes vanish after only a base shrinking -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe w u
namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.CategoryTheory.Sheaf.LargeCohomology
open _root_.Algebra.Smooth _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The final shrinking is an actual open of the original base. -/
abbrev relativeLineBaseOpen (r : R) : (lineSite (k := k) (R := R)).left.Opens :=
  polynomialProjection (.of R) ⁻¹ᵁ PrimeSpectrum.basicOpen r

/-- Given a constructed monic zero square, the higher class vanishes over a
nonzero principal base open. Only the actual generic fiber has curve dimension. -/
theorem exists_relativeLine_base_open_restriction_eq_zero_of_zero_square
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (n : ℕ) (g : R[X]) (hg : g.Monic)
    {Y : SmoothSite (Spec (.of k))}
    (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
    [IsIso (pullback.snd p.left (inclusion g))]
    (e : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 2) (lineSite (k := k) (R := R)))
    (hU : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 2)).map (openInclusion g).op e = 0)
    (hY : (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F (n + 2)).map p.op e = 0) :
    ∃ r : R, r ≠ 0 ∧
      (presheaf.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        F (n + 2)).map
          (SmoothSite.openInclusion (lineSite (k := k) (R := R))
            (relativeLineBaseOpen r)).op e = 0 := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let L := lineSite (k := k) (R := R)
  let j := openInclusion (k := k) g
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (principalOpen g).ι)
  let W := pullback j p
  let i : W ⟶ Y := pullback.snd j p
  let sq := ordinaryPullbackSquare j p
  have hpb : sq.IsPullback := IsPullback.of_hasPullback _ _
  have hcomp : Set.range (inclusion g) = (Set.range j.left)ᶜ := by
    change Set.range (inclusion g) = (Set.range (principalOpen g).ι)ᶜ
    rw [range_inclusion_complement, Scheme.Opens.range_ι]
  obtain ⟨q, f, hq, hf⟩ := exists_nisnevich_overlap_boundary_lift.{w, u + 1, u}
    sq hpb (inclusion g) hcomp F (n + 1) e hU hY
  have hpbScheme : IsPullback (pullback.fst j p).left (pullback.snd j p).left j.left p.left :=
    (SmoothSite.forgetScheme _).map_isPullback hpb
  let : IsOpenImmersion i.left := MorphismProperty.of_isPullback hpbScheme inferInstance
  obtain ⟨O, hO, hfO⟩ := exists_all_generic_open_restriction_eq_zero F n W f
  let z := pullback.fst p.left (inclusion g)
  have hzfin : IsFinite (z ≫ p.left ≫ polynomialProjection (.of R)) := by
    have he : z ≫ p.left ≫ polynomialProjection (.of R) =
        pullback.snd p.left (inclusion g) ≫ source g := by
      rw [← Category.assoc, pullback.condition, Category.assoc, inclusion_projection]
    rw [he]
    let : IsFinite (source g) := source_finite g hg
    infer_instance
  let : IsFinite (z ≫ p.left ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))) := hzfin
  have hdisj : Disjoint (Set.range z) (Set.range i.left) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨a, rfl⟩ ⟨b, hb⟩
    have ha : p.left (z a) ∈ Set.range (inclusion g) := by
      refine ⟨pullback.snd p.left (inclusion g) a, ?_⟩
      exact (congrArg (fun h => h a) (pullback.condition (f := p.left) (g := inclusion g))).symm
    rw [hcomp] at ha
    apply ha
    refine ⟨(pullback.fst j p).left b, ?_⟩
    exact (congrArg (fun h : W ⟶ L => h.left b) (pullback.condition (f := j) (g := p))).trans
      (congrArg p.left hb)
  obtain ⟨r, hr, T, hretain, hsmall⟩ :=
    Scheme.exists_base_principal_openImmersion_overlap_shrinking R p.left i.left O hO z hdisj
  let C := relativeLineBaseOpen (k := k) r
  have hkeep : ∀ y : Y.left, p.left y ∈ Set.range (inclusion g) → p.left y ∈ C → y ∈ T := by
    intro y hy hC
    obtain ⟨a, ha⟩ := (Scheme.Pullback.range_fst p.left (inclusion g)).ge hy
    rw [← ha]
    apply hretain a
    change polynomialProjection (.of R) (p.left (z a)) ∈ PrimeSpectrum.basicOpen r
    change polynomialProjection (.of R) (p.left y) ∈ PrimeSpectrum.basicOpen r at hC
    have ha' : z a = y := ha
    rw [ha']
    exact hC
  let sq' := ordinaryOpenBaseSquare j p C T
  let d := ordinaryOpenBaseSquareMap j p C T
  let : IsIso (pullback.snd sq'.f₃₄.left (inclusion g ∣_ C)) :=
    ordinaryOpenBaseSquare_iso_complement j p C T (inclusion g) hkeep
  have hcomp' := ordinaryOpenBaseSquare_complement j p C T (inclusion g) hcomp
  have hfactor : Set.range d.τ₁.left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    rintro y ⟨a, rfl⟩
    apply hsmall
    change i.left (d.τ₁.left a) ∈ T
    have hc := congrArg (fun h => h.left a) d.comm₁₃
    change d.τ₃.left (sq'.f₁₃.left a) = i.left (d.τ₁.left a) at hc
    rw [← hc]
    exact (sq'.f₁₃.left a).property.2
  let v₀ := IsOpenImmersion.lift O.ι d.τ₁.left hfactor
  have hv₀ : v₀ ≫ O.ι = d.τ₁.left := IsOpenImmersion.lift_fac _ _ _
  let v : sq'.X₁ ⟶ (SmoothSite.opensFunctor W).obj O := SmoothSite.homMk v₀ (by
    change v₀ ≫ (O.ι ≫ W.hom) = _
    rw [← Category.assoc, hv₀, MorphismProperty.Over.w])
  have hv : v ≫ SmoothSite.openInclusion W O = d.τ₁ := by
    apply MorphismProperty.Over.Hom.ext
    exact hv₀
  have hf' : (presheaf _ F (n + 1)).map d.τ₁.op f = 0 := by
    rw [← hv, op_comp, Functor.map_comp_apply, hfO, map_zero]
  let : Mono j := (SmoothSite.forgetScheme _).mono_of_mono_map (by
    change Mono j.left
    infer_instance)
  let : Mono sq.f₁₃ := hpb.mono_snd_of_mono
  refine ⟨r, hr, ?_⟩
  exact ordinary_restriction_eq_zero_of_square_refinement.{w, u + 1, u}
    d (IsPullback.of_hasPullback _ _) (inclusion g ∣_ C) hcomp' F (n + 1) e q f hq hf hf'

end Motivic.SheafCohomology
