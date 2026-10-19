/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.FiniteField.CoefficientLocalZero
public import Motivic.Cohomology.A1.LocalVanishing.Affine.IntegralDetection
public import Motivic.Transfers.Presheaf.Sheafification.Image


/-! # Dense detection before homotopy invariance of sheafification

The actual image of the transfer-natural unit is HI and separated. Original
local-zero neighborhoods detect its sections, and local representatives then
detect sections of the actual Nisnevich sheafification. No HI assumption on
that sheafification, generic-field comparison, or boundary family is used.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- The actual finite and infinite geometric producers give local zero over every field. -/
theorem integralAffineLocalZero_of_field (k : Type u) [Field k] :
    IntegralAffineLocalZero k := by
  cases finite_or_infinite k
  · exact integralAffineLocalZero_of_finite k
  · intro X A _ _ _ a _ P hP v hv x
    exact exists_zero_neighborhood_of_integral_affine a P hP v hv x

/-- Dense restriction detects an original HI presheaf as soon as it is separated.
Only the uniqueness half of the Nisnevich sheaf condition is needed. -/
theorem section_eq_zero_of_dense_open_of_separated
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hsep : Presheaf.IsSeparated (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj P))
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (s : P.sections (Cor.mk X))
    (hs : P.transfer ((Cor.graphFunctor k).map a) s = 0) : s = 0 := by
  classical
  let Q := (toPresheaf k).obj P
  have hlocal := exists_zero_neighborhood_of_dense_open_of_integralAffineLocalZero
    (integralAffineLocalZero_of_field k) a ha P hP s hs
  choose O hO hx hz using hlocal
  let Y (x : X.left) := SmoothSite.mk ((O x).ι ≫ X.hom)
  let f (x : X.left) : Y x ⟶ X := SmoothSite.homMk (O x).ι rfl
  have hpre : Presieve.ofArrows Y f ∈
      SmoothSite.nisnevichPrecoverage (Spec (.of k)) X := by
    apply (SmoothSite.ofArrows_mem_nisnevichPrecoverage_iff f).mpr
    exact ⟨fun x => inferInstanceAs (Etale (O x).ι),
      fun x => ⟨x, ⟨x, hx x⟩, rfl,
        inferInstanceAs (IsIso ((O x).ι.residueFieldMap ⟨x, hx x⟩))⟩⟩
  have hcover : Presheaf.equalizerSieve (F := Q) s 0 ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) X := by
    apply SmoothSite.mem_nisnevichTopology_iff.mpr
    refine ⟨Presieve.ofArrows Y f, hpre, ?_⟩
    rw [Presieve.ofArrows_le_iff]
    intro x
    change P.transfer ((Cor.graphFunctor k).map (f x)) s =
      P.transfer ((Cor.graphFunctor k).map (f x)) 0
    rw [map_zero]
    exact hz x
  exact hsep X (Presheaf.equalizerSieve (F := Q) s 0) hcover s 0
    (fun _ _ hf => hf)

/-- A separated HI presheaf locally generating a sheaf detects that sheaf on
original dense opens. The sheaf is not assumed homotopy invariant. -/
theorem sheaf_section_eq_zero_of_dense_open_of_separated_local_generation
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (hsep : Presheaf.IsSeparated (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((toPresheaf k).obj P))
    (G : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (m : (toPresheaf k).obj P ⟶ G.obj)
    [∀ Y, Mono (m.app (op Y))]
    [Presheaf.IsLocallySurjective (SmoothSite.nisnevichTopology (Spec (.of k))) m]
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left) (s : G.obj.obj (op X))
    (hs : G.obj.map a.op s = 0) : s = 0 := by
  classical
  obtain ⟨R, hR, hRm⟩ := SmoothSite.mem_nisnevichTopology_iff.mp
    (Presheaf.imageSieve_mem (SmoothSite.nisnevichTopology (Spec (.of k))) m s)
  have hcov : Sieve.generate R ∈ SmoothSite.nisnevichTopology (Spec (.of k)) X :=
    Precoverage.generate_mem_toGrothendieck hR
  have hsheaf := ((isSheaf_iff_isSheaf_of_type
    (SmoothSite.nisnevichTopology (Spec (.of k))) _).mp
      ((sheafCompose (SmoothSite.nisnevichTopology (Spec (.of k)))
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).property).isSheafFor R hcov
  apply hsheaf.isSeparatedFor.ext
  intro Y f hf
  have : Etale f.left := SmoothSite.etale_of_mem_nisnevichPrecoverage hR hf
  obtain ⟨t, ht⟩ := hRm Y f hf
  let B := SmoothSite.etalePullback a f
  let j : B ⟶ Y := SmoothSite.etalePullbackSnd a f
  let b : B ⟶ A := SmoothSite.etalePullbackFst a f
  have : IsOpenImmersion j.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd a.left f.left))
  have hjdense : DenseRange j.left := by
    change Dense (Set.range (pullback.snd a.left f.left))
    rw [IsOpenImmersion.range_pullbackSnd]
    exact ha.preimage f.left.isOpenMap
  have hj : j ≫ f = b ≫ a := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.condition.symm
  have htzero : P.transfer ((Cor.graphFunctor k).map j) t = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (m.app (op B))).mp inferInstance
    rw [map_zero]
    change m.app (op B) (((toPresheaf k).obj P).map j.op t) = 0
    rw [NatTrans.naturality_apply, ht]
    have he := ConcreteCategory.congr_hom (congrArg (fun g => G.obj.map g.op) hj) s
    simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, map_zero] using he
  have ht0 := section_eq_zero_of_dense_open_of_separated P hP hsep j hjdense t htzero
  change G.obj.map f.op s = G.obj.map f.op 0
  rw [map_zero, ← ht, ht0, map_zero]

/-- The canonical Nisnevich sheafification of an original HI PST is detected on
actual dense opens, before its homotopy invariance has been proved. -/
theorem nisnevichSheafify_section_eq_zero_of_dense_open
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X A : SmoothSite (Spec (.of k))} (a : A ⟶ X) [IsOpenImmersion a.left]
    (ha : DenseRange a.left)
    (s : ((nisnevichSheafify k).obj P).obj.sections (Cor.mk X))
    (hs : ((nisnevichSheafify k).obj P).obj.transfer ((Cor.graphFunctor k).map a) s = 0) :
    s = 0 := by
  exact sheaf_section_eq_zero_of_dense_open_of_separated_local_generation
    (nisnevichImage P) (nisnevichImage_isA1Invariant P hP)
    (nisnevichImage_isSeparated P)
    ((SheafWithTransfers.toSheaf k).obj ((nisnevichSheafify k).obj P))
    ((toPresheaf k).map (nisnevichImageι P)) a ha s hs

end Motivic.PresheafWithTransfers
