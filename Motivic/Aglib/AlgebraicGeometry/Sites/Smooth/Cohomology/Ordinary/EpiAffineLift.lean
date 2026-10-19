/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteSections
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Limits

/-! # Genuine ordinary epimorphic sections lift on affine singleton Nisnevich covers -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}}

/-- The actual finite coproduct, not an abstract section product, is affine. -/
theorem finiteCoproduct_affine {n : ℕ} (Y : Fin n → SmoothSite S)
    [∀ i, IsAffine (Y i).left] : IsAffine (finiteCoproduct Y).left := by
  induction n with
  | zero => change IsAffine (∅ : Scheme.{u}); infer_instance
  | succ n ih =>
    have := ih (fun i : Fin n => Y i.succ)
    change IsAffine ((Y 0).left ⨿ (finiteCoproduct (fun i : Fin n => Y i.succ)).left)
    infer_instance

end AlgebraicGeometry.Scheme.SmoothSite
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsNoetherian S]

/-- Only the original ordinary sheaves are glued. No positive-cohomology
presheaf is presumed to be a sheaf. -/
theorem exists_affine_nisnevich_lift
    {I Q : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}}
    (φ : I ⟶ Q) [Epi φ] (X : SmoothSite S) (s : Q.obj.obj (op X)) :
    ∃ (Y : SmoothSite S) (p : Y ⟶ X), IsAffine Y.left ∧ Etale p.left ∧
      Presieve.singleton p.left ∈ Nisnevich.precoverage X.left ∧
      ∃ l : I.obj.obj (op Y), φ.hom.app (op Y) l = Q.obj.map p.op s := by
  let J := nisnevichTopology S
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat.{u + 1} φ).mpr inferInstance
  obtain ⟨P, hP, hPQ⟩ := mem_nisnevichTopology_iff.mp
    (Presheaf.imageSieve_mem J φ.hom s)
  obtain ⟨ι, U, p, rfl⟩ := P.exists_eq_ofArrows
  choose l hl using fun i => hPQ _ _ (Presieve.ofArrows.mk i)
  have hp : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (p i).left) ∈
      Nisnevich.precoverage X.left := by
    have h := mem_nisnevichPrecoverage_iff.mp hP
    rw [Presieve.map_ofArrows] at h
    exact h
  let V (a : Σ i, (U i).left.affineCover.I₀) : SmoothSite S :=
    mk ((U a.1).left.affineCover.f a.2 ≫ (U a.1).hom)
  let j (a : Σ i, (U i).left.affineCover.I₀) : V a ⟶ U a.1 :=
    homMk ((U a.1).left.affineCover.f a.2) rfl
  let f (a : Σ i, (U i).left.affineCover.I₀) : V a ⟶ X := j a ≫ p a.1
  have hf : Presieve.ofArrows (fun a => (V a).left) (fun a => (f a).left) ∈
      Nisnevich.precoverage X.left :=
    Precoverage.comp_mem_coverings (fun i => (p i).left) hp
      (fun i a => (U i).left.affineCover.f a)
      (fun i => Nisnevich.zariskiPrecoverage_le_precoverage _ (U i).left.affineCover.mem₀)
  let N := normalizeFiniteNisnevichCoverOfMem f hf
  have ha (a) : IsAffine (V a).left := by dsimp [V]; infer_instance
  have htotal : IsAffine N.total.left := finiteCoproduct_affine _
  let lv (a) := I.obj.map (j a).op (l a.1)
  have hlv (a) : φ.hom.app (op (V a)) (lv a) = Q.obj.map (f a).op s := by
    change φ.hom.app (op (V a)) (I.obj.map (j a).op (l a.1)) = _
    rw [φ.hom.naturality_apply, hl, ← Functor.map_comp_apply, ← op_comp]
  obtain ⟨t, ht⟩ := exists_section_finiteCoproduct I
    (fun i => V (N.index i)) (fun i => lv (N.index i))
  refine ⟨N.total, N.map, htotal, inferInstance, N.mem_precoverage, t, ?_⟩
  have hcover : Sieve.ofArrows _ N.inclusion ∈ J N.total :=
    mem_nisnevichTopology_iff.mpr
      ⟨_, finiteCoproductι_mem_nisnevichPrecoverage _, Sieve.le_generate _⟩
  have hsheaf := ((isSheaf_iff_isSheaf_of_type J _).mp
    ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj Q).property).isSheafFor
      (Presieve.ofArrows _ N.inclusion) hcover
  apply hsheaf.isSeparatedFor.ext
  rintro W g ⟨i⟩
  change Q.obj.map (N.inclusion i).op (φ.hom.app (op N.total) t) =
    Q.obj.map (N.inclusion i).op (Q.obj.map N.map.op s)
  rw [← φ.hom.naturality_apply, ht, hlv,
    ← Functor.map_comp_apply, ← op_comp, N.inclusion_map]

end AlgebraicGeometry.Scheme.SmoothSite
