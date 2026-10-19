/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData
public import Motivic.Transfers.Presheaf.Actions.Pencils.LambdaDictionary
/-! # The same retained section data in the original action dictionary

These are literal correspondence identities for the retained BoundarySectionData,
not assumed action identities. They preserve both original zero schemes and the
correction sign, and allow the norm consumers to refer to the unchanged toData.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

variable (k : Type u) [Field k] {S X Y A B Z C D V : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- The literal lam of the same retained section choice. -/
theorem BoundarySectionData.lam_comp_graph_dictionary
    (c : BoundarySectionData q π j p hq a z s hs H e ha d hd)
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
    (Q : SmoothSite (Spec (.of k))) (u : relativeTargetSite k t π v ⟶ Q) :
    let := c.a_unit
    let := c.b_unit
    let := c.n_unit
    let := c.d_unit
    let qA := j ≫ π
    let iA := retainedProductInclusion qA π v
    let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
    let : IsAffine (lambdaSourceSite k t π j).left := ‹IsAffine Y›
    let : IsAffine (retainedProduct qA π v) := retainedProduct_affine qA π v
    let : SmoothOfRelativeDimension 1 (iA ≫ pullback.fst qA π) :=
      retainedProduct_smooth qA π v
    let hcA := lambdaBoundary_retained_cover π j s d v hc
    let g := pullback.snd qA (v ≫ π) ≫ u.left
    let hb : (iA ≫ pullback.fst qA π) ≫ (lambdaSourceSite k t π j).hom = g ≫ Q.hom := by
      change (iA ≫ pullback.fst qA π) ≫ (qA ≫ t) =
        (pullback.snd qA (v ≫ π) ≫ u.left) ≫ Q.hom
      have hu : u.left ≫ Q.hom = (v ≫ π) ≫ t := u.w
      rw [Category.assoc (pullback.snd qA (v ≫ π)) u.left Q.hom, hu]
      rw [retainedProductInclusion_fst]
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ t) (pullback.condition (f := qA) (g := v ≫ π))
    (BoundarySectionData.toData k t q π j p hq a α β h z s hs H e ha d hd
      c v hc φ hφ).lam ≫ (Cor.graphFunctor k).map u =
      Cor.boundarySection (lambdaSourceSite k t π j) Q zA (pullback.fst qA π) iA
        (tensorLineBundle _ c.T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
        hcA g hb c.aS -
      Cor.boundarySection (lambdaSourceSite k t π j) Q zA (pullback.fst qA π) iA
        c.T hcA g hb c.bS := by
  let := c.a_unit
  let := c.b_unit
  let := c.n_unit
  let := c.d_unit
  exact dataOfBoundarySections_lam_comp_graph
    k t q π j p hq a α β h z s hs H e ha d hd v hc
    c.T c.N c.aS c.bS c.nS c.dS c.hA c.hN φ hφ Q u


/-- The literal psi of the same retained section choice. -/
theorem BoundarySectionData.psi_comp_graph_dictionary
    (c : BoundarySectionData q π j p hq a z s hs H e ha d hd)
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
    (Q : SmoothSite (Spec (.of k))) (u : relativeTargetSite k t π v ⟶ Q) :
    let := c.a_unit
    let := c.b_unit
    let := c.n_unit
    let := c.d_unit
    let qN := a ≫ q
    let iN := retainedProductInclusion qN π v
    let zN := psiBoundaryInclusion q π j p hq a z s hs d
    let : IsAffine (psiSourceSite k t q a).left := ‹IsAffine A›
    let : IsAffine (retainedProduct qN π v) := retainedProduct_affine qN π v
    let : SmoothOfRelativeDimension 1 (iN ≫ pullback.fst qN π) :=
      retainedProduct_smooth qN π v
    let hcN := psiBoundary_retained_cover q π j p hq a z s hs d v hc
    let g := pullback.snd qN (v ≫ π) ≫ u.left
    let hb : (iN ≫ pullback.fst qN π) ≫ (psiSourceSite k t q a).hom = g ≫ Q.hom := by
      change (iN ≫ pullback.fst qN π) ≫ (qN ≫ t) =
        (pullback.snd qN (v ≫ π) ≫ u.left) ≫ Q.hom
      have hu : u.left ≫ Q.hom = (v ≫ π) ≫ t := u.w
      rw [Category.assoc (pullback.snd qN (v ≫ π)) u.left Q.hom, hu]
      rw [retainedProductInclusion_fst]
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ t) (pullback.condition (f := qN) (g := v ≫ π))
    (BoundarySectionData.toData k t q π j p hq a α β h z s hs H e ha d hd
      c v hc φ hφ).psi ≫ (Cor.graphFunctor k).map u =
      Cor.boundarySection (psiSourceSite k t q a) Q zN (pullback.fst qN π) iN
        c.N hcN g hb c.dS -
      Cor.boundarySection (psiSourceSite k t q a) Q zN (pullback.fst qN π) iN
        c.N hcN g hb c.nS := by
  let := c.a_unit
  let := c.b_unit
  let := c.n_unit
  let := c.d_unit
  exact dataOfBoundarySections_psi_comp_graph
    k t q π j p hq a α β h z s hs H e ha d hd v hc
    c.T c.N c.aS c.bS c.nS c.dS c.hA c.hN φ hφ Q u

end AlgebraicGeometry.Scheme.RelativeCurvePencil
