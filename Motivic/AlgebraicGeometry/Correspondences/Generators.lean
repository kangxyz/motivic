/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Data.Finsupp.Basic

/-!
# Geometric generators of finite correspondences

An elementary finite correspondence from `X` to `Y` over `S` is an actual
integral closed subscheme of `X ×[S] Y` whose projection to `X` is finite
and surjective onto an irreducible component of `X`. Closed subschemes are
represented by mathlib's ideal sheaves and their constructed subschemes.

`FiniteCorrespondence` is the free abelian group on those geometric generators.
For integral `X` and separated `Y/S`, the graph of a morphism is a generator;
its projection is proved to be an isomorphism.

This file constructs the generators and cycle groups only. Intersection
multiplicities, composition and the category `Cor(S)` are not constructed here.
The definitions apply to arbitrary schemes; later applications will restrict
the objects to smooth separated finite-type schemes over a field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S X Y : Scheme.{u}}

/-- The source projection of a closed subscheme of a fiber product. -/
noncomputable def correspondenceProjection (f : X ⟶ S) (g : Y ⟶ S)
    (I : (pullback f g).IdealSheafData) : I.subscheme ⟶ X :=
  I.subschemeι ≫ pullback.fst f g

/-- An actual integral closed subscheme, finite and surjective over a source component. -/
def IsFiniteCorrespondenceGenerator (f : X ⟶ S) (g : Y ⟶ S)
    (I : (pullback f g).IdealSheafData) : Prop :=
  IsIntegral I.subscheme ∧ IsFinite (correspondenceProjection f g I) ∧
    Set.range (correspondenceProjection f g I) ∈ irreducibleComponents X

/-- The geometric basis of finite correspondences. -/
def FiniteCorrespondenceGenerator (f : X ⟶ S) (g : Y ⟶ S) : Type u :=
  {I : (pullback f g).IdealSheafData // IsFiniteCorrespondenceGenerator f g I}

/-- Integral cycles with finite support on the elementary finite correspondences. -/
abbrev FiniteCorrespondence (f : X ⟶ S) (g : Y ⟶ S) : Type u :=
  FiniteCorrespondenceGenerator f g →₀ ℤ

namespace FiniteCorrespondenceGenerator

variable {f : X ⟶ S} {g : Y ⟶ S} (Z : FiniteCorrespondenceGenerator f g)

/-- The integral scheme underlying an elementary correspondence. -/
noncomputable abbrev scheme : Scheme.{u} := Z.val.subscheme

/-- The canonical closed immersion into the product. -/
noncomputable abbrev inclusion : Z.scheme ⟶ pullback f g := Z.val.subschemeι

/-- The projection to the source. -/
noncomputable abbrev projection : Z.scheme ⟶ X := correspondenceProjection f g Z.val

instance : IsIntegral Z.scheme := Z.property.1

instance : IsClosedImmersion Z.inclusion := inferInstanceAs (IsClosedImmersion Z.val.subschemeι)

instance : IsFinite Z.projection := Z.property.2.1

/-- The image is literally an irreducible component of the source. -/
theorem range_projection_mem : Set.range Z.projection ∈ irreducibleComponents X :=
  Z.property.2.2

/-- On an irreducible source, a generator projects surjectively onto the whole source. -/
theorem projection_surjective [IrreducibleSpace X] : Function.Surjective Z.projection := by
  apply Set.range_eq_univ.mp
  have h := Z.range_projection_mem
  simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using h

/-- The cycle with multiplicity one on the given closed subscheme. -/
noncomputable def cycle : FiniteCorrespondence f g := Finsupp.single Z 1

@[simp]
theorem cycle_self : Z.cycle Z = 1 := Finsupp.single_eq_same

/-- Distinct geometric generators are distinguished by their unit cycles. -/
theorem cycle_injective : Function.Injective (cycle (f := f) (g := g)) := by
  intro Z W h
  by_contra hne
  have hc := congrArg (fun c : FiniteCorrespondence f g => c Z) h
  simp [cycle, hne] at hc

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence

variable {f : X ⟶ S} {g : Y ⟶ S}

/-- Equality of cycles is equality of every geometric multiplicity. -/
@[ext]
theorem ext {α β : FiniteCorrespondence f g}
    (h : ∀ Z, α Z = β Z) : α = β := Finsupp.ext h

end FiniteCorrespondence

section Graph

variable (φ : X ⟶ Y) (g : Y ⟶ S)

/-- The actual graph morphism into the fiber product. -/
noncomputable def correspondenceGraph : X ⟶ pullback (φ ≫ g) g :=
  pullback.lift (𝟙 X) φ (Category.id_comp (φ ≫ g))

@[reassoc (attr := simp)]
theorem correspondenceGraph_fst : correspondenceGraph φ g ≫ pullback.fst (φ ≫ g) g = 𝟙 X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem correspondenceGraph_snd : correspondenceGraph φ g ≫ pullback.snd (φ ≫ g) g = φ :=
  pullback.lift_snd _ _ _

instance [IsSeparated g] : IsClosedImmersion (correspondenceGraph φ g) := by
  unfold correspondenceGraph
  infer_instance

/-- The ideal sheaf cutting out the graph. -/
noncomputable def correspondenceGraphIdeal : (pullback (φ ≫ g) g).IdealSheafData :=
  (correspondenceGraph φ g).ker

@[reassoc, simp]
theorem graph_toImage_projection :
    (correspondenceGraph φ g).toImage ≫
      correspondenceProjection (φ ≫ g) g (correspondenceGraphIdeal φ g) = 𝟙 X := by
  simp [correspondenceProjection, correspondenceGraphIdeal]

instance [IsSeparated g] :
    IsIso (correspondenceProjection (φ ≫ g) g (correspondenceGraphIdeal φ g)) := by
  let : IsIso (correspondenceGraph φ g).toImage :=
    IsClosedImmersion.instIsIsoSchemeToImage _
  have h : correspondenceProjection (φ ≫ g) g (correspondenceGraphIdeal φ g) =
      inv (correspondenceGraph φ g).toImage := by
    apply (cancel_epi (correspondenceGraph φ g).toImage).mp
    simp
  exact h ▸ (asIso (correspondenceGraph φ g).toImage).symm.isIso_hom

/-- Graphs give genuine elementary finite correspondences for integral sources. -/
noncomputable def graphGenerator [IsIntegral X] [IsSeparated g] :
    FiniteCorrespondenceGenerator (φ ≫ g) g := by
  refine ⟨correspondenceGraphIdeal φ g, ?_, inferInstance, ?_⟩
  · change IsIntegral (correspondenceGraph φ g).image
    exact IsIntegral.of_isIso (correspondenceGraph φ g).toImage
  · have hsurj : Function.Surjective
        (correspondenceProjection (φ ≫ g) g (correspondenceGraphIdeal φ g)) :=
      (Scheme.homeoOfIso (asIso
        (correspondenceProjection (φ ≫ g) g (correspondenceGraphIdeal φ g)))).surjective
    simp [Set.range_eq_univ.mpr hsurj, irreducibleComponents_eq_singleton]

/-- The integral graph correspondence with its actual geometric support. -/
noncomputable def graphCycle [IsIntegral X] [IsSeparated g] :
    FiniteCorrespondence (φ ≫ g) g := (graphGenerator φ g).cycle

@[simp]
theorem graphCycle_coefficient [IsIntegral X] [IsSeparated g] :
    graphCycle φ g (graphGenerator φ g) = 1 :=
  FiniteCorrespondenceGenerator.cycle_self _

end Graph

end Motivic
