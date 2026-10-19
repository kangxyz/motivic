# General graph morphisms and stalk comparisons

These candidates retain actual scheme maps, relative products and stalk maps.
Their intended upstream owner is `Aglib.AlgebraicGeometry.Graph`; the lower
primitive is `Aglib.AlgebraicGeometry.Graph.Morphism`. Current consumers are
general graph/incidence adapters and their host correspondence applications.

| Exact import | Interface |
| --- | --- |
| `Motivic.Aglib.AlgebraicGeometry.Graph.Morphism` | The graph into a relative product and its projection laws |
| `Motivic.Aglib.AlgebraicGeometry.Graph.StalkTransport` | Compatible structural maps and actual open-chart stalk transport |
| `Motivic.Aglib.AlgebraicGeometry.Graph.PairGeometry` | The graph-to-middle-diagonal bridge |
| `Motivic.Aglib.AlgebraicGeometry.Graph.LeftPairGeometry` | The transposed graph-to-middle-diagonal bridge |

For `X Y S : Scheme.{u}`, with arbitrary universe `u`, `φ : X ⟶ Y` and
`g : Y ⟶ S`, `AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g` is the
actual map `X ⟶ pullback (φ ≫ g) g`. It is the pullback lift of `𝟙 X` and `φ`.
The laws `correspondenceGraph_fst` and `correspondenceGraph_snd` identify its
projections with `𝟙 X` and `φ`; both have reassociation/simplification APIs.
The closed-immersion instance requires `[IsSeparated g]`. The construction and
projection laws impose no separatedness, field or flatness hypothesis.

The compatible-structural-map form is
`AlgebraicGeometry.Scheme.Graph.morphism a b f h`, where
`a : X ⟶ S`, `b : Y ⟶ S`, `f : X ⟶ Y` and `h : f ≫ b = a`.
It maps `X ⟶ pullback a b` using the same original factors. In
[Pair](Pair.lean), `morphism_eq_correspondenceGraph` identifies
`morphism (f ≫ b) b f rfl` with `correspondenceGraph f b` by `rfl`.
The pair-map and aligned-stalk comparisons likewise retain their original maps.

In native namespace `AlgebraicGeometry.Scheme.Products`, `graphMiddlePair`
maps the graph ambient product to `pullback g g` by applying `φ` on the first
factor. `leftGraphMiddlePair` then transposes the two middle coordinates.
`correspondenceGraph_middlePair` and `correspondenceGraph_leftMiddlePair`
identify composition with either pair map as `φ ≫ pullback.diagonal g`,
with generated reassociation laws. These are pure general-geometry bridges;
actual `Cor`, transfer-presheaf and generator applications remain host source.

[StalkTransport](StalkTransport.lean) identifies graph stalk arrows through
open charts on both factors over a base monomorphism, retaining the actual
product map and its graph-commutation equation. It adds no graph-source
flatness premise. [Pair](Pair.lean), [LeftPair](LeftPair.lean) and
[CommonStalkTransport](CommonStalkTransport.lean) retain the displayed
regularity, kernel and neighborhood hypotheses of their stalk/common-list
results. These interfaces do not imply unrestricted purity or Tor symmetry.

Use the [general-geometry guide](../README.md) for lower subject owners and
[diagonal stalk transport](../Diagonal/StalkTransport.lean) for the original
stalk-alignment infrastructure. The
[host correspondence guide](../../../AlgebraicGeometry/Correspondences/README.md)
records the separate incidence and transfer consumers.
