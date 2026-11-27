# Unrestricted Erdős–Pach #132: continuation log

Blake Stone · research continuation, 2026-11-27.

This is a scoped research record, **not a claimed solution**.  Distances are
positive and multiplicities count unordered pairs.  (R(A)) is the number of
distances occurring at most (|A|) times.

## Inputs rechecked

The current additive-cover manuscript proves a strong theorem only when the
whole configuration is covered by few bounded-rank, polynomial-size GAPs.  Its
three-anchor product bound cannot be applied just to the triangular interior
of an unrestricted candidate: pairs involving the two outer convex layers can
restore a distance that is rare in the interior.  No rarity-under-restoration
step is used here.

For a hypothetical unbounded family with (R(A)=1), the checked unrestricted
reductions currently force:

* the first two convex layers to contain ((2/3+o(1))n) points;
* the remaining interior to contain ((1/3+o(1))n) points, almost all with six
  minimum-distance neighbours;
* every minimum-distance component to lie in a mesh-(delta) triangular
  lattice;
* (O(n^{5/7})) good centres per lattice orientation, hence
  (Omega(n^{2/7})) orientations and (Omega(n^{9/14})) exceptional
  interior vertices.

These are necessary conditions, not a contradiction.

## Attempt 1: accumulate boundary deficits over unrelated orientations

Let (b) be the number of exceptional interior vertices.  The internal
minimum-distance graph satisfies
[
 e_delta(I)le 3|I|-b/2.
]
Since the full minimum class is rich, at least (b/2) minimum pairs (up to the
already controlled (o(n)) layer-size error) must touch the outer two layers.
The orientation theorem gives
[
 bgg n^{9/14}.
]

The best checked quantitative short-incidence estimate for a fixed short rank
allows
[
 O!left(n^{55/56}(log n)^{1/7}ight)
]
edges touching a fixed union of convex layers.  Thus the attempted
contradiction would compare exponents
[
 9/14=36/56 quadhbox{and}quad 55/56.
]
They are separated by (19/56) in the wrong direction.  Summing a fixed
number of triangular shells only changes constants.  The available complete
patch radius (n^{1/112}(log n)^{-1/14}) is also far too small to recover
this exponent gap by summing all controlled shells.  This route therefore
needs either a short-incidence exponent below (9/14), a much stronger
orientation/component bound, or a new coupling between the short interior
spectrum and the long outer-layer spectrum.

## Attempt 2: finite descent at the first uncovered order

The small-order literature now records the first assertion through (n=14)
(the (n=11,12) branch depends on the Wei classification, for which exact
public certificates and a repaired proof chain are available).  This was a
literature correction to the older note that called (n=11) unhandled; the
full external proof chain was not rerun in this session.

Suppose an (n=15) counterexample exists.  Pair counting gives at most seven
distances, while the published bound (g(6)=13) forces at least seven.
Hence there are exactly seven distance classes.  Write the six nondiametral
multiplicities as
[
 16+x_1,ldots,16+x_6,qquad x_ige0,
]
and write (d) for the diameter multiplicity.  Since there are 105 pairs,
[
 d+sum_{i=1}^6x_i=9.
]
The unique-diameter and star-diameter theorems exclude (d=1) and guarantee
that the original diameter survives every one-point deletion.  Therefore
(2le dle9).

Deleting any vertex (v) leaves 14 points and a surviving rare diameter.
The verified (n=14) result forces another rare class.  Consequently
[
 orall vquadexists iin{1,ldots,6}:
 deg_{G_i}(v)ge x_i+2. 	ag{1}
]
This is an exact necessary condition.

Condition (1), even together with the extremal multiplicity profile, is not
enough.  On (mathbb Z/15mathbb Z), color an edge by its circular
difference (1,ldots,7).  Each color initially has 15 edges.  Move six
distinct color-7 edges, one into each of colors 1 through 6.  The class sizes
become
[
 (16,16,16,16,16,16,9).
]
Every rich color contains its original 2-regular difference graph plus one
edge.  After deleting any vertex it has 13 or 14 edges, so all six rich
classes become rare at the new threshold.  Color 7 is a 15-cycle with six
edges removed, hence a linear forest; it is individually realizable as a
planar diameter graph.  The exact verifier in
`verify-n15-deletion-obstruction.py` checks these statements.

This is **not** a Euclidean counterexample: the seven graphs have not been
realized simultaneously by one planar distance matrix.  It proves that
one-point descent, pair counting, and individual diameter-graph constraints
cannot settle (n=15).  Any successful finite proof must impose a joint
Euclidean compatibility condition on at least two distance classes.

## Next nonrepeating tests

1. Seek a coupled incidence bound for the first distance joining differently
   oriented triangular components, with the outer convex layer present.
2. For (n=15), encode simultaneous Cayley–Menger/Gram constraints for the
   seven extremal color classes rather than extending deletion counting.
3. Do not infer a common triangular lattice, or global rarity from rarity in
   the interior additive cover.

## Source anchors

* [Repository additive-cover manuscript](additive-covers.tex)
* [Current unrestricted frontier](https://erdosproblems.ai/wiki/research/erdos_132/unrestricted_frontier)
* [Translated-triangle/orientation bound](https://erdosproblems.ai/wiki/research/erdos_132/translated_triangles)
* [Marchetto finite cases 7–13](https://github.com/JuanMarchetto/erdos-132-note)
* [Exact Wei-chain certificates](https://github.com/lyfar/erdos132-wei-certificates)
