.. _Ch33_CompGeometry:

########################################
Computational Geometry
########################################

This chapter covers the computational geometry algorithms from CLRS
Chapter 33: the line-segment primitives from §33.1 and two convex
hull algorithms from §33.3 (Graham Scan and Jarvis March). All
implementations are fully verified with **zero admits, assumes, or
assume_ calls**. Every Pulse function is proven equivalent to a pure
specification.

Segment Primitives (§33.1)
===========================

Pure Specifications
~~~~~~~~~~~~~~~~~~~~

The core geometry predicates are expressed as pure functions on
integer coordinates:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pure_specs
   :end-before: //SNIPPET_END: pure_specs

``cross_product_spec`` computes the cross product
(p₂ − p₁) × (p₃ − p₁). The sign encodes orientation: positive
means p₃ is counter-clockwise from the directed line p₁→p₂,
negative means clockwise, and zero means collinear.
``direction_spec`` is a thin wrapper, matching the CLRS naming.
``on_segment_spec`` checks whether a collinear point lies within
the bounding box of a segment.

Orientation Type
~~~~~~~~~~~~~~~~~

A formal type connects the cross-product sign to geometric meaning:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: orientation
   :end-before: //SNIPPET_END: orientation

Segment Intersection
~~~~~~~~~~~~~~~~~~~~~

The full intersection test follows CLRS's algorithm exactly: compute
four direction values, check for the general straddling case, then
handle the four collinear boundary cases:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: segments_intersect_spec
   :end-before: //SNIPPET_END: segments_intersect_spec

Two segments straddle each other when their endpoints lie on opposite
sides of the other segment's supporting line. The special cases cover
situations where an endpoint is exactly collinear with the other
segment and lies within its bounding box.

Pulse Implementations
~~~~~~~~~~~~~~~~~~~~~~

Each Pulse ``fn`` is proven to return exactly the value of its pure
specification. The postconditions use ``pure (result == …_spec …)``
to express functional equivalence.

**Cross Product:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: cross_product_sig
   :end-before: //SNIPPET_END: cross_product_sig

**Direction:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: direction_sig
   :end-before: //SNIPPET_END: direction_sig

**On-Segment:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: on_segment_sig
   :end-before: //SNIPPET_END: on_segment_sig

**Segment Intersection:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: segments_intersect_sig
   :end-before: //SNIPPET_END: segments_intersect_sig

The implementation computes the four direction values ``d1`` through
``d4``, checks the general straddling condition, and falls through to
the collinear special cases. Because all branches are pure
conditionals on integers, the proof is handled automatically by SMT.

Cross-Product Properties
~~~~~~~~~~~~~~~~~~~~~~~~~

The ``Segments.Lemmas`` module proves algebraic properties of the
cross product, useful as building blocks for the convex hull
algorithms:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Lemmas.fsti
   :language: fstar
   :start-after: //SNIPPET_START: cross_product_properties
   :end-before: //SNIPPET_END: cross_product_properties

All proofs are automatic (each is a one-line ``= ()``).

Complexity
~~~~~~~~~~~

All segment operations perform a constant number of arithmetic
operations and comparisons (O(1)). No formal complexity module
exists — constant-time primitives do not require one.

Graham Scan (§33.3)
====================

Graham's Scan computes the convex hull by sorting points by polar
angle w.r.t. the bottom-most point, then processing them with a
stack: for each point, pop the stack while the top makes a non-left
turn, then push. The algorithm runs in O(n log n) time, dominated
by the sorting step.

Pure Specifications
~~~~~~~~~~~~~~~~~~~~

**find_bottom_spec** — Find the starting point (minimum y, tiebreak
minimum x):

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: find_bottom_spec
   :end-before: //SNIPPET_END: find_bottom_spec

**polar_cmp_spec** — Compare polar angles of two points w.r.t. a
pivot, using the cross product:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: polar_cmp_spec
   :end-before: //SNIPPET_END: polar_cmp_spec

**Full scan specification** — pop-non-left, scan-step, loop, and
the complete Graham scan on pre-sorted indices:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: scan_specs
   :end-before: //SNIPPET_END: scan_specs

**pop_while_spec** — SZ.t version for direct Pulse array
compatibility:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: pop_while_spec
   :end-before: //SNIPPET_END: pop_while_spec

Pulse Implementations
~~~~~~~~~~~~~~~~~~~~~~

**find_bottom:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: find_bottom_sig
   :end-before: //SNIPPET_END: find_bottom_sig

Postcondition: ``SZ.v result == find_bottom_spec sxs sys`` — the
result is the index of the bottom-most point — and
``SZ.v result < SZ.v len`` — the result is a valid index.

**polar_cmp:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: polar_cmp_sig
   :end-before: //SNIPPET_END: polar_cmp_sig

Postcondition: ``result == polar_cmp_spec sxs sys …`` — exact cross
product of the three indexed points.

**pop_while:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: pop_while_sig
   :end-before: //SNIPPET_END: pop_while_sig

Postcondition: ``SZ.v result == pop_while_spec …`` and
``SZ.v result <= SZ.v top_in`` — the stack pointer decreases or stays
the same.

Correctness Properties
~~~~~~~~~~~~~~~~~~~~~~~

The ``all_left_turns`` predicate formalizes the convex hull invariant:
every consecutive triple of hull vertices makes a strict left turn
(cross product > 0):

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: correctness_defs
   :end-before: //SNIPPET_END: correctness_defs

The key correctness lemma is ``pop_while_ensures_left_turn``: after
popping, if the stack has ≥ 2 elements, the top two elements and the
new point make a left turn. This is the **CLRS Theorem 33.1
maintenance step** — pushing the new point preserves the convex
position of the stack:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.GrahamScan.Lemmas.fsti
   :language: fstar
   :start-after: //SNIPPET_START: pop_while_left_turn
   :end-before: //SNIPPET_END: pop_while_left_turn

Complexity
~~~~~~~~~~~

O(n log n) dominated by sorting; the scan loop is O(n) amortized
(each point is pushed and popped at most once). The complexity
definitions are stated and proven as pure functions but are **not
formally linked** to the Pulse implementation via ghost operation
counters.

Limitations
~~~~~~~~~~~~

- Only ``find_bottom``, ``polar_cmp``, and ``pop_while`` are
  implemented in Pulse. The full scan loop and sorting step are
  specified purely but not yet implemented as Pulse functions.
- The sorting step is assumed (``graham_scan_sorted`` takes
  pre-sorted indices).
- The ``all_left_turns`` invariant maintenance step is proven, but
  the full inductive proof that the complete algorithm produces an
  ``all_left_turns`` hull is not completed.

Jarvis March — Gift Wrapping (§33.3)
======================================

Jarvis's March computes the convex hull by starting from the leftmost
point and repeatedly selecting the most clockwise point as the next
hull vertex. The algorithm runs in O(nh) time where h is the number
of hull vertices.

Pure Specifications
~~~~~~~~~~~~~~~~~~~~

**find_leftmost_spec** — Find the starting point (minimum x,
tiebreak minimum y):

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.JarvisMarch.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: find_leftmost_spec
   :end-before: //SNIPPET_END: find_leftmost_spec

**find_next_spec** — Find the next hull vertex by scanning all points
and selecting the one that makes the most clockwise turn:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.JarvisMarch.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: find_next_spec
   :end-before: //SNIPPET_END: find_next_spec

**jarvis_march_spec** — Full convex hull computation, returning the
number of hull vertices:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.JarvisMarch.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: jarvis_march_spec
   :end-before: //SNIPPET_END: jarvis_march_spec

Pulse Implementations
~~~~~~~~~~~~~~~~~~~~~~

**find_leftmost:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.JarvisMarch.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: find_leftmost_sig
   :end-before: //SNIPPET_END: find_leftmost_sig

**find_next:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.JarvisMarch.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: find_next_sig
   :end-before: //SNIPPET_END: find_next_sig

**jarvis_march:**

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.JarvisMarch.Impl.fsti
   :language: fstar
   :start-after: //SNIPPET_START: jarvis_march_sig
   :end-before: //SNIPPET_END: jarvis_march_sig

The ``jarvis_march`` postcondition guarantees:
``SZ.v h == jarvis_march_spec sxs sys`` (exact match with spec),
``SZ.v h >= 1`` (at least one hull vertex), and
``SZ.v h <= SZ.v len`` (at most all input points).

Correctness Properties
~~~~~~~~~~~~~~~~~~~~~~~

The Jarvis march correctness definitions:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.JarvisMarch.Spec.fst
   :language: fstar
   :start-after: //SNIPPET_START: correctness_defs
   :end-before: //SNIPPET_END: correctness_defs

``is_leftmost`` asserts that a point is the lexicographic minimum by
x, then y. ``all_left_of`` asserts that all points (other than p)
lie to the left of or on the directed line p→q — this means edge
(p, q) is a supporting edge of the convex hull.

The core correctness theorem is ``find_next_all_left_of``: from any
hull vertex, the point selected by ``find_next`` satisfies
``all_left_of``, meaning all other points lie to the left of the
directed line from current to next. This uses:

- ``half_plane_transitivity``: an algebraic proof that cross-product
  comparison is transitive when all points are in the upper
  half-plane (y[k] ≥ y[current]).
- ``cross_prod_transitivity``: the translated version stated
  directly in terms of ``cross_prod``, with an SMT pattern for
  automatic application.

The proof requires two preconditions: (1) all non-current points are
strictly above the current point (strict upper half-plane), and (2)
no two distinct non-current points have the same polar angle (general
position). Under these conditions, ``find_next`` correctly identifies
the most-clockwise point.

Complexity
~~~~~~~~~~~

O(nh) where n is the number of input points and h is the number of
hull vertices. In the worst case (all points on hull), this is O(n²).
The complexity bounds are stated and proven as pure functions but are
**not formally linked** to the Pulse implementation via ghost
operation counters.

Limitations
~~~~~~~~~~~~

- The ``all_left_of`` correctness theorem requires **general
  position** (no collinear triples) and **strict upper half-plane**
  (all y[k] > y[current]). Real-world point sets may violate these
  assumptions.
- ``jarvis_march`` returns only the hull vertex *count*, not the
  vertices themselves (no output array).
- The full closed-polygon convexity property is not proven
  end-to-end; ``all_left_of`` is established per edge under
  specific preconditions.

Proof Techniques Summary
=========================

This chapter demonstrates several verification patterns:

1. **Specification-first design**: Pure total functions define the
   expected result. Pulse implementations are proven equivalent
   via ``result == spec …`` postconditions.

2. **Functional equivalence postconditions**: Each Pulse function's
   postcondition asserts ``result == spec …``, so correctness
   reduces to a single SMT query.

3. **Half-plane transitivity**: The algebraic core of the Jarvis
   march proof. Cross-product comparison is transitive in the upper
   half-plane, enabling an inductive argument that the greedy
   selection finds the most-clockwise point.

4. **Loop invariant peeling**: The ``pop_while`` loop uses a
   ``keep_going`` flag pattern with the invariant stated in two
   branches (running vs. stopped), enabling the proof to track
   both the running state and the accumulated result.

Verification Status Summary
=============================

.. list-table::
   :header-rows: 1
   :widths: 40 20 20

   * - Module
     - Type
     - Admits
   * - Segments.Spec
     - Pure spec
     - 0
   * - Segments.Impl
     - Pulse impl
     - 0
   * - Segments.Lemmas
     - Pure proof
     - 0
   * - Segments (combined)
     - Combined
     - 0
   * - GrahamScan.Spec
     - Pure spec
     - 0
   * - GrahamScan.Impl
     - Pulse impl
     - 0
   * - GrahamScan.Lemmas
     - Pure proof
     - 0
   * - GrahamScan (combined)
     - Combined
     - 0
   * - JarvisMarch.Spec
     - Pure spec
     - 0
   * - JarvisMarch.Impl
     - Pulse impl
     - 0
   * - JarvisMarch.Lemmas
     - Pure proof
     - 0
   * - JarvisMarch (combined)
     - Combined
     - 0

All modules are fully verified with 0 admits ✅.
