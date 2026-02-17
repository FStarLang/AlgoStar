.. _Ch33_CompGeometry:

########################################
Computational Geometry
########################################

This chapter covers the line-segment primitives from CLRS Chapter 33,
Section 33.1. The formalization implements the cross-product direction
test and the SEGMENTS-INTERSECT algorithm using orientation tests.
All implementations are fully verified with **zero admits, assumes, or
assume_ calls**. Every Pulse function is proven equivalent to a pure
specification.

Pure Specifications
====================

The core geometry predicates are expressed as pure functions on
integer coordinates:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.fst
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

Segment Intersection
=====================

The full intersection test follows CLRS's algorithm exactly: compute
four direction values, check for the general straddling case, then
handle the four collinear boundary cases:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.fst
   :language: fstar
   :start-after: //SNIPPET_START: segments_intersect_spec
   :end-before: //SNIPPET_END: segments_intersect_spec

Two segments straddle each other when their endpoints lie on opposite
sides of the other segment's supporting line. The special cases cover
situations where an endpoint is exactly collinear with the other
segment and lies within its bounding box.

Pulse Implementations
======================

Each Pulse ``fn`` is proven to return exactly the value of its pure
specification. The postconditions use ``pure (result == …_spec …)``
to express functional equivalence.

Cross Product
~~~~~~~~~~~~~

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.fst
   :language: pulse
   :start-after: //SNIPPET_START: cross_product_sig
   :end-before: //SNIPPET_END: cross_product_sig

Direction
~~~~~~~~~

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.fst
   :language: pulse
   :start-after: //SNIPPET_START: direction_sig
   :end-before: //SNIPPET_END: direction_sig

On-Segment
~~~~~~~~~~

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.fst
   :language: pulse
   :start-after: //SNIPPET_START: on_segment_sig
   :end-before: //SNIPPET_END: on_segment_sig

Segment Intersection
~~~~~~~~~~~~~~~~~~~~

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.fst
   :language: pulse
   :start-after: //SNIPPET_START: segments_intersect_sig
   :end-before: //SNIPPET_END: segments_intersect_sig

The implementation computes the four direction values ``d1`` through
``d4``, checks the general straddling condition, and falls through to
the collinear special cases. Because all branches are pure
conditionals on integers, the proof is handled automatically by SMT.

Complexity
==========

All operations perform a constant number of arithmetic operations
and comparisons. The operation counts are defined as named constants:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: op_counts
   :end-before: //SNIPPET_END: op_counts

A lemma confirms the total is bounded by a small constant:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: all_constant
   :end-before: //SNIPPET_END: all_constant

The composition lemma verifies that the segment intersection cost
decomposes into at most four direction tests plus two on-segment
checks, matching the CLRS analysis:

.. literalinclude:: ../ch33-comp-geometry/CLRS.Ch33.Segments.Complexity.fst
   :language: fstar
   :start-after: //SNIPPET_START: composition
   :end-before: //SNIPPET_END: composition

Proof Techniques Summary
=========================

This chapter demonstrates a straightforward verification pattern for
O(1) geometry primitives:

1. **Specification-first design**: Pure total functions define the
   expected result for every input combination.

2. **Functional equivalence postconditions**: Each Pulse function's
   postcondition asserts ``result == spec …``, so correctness is a
   single SMT query with no manual lemma calls.

3. **Constant-time analysis via named constants**: Rather than
   threading ghost counters (as done for loop-based algorithms),
   O(1) operations are analyzed by assigning a fixed operation count
   and proving arithmetic bounds.
