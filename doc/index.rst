.. Verified CLRS Algorithms in F* and Pulse

.. role:: fstar(code)
   :language: fstar

Verified CLRS Algorithms in F* and Pulse
=========================================

This document is a companion to the classic textbook *Introduction to
Algorithms* by Cormen, Leiserson, Rivest, and Stein (CLRS, 4th edition).
It presents formalized implementations and proofs of correctness and
complexity for a significant subset of the algorithms covered in CLRS,
using `F* <https://fstar-lang.org>`_ for pure specifications and proofs,
and `Pulse <https://fstar-lang.org/tutorial/pulse>`_ for verified
imperative implementations.

All code listings in this document are extracted directly from verified
source files. Every theorem shown here has been mechanically checked by
the F*/Z3 toolchain, unless explicitly marked otherwise.

.. toctree::
   :maxdepth: 2
   :caption: Contents:

   intro
   ch02_sorting
   ch04_divide_conquer
   ch06_heapsort
   ch07_quicksort
   ch08_linear_sorting
   ch09_order_stats
   ch10_elementary_ds
   ch11_hash_tables
   ch12_bst
   ch13_rbtree
   ch15_dynamic_prog
   ch16_greedy
   ch21_disjoint_sets
   ch22_graphs
   ch23_mst
   ch24_sssp
   ch25_apsp
   ch26_max_flow
   ch31_number_theory
   ch32_string_match
   ch33_comp_geometry
   ch35_approximation
