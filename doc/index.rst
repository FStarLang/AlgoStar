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
   ch15_dynamic_prog
