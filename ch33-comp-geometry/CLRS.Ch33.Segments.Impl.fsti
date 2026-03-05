(*
   Computational Geometry Primitives — CLRS Chapter 33, Section 33.1
   
   Pulse implementation interface: verified imperative versions of
   cross product, direction, on-segment, and segment intersection.
*)

module CLRS.Ch33.Segments.Impl
#lang-pulse
open Pulse.Lib.Pervasives
open CLRS.Ch33.Segments.Spec
open FStar.Mul

//SNIPPET_START: cross_product_sig
fn cross_product (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == cross_product_spec x1 y1 x2 y2 x3 y3)
//SNIPPET_END: cross_product_sig

//SNIPPET_START: direction_sig
fn direction (x1 y1 x2 y2 x3 y3: int)
  requires emp
  returns result: int
  ensures emp ** pure (result == direction_spec x1 y1 x2 y2 x3 y3)
//SNIPPET_END: direction_sig

//SNIPPET_START: on_segment_sig
fn on_segment (x1 y1 x2 y2 x y: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == on_segment_spec x1 y1 x2 y2 x y)
//SNIPPET_END: on_segment_sig

//SNIPPET_START: segments_intersect_sig
fn segments_intersect (x1 y1 x2 y2 x3 y3 x4 y4: int)
  requires emp
  returns result: bool
  ensures emp ** pure (result == segments_intersect_spec x1 y1 x2 y2 x3 y3 x4 y4)
//SNIPPET_END: segments_intersect_sig
