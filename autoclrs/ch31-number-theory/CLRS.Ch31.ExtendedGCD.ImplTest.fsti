module CLRS.Ch31.ExtendedGCD.ImplTest

open Pulse.Lib.Pervasives
open FStar.SizeT

module SZ = FStar.SizeT

val test_extended_gcd (_:unit) : stt bool emp (fun r -> pure (r == true))
