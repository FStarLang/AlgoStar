module CLRS.Ch31.GCD.ImplTest

open Pulse.Lib.Pervasives
open FStar.SizeT

module SZ = FStar.SizeT

val test_gcd (_:unit) : stt bool emp (fun r -> pure (r == true))
