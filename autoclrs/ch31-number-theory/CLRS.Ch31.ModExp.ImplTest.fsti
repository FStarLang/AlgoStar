module CLRS.Ch31.ModExp.ImplTest

open Pulse.Lib.Pervasives
open FStar.SizeT

module SZ = FStar.SizeT

val test_mod_exp (_:unit) : stt bool emp (fun r -> pure (r == true))
