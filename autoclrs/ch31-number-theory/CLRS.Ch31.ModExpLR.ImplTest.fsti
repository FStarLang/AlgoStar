module CLRS.Ch31.ModExpLR.ImplTest

open Pulse.Lib.Pervasives
open FStar.SizeT

module SZ = FStar.SizeT

val test_mod_exp_lr (_:unit) : stt bool emp (fun r -> pure (r == true))
