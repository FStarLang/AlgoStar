module Dummy
open Pulse
open Pulse.Lib.C
#lang-pulse
fn dummy () requires emp returns _ : unit ensures emp { () }
