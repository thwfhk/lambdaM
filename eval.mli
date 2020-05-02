(* module Eval:
   functions for evaluation *)

open Syntax
open Print
open Metric

val eval : context -> term -> term 