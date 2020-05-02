(* module eval:
   functions for evaluation *)

open Syntax
open Metric

val eval : context -> term -> term 
(* val metricless : context -> metricContext -> metric -> metric -> bool *)