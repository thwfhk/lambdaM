(* module Metric:
   support functions for metric and metric context *)
open Syntax
open Print

val emptymctx : metricContext
val getmetric : metricContext -> string -> metric option
val addmetric : metricContext -> string -> metric -> metricContext
val shiftMetricContext: metricContext -> int -> metricContext

val generatePiType : ty -> int -> string -> ty
val addbindingOfMetric : context -> int -> string -> context
val generateMetric : int -> int -> metric
val substMetric : metric -> ty -> ty
val derivedformTmFun : string -> ty list -> ty -> term -> term
val derivedformTmFunApp : string -> term -> metric -> term
val metricless : context -> metricContext -> metric -> metric -> bool