(* module typecheck:
   functions for kinding and typing *)

open Syntax

(* val whnf : term -> term  *)
val typeof : context -> metricContext -> term -> ty 
val kindof : context -> ty -> kind 
val checkkind : context -> kind -> unit 
val kindeqv : context -> kind -> kind -> bool 
val tyeqv : context -> ty -> ty -> bool 
val tmeqv : context -> term -> term -> bool