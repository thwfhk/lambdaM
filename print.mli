(* module Print:
   support functions for printing and debugging *)

open Syntax

val printType: context -> ty -> unit
val printTerm: context -> term -> unit
val debugType: context -> ty -> unit
val debugTerm: context -> term -> unit