open! Core
open! Ast

val pp_synthesize_tp : string -> unit
(** Pretty-print synthesize type with elaboration (default) *)

val pp_typecheck : string -> LType.t -> unit
(** Pretty-print typecheck with elaboration (default) *)

val pp_synthesize_tp_no_elab : string -> unit
(** Pretty-print synthesize type without elaboration *)

val pp_typecheck_no_elab : string -> LType.t -> unit
(** Pretty-print typecheck without elaboration *)
