open! Core
open! Ast

val parse : string -> LDefn.t list Or_error.t

val parse_expr : string -> LExpr.t Or_error.t

val pp_parse_type : string -> unit

val pp_parse_expr : string -> unit
