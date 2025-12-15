open! Core
open! Ast

val synthesize_tp : ctx:Context.t -> expr:LExpr.t -> LType.t Or_error.t

val typecheck : ctx:Context.t -> expr:LExpr.t -> tp:LType.t -> unit Or_error.t

val check_val : LExpr.t -> unit Or_error.t
