open! Core
open! Ast

type tpdef_map

val build_typedef_map : LDefn.t list -> tpdef_map

val expand_type : tpdef_map -> LType.t -> LType.t

val elab : LDefn.t list -> LExpr.t -> LExpr.t
