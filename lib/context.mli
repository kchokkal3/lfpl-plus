open! Core
open! Ast

module Binding : sig
  type status =
    | Bound  (** Variable is bound but not yet read *)
    | Read  (** Variable has been read *)

  type t = LType.t * status option
end

type t

val create : ?check_diamonds:bool -> unit -> t

val of_defns : ?check_diamonds:bool -> (Var.t * LType.t) list -> t

val add : t -> Var.t -> LType.t -> unit Or_error.t

val find : t -> Var.t -> Binding.t option

val remove : t -> Var.t -> unit Or_error.t

val read : t -> Var.t -> unit Or_error.t

val read_latest_dmd : t -> unit Or_error.t

val merge : t -> t -> t -> unit

val duplicate : t -> t

val duplicate_dmd_free : t -> t
