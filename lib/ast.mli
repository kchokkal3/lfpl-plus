open! Core

module LType : sig
  type t =
    | Diamond
    | Fun of (t * t)
    | Sfun of (t * t)
    | List of t
    | Stack of t
    | Tree of t
    | Prod of (t * t)
    | Unit
    | Sum of (t * t)
    | TypeAlias of string
  [@@deriving sexp, equal]

  val to_string_hum : t -> string

  include Stringable.S with type t := t
end

module Var : sig
  type t = string * int option [@@deriving sexp, compare, hash, equal]

  include Comparator.S with type t := t

  val to_string_hum : t -> string
end

module Lbl : sig
  type t = string [@@deriving sexp]
end

module LExpr : sig
  type t =
    | Diamond
    | Var of Var.t
    | Lam of (Var.t * LType.t * t)
    | Slam of (Var.t * LType.t * t)
    | App of (t * t)
    | Nil of LType.t
    | Cons of (t * t * t)
    | Leaf of LType.t
    | Node of (t * t * t * t)
    | Snil of LType.t
    | Scons of (t * t)
    | Lrec of (t * t * (Var.t * Var.t * Var.t * t))
    | Trec of (t * t * (Var.t * Var.t * Var.t * Var.t * t)) (* d, y1, x, y2 *)
    | Pair of (t * t)
    | Letp of (t * (Var.t * Var.t * t))
    | Null
    | Inj of ((LType.t * LType.t) * (t, t) Either.t)
    | Case of (t * (Var.t * t) * (Var.t * t))
    | Scase of (t * t * (Var.t * Var.t * t))
    | List of (LType.t * t list)
    | Stack of (LType.t * t list)
  [@@deriving sexp]

  val to_string_hum : t -> string
end

module LDefn : sig
  type t =
    | Decl of (string * LType.t)
    | Defn of (string * LExpr.t)
    | Typedef of (string * LType.t)
    | Val of LExpr.t
  [@@deriving sexp]
end
