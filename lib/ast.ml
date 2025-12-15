open! Core

module LType = struct
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

  let rec to_string_hum (t : t) =
    match t with
    | Diamond ->
        "<>"
    | Fun (f, s) ->
        [%string "%{to_string_hum f} -@ %{to_string_hum s}"]
    | Sfun (f, s) ->
        [%string "%{to_string_hum f} -> %{to_string_hum s}"]
    | List i ->
        [%string "(%{to_string_hum i} list)"]
    | Stack i ->
        [%string "(%{to_string_hum i} stack)"]
    | Tree i ->
        [%string "(%{to_string_hum i} tree)"]
    | Prod (f, s) ->
        [%string "(%{to_string_hum f} * %{to_string_hum s})"]
    | Unit ->
        "1"
    | Sum (f, s) ->
        [%string "(%{to_string_hum f} + %{to_string_hum s})"]
    | TypeAlias name ->
        name

  let to_string t = sexp_of_t t |> Sexp.to_string

  let of_string s = Sexp.of_string s |> t_of_sexp
end

module Var = struct
  module T = struct
    type t = string * int option [@@deriving sexp, compare, hash, equal]
  end

  include T
  include Comparator.Make (T)

  let to_string_hum (x, _) = x
end

module Lbl = struct
  type t = string [@@deriving sexp]
end

module LExpr = struct
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
    | Trec of (t * t * (Var.t * Var.t * Var.t * Var.t * t))
    | Pair of (t * t)
    | Letp of (t * (Var.t * Var.t * t))
    | Null
    | Inj of ((LType.t * LType.t) * (t, t) Either.t)
    | Case of (t * (Var.t * t) * (Var.t * t))
    | Scase of (t * t * (Var.t * Var.t * t))
    | List of (LType.t * t list)
    | Stack of (LType.t * t list)
  [@@deriving sexp]

  let rec to_string_hum (t : t) =
    match t with
    | Diamond ->
        "<*>"
    | Var x ->
        Var.to_string_hum x
    | Lam (x, t, e) ->
        [%string
          "(fn (%{Var.to_string_hum x} : %{LType.to_string_hum t}). \
           %{to_string_hum e})"]
    | Slam (x, t, e) ->
        [%string
          "(sfn (%{Var.to_string_hum x} : %{LType.to_string_hum t}). \
           %{to_string_hum e})"]
    | App (f, s) ->
        [%string "(%{to_string_hum f} %{to_string_hum s})"]
    | Nil tp ->
        [%string "nil[%{LType.to_string_hum tp}]"]
    | Cons (d, x, e) ->
        [%string
          "cons(%{to_string_hum d}; %{to_string_hum x}; %{to_string_hum e})"]
    | Leaf tp ->
        [%string "leaf[%{LType.to_string_hum tp}]"]
    | Node (d, l, x, r) ->
        [%string
          "node(%{to_string_hum d}; %{to_string_hum l}; \n\
          \          %{to_string_hum x}; %{to_string_hum r})"]
    | Snil tp ->
        [%string "snil[%{LType.to_string_hum tp}]"]
    | Scons (x, e) ->
        [%string "scons(%{to_string_hum x}; %{to_string_hum e})"]
    | Lrec (e, e1, (x1, x2, y, e2)) ->
        [%string
          "lrec %{to_string_hum e} { %{to_string_hum e1} | %{Var.to_string_hum \
           x1}, %{Var.to_string_hum x2}, %{Var.to_string_hum y}. \
           %{to_string_hum e2}}"]
    | Trec (e, e1, (x1, y1, x2, y2, e2)) ->
        [%string
          "trec %{to_string_hum e} { %{to_string_hum e1} | %{Var.to_string_hum \
           x1}, %{Var.to_string_hum y1}, %{Var.to_string_hum x2}, \
           %{Var.to_string_hum y2}. %{to_string_hum e2}}"]
    | Pair (f, s) ->
        [%string "(%{to_string_hum f}, %{to_string_hum s})"]
    | Letp (e, (f, s, e1)) ->
        [%string
          "letp (%{Var.to_string_hum f}, %{Var.to_string_hum s}) = \
           %{to_string_hum e} in %{to_string_hum e1}"]
    | Null ->
        "()"
    | Inj ((f_tp, s_tp), First e) ->
        [%string
          "[%{LType.to_string_hum f_tp}; %{LType.to_string_hum \
           s_tp}](1.(%{to_string_hum e}))"]
    | Inj ((f_tp, s_tp), Second e) ->
        [%string
          "[%{LType.to_string_hum f_tp}; %{LType.to_string_hum \
           s_tp}](2.(%{to_string_hum e}))"]
    | Case (e, (x1, e1), (x2, e2)) ->
        [%string
          "case %{to_string_hum e} { %{Var.to_string_hum x1}. %{to_string_hum \
           e1} | %{Var.to_string_hum x2}. %{to_string_hum e2} }"]
    | Scase (e, e1, (x1, x2, e2)) ->
        [%string
          "scase %{to_string_hum e} { %{to_string_hum e1} | \
           %{Var.to_string_hum x1}, %{Var.to_string_hum x2}. %{to_string_hum \
           e2} }"]
    | List (typ, elems) ->
        let elem_strs = List.map elems ~f:to_string_hum in
        [%string
          "[%{LType.to_string_hum typ}][%{String.concat ~sep:\"; \" elem_strs}]"]
    | Stack (typ, elems) ->
        let elem_strs = List.map elems ~f:to_string_hum in
        [%string
          "[%{LType.to_string_hum typ}][|%{String.concat ~sep:\"; \" \
           elem_strs}|]"]
end

module LDefn = struct
  type t =
    | Decl of (string * LType.t)
    | Defn of (string * LExpr.t)
    | Typedef of (string * LType.t)
    | Val of LExpr.t
  [@@deriving sexp]
end
