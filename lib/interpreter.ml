open! Core
open! Ast
open! Or_error.Let_syntax

module Value = struct
  type 'a tree = Leaf | Node of ('a tree * 'a * 'a tree) [@@deriving sexp_of]

  type t =
    | VNull
    | VDiamond
    | VFun of (t -> t)
    | VList of t list
    | VTree of t tree
    | VStack of t list
    | VPair of (t * t)
    | VSum of (t, t) Either.t
  [@@deriving sexp_of]

  let rec tree_to_string_hum_helper (tree : t tree) (prefix : string)
      (is_left : bool) =
    match tree with
    | Leaf ->
        ""
    | Node (l, x, r) ->
        let node_str =
          prefix ^ (if is_left then "|--" else "`--") ^ to_string_hum x ^ "\n"
        in
        let new_prefix = prefix ^ if is_left then "|  " else "   " in
        node_str
        ^ tree_to_string_hum_helper l new_prefix true
        ^ tree_to_string_hum_helper r new_prefix false

  and tree_to_string_hum (tree : t tree) =
    match tree with
    | Leaf ->
        "<empty tree>"
    | Node (l, x, r) ->
        let result =
          "\n" ^ to_string_hum x ^ "\n"
          ^ tree_to_string_hum_helper l "" true
          ^ tree_to_string_hum_helper r "" false
        in
        (* Remove trailing newline if present *)
        String.rstrip result

  and to_string_hum (t : t) =
    match t with
    | VNull ->
        "()"
    | VDiamond ->
        "<>"
    | VFun _ ->
        "vfun"
    | VList l ->
        "[ " ^ (List.map l ~f:to_string_hum |> String.concat ~sep:";") ^ " ]"
    | VStack s ->
        "[|" ^ (List.map s ~f:to_string_hum |> String.concat ~sep:";") ^ "|]"
    | VTree tree ->
        tree_to_string_hum tree
    | VPair (f, s) ->
        [%string "(%{to_string_hum f}, %{to_string_hum s})"]
    | VSum (First v) ->
        [%string "1.(%{to_string_hum v})"]
    | VSum (Second v) ->
        [%string "2.(%{to_string_hum v})"]
end

module Environment = struct
  type t = (Var.t, Value.t list, Var.comparator_witness) Map.t

  let empty = Map.empty (module Var)

  let add (ctx : t) (key : Var.t) (value : Value.t) : t =
    Map.add_multi ctx ~key ~data:value

  let find (ctx : t) (key : Var.t) : Value.t option =
    Map.find_multi ctx key |> List.hd

  let remove (ctx : t) (key : Var.t) : t =
    Map.change ctx key ~f:(function
      | None ->
          raise (Exn.create_s (Sexp.Atom "Variable not bound"))
      | Some y ->
          Some (List.tl_exn y) )
end

let rec eval ~(env : Environment.t) ~(expr : LExpr.t) =
  match expr with
  | LExpr.Diamond ->
      Value.VDiamond
  | LExpr.Var v ->
      Environment.find env v |> Option.value_exn
  | LExpr.Nil _ ->
      VList []
  | LExpr.Leaf _ ->
      VTree Leaf
  | LExpr.Null ->
      VNull
  | LExpr.Lam (x, _, e) ->
      VFun
        (fun v ->
          let env = Environment.add env x v in
          let res = eval ~env ~expr:e in
          let _env = Environment.remove env x in
          res )
  | LExpr.Slam (x, _, e) ->
      VFun
        (fun v ->
          let env = Environment.add env x v in
          let res = eval ~env ~expr:e in
          let _env = Environment.remove env x in
          res )
  | LExpr.App (f, s) -> (
      let func = eval ~env ~expr:f in
      match func with
      | VFun f ->
          let arg = eval ~env ~expr:s in
          f arg
      | _ ->
          raise (Exn.create_s (Sexp.Atom "Cannot apply to non-function value"))
      )
  | LExpr.Cons (d, x, y) -> (
      let _ = eval ~env ~expr:d in
      let hd = eval ~env ~expr:x in
      let tl = eval ~env ~expr:y in
      match tl with
      | VList tl ->
          VList (hd :: tl)
      | _ ->
          raise (Exn.create_s (Sexp.Atom "Cannot cons onto non-list value")) )
  | LExpr.Snil _ ->
      VStack []
  | LExpr.Scons (x, y) -> (
      let hd = eval ~env ~expr:x in
      let tl = eval ~env ~expr:y in
      match tl with
      | VStack tl ->
          VStack (hd :: tl)
      | _ ->
          raise (Exn.create_s (Sexp.Atom "Cannot scons onto non-stack value")) )
  | LExpr.Node (d, l, x, r) -> (
      let _ = eval ~env ~expr:d in
      let left = eval ~env ~expr:l in
      let ele = eval ~env ~expr:x in
      let right = eval ~env ~expr:r in
      match (left, right) with
      | VTree left, VTree right ->
          VTree (Node (left, ele, right))
      | _ ->
          raise
            (Exn.create_s (Sexp.Atom "Cannot build trees on non-tree values")) )
  | LExpr.Lrec (e, e1, (x1, x2, y, e2)) -> (
      let l = eval ~env ~expr:e in
      let rec lrec vs =
        match vs with
        | [] ->
            eval ~env ~expr:e1
        | v :: vs ->
            let inner_env = Environment.add env x1 VDiamond in
            let inner_env = Environment.add inner_env x2 v in
            let inner_env = Environment.add inner_env y (lrec vs) in
            eval ~env:inner_env ~expr:e2
      in
      match l with
      | VList l ->
          lrec l
      | _ ->
          raise
            (Exn.create_s (Sexp.Atom "Cannot eval lrec with non-list value")) )
  | LExpr.Trec (e, e1, (x1, y1, x2, y2, e2)) -> (
      let t = eval ~env ~expr:e in
      let rec trec tree =
        match tree with
        | Value.Leaf ->
            eval ~env ~expr:e1
        | Value.Node (left, v, right) ->
            let inner_env = Environment.add env x1 VDiamond in
            let inner_env = Environment.add inner_env y1 (trec left) in
            let inner_env = Environment.add inner_env x2 v in
            let inner_env = Environment.add inner_env y2 (trec right) in
            eval ~env:inner_env ~expr:e2
      in
      match t with
      | VTree t ->
          trec t
      | _ ->
          raise
            (Exn.create_s (Sexp.Atom "Cannot eval trec with non-tree value")) )
  | LExpr.Pair (f, s) ->
      let f = eval ~env ~expr:f in
      let s = eval ~env ~expr:s in
      VPair (f, s)
  | LExpr.Letp (e1, (x, y, e2)) -> (
    match eval ~env ~expr:e1 with
    | VPair (v1, v2) ->
        let inner_env = Environment.add env x v1 in
        let inner_env = Environment.add inner_env y v2 in
        eval ~env:inner_env ~expr:e2
    | _ ->
        raise (Exn.create_s (Sexp.Atom "Cannot eval lept with non-pair value"))
    )
  | LExpr.Inj (_, e) ->
      VSum
        ( match e with
        | First expr ->
            First (eval ~env ~expr)
        | Second expr ->
            Second (eval ~env ~expr) )
  | LExpr.Case (e, (x1, e1), (x2, e2)) -> (
      let arg = eval ~env ~expr:e in
      match arg with
      | VSum e ->
          Either.value_map e
            ~first:(fun v1 -> eval ~env:(Environment.add env x1 v1) ~expr:e1)
            ~second:(fun v2 -> eval ~env:(Environment.add env x2 v2) ~expr:e2)
      | _ ->
          raise (Exn.create_s (Sexp.Atom "Cannot eval case with non-sum value"))
      )
  | LExpr.Scase (e, e1, (x1, x2, e2)) -> (
      let arg = eval ~env ~expr:e in
      match arg with
      | VStack [] ->
          eval ~env ~expr:e1
      | VStack (h :: tl) ->
          let env = Environment.add env x1 h in
          let env = Environment.add env x2 (VStack tl) in
          eval ~env ~expr:e2
      | _ ->
          raise
            (Exn.create_s (Sexp.Atom "Cannot eval scase with non-stack value"))
      )
  | LExpr.List _ ->
      raise
        (Exn.create_s
           (Sexp.Atom "Stack syntactic sugar should've been elaborated") )
  | LExpr.Stack _ ->
      raise
        (Exn.create_s
           (Sexp.Atom "Stack syntactic sugar should've been elaborated") )
