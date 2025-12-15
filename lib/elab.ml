open! Core
open! Ast

type t = int String.Map.t

type tpdef_map = LType.t String.Map.t

(* Expand type aliases recursively *)
let rec expand_type typedef_map ty =
  match ty with
  | LType.Diamond ->
      LType.Diamond
  | LType.Unit ->
      LType.Unit
  | LType.TypeAlias name -> (
    match Map.find typedef_map name with
    | Some expanded_ty ->
        expand_type typedef_map expanded_ty
    | None ->
        failwith [%string "Undefined type alias: %{name}"] )
  | LType.Fun (t1, t2) ->
      LType.Fun (expand_type typedef_map t1, expand_type typedef_map t2)
  | LType.Sfun (t1, t2) ->
      LType.Sfun (expand_type typedef_map t1, expand_type typedef_map t2)
  | LType.List t ->
      LType.List (expand_type typedef_map t)
  | LType.Stack t ->
      LType.Stack (expand_type typedef_map t)
  | LType.Tree t ->
      LType.Tree (expand_type typedef_map t)
  | LType.Prod (t1, t2) ->
      LType.Prod (expand_type typedef_map t1, expand_type typedef_map t2)
  | LType.Sum (t1, t2) ->
      LType.Sum (expand_type typedef_map t1, expand_type typedef_map t2)

let bind (names : t) ~var =
  let var, _ = var in
  let names =
    Map.update names var ~f:(function None -> 0 | Some x -> x + 1)
  in
  ((var, Map.find names var), names)

(* We elaborate the list syntatic sugar, expand typedefs, and rename variables in a single pass *)
let rec elab' (typedef_map : LType.t String.Map.t) (names : t) (t : LExpr.t) :
    LExpr.t =
  match (t : LExpr.t) with
  | Diamond ->
      Diamond
  | Var (x, _) ->
      let i = Map.find names x in
      Var (x, i)
  | Lam (x, tp, e) ->
      let x, names = bind names ~var:x in
      Lam (x, expand_type typedef_map tp, elab' typedef_map names e)
  | Slam (x, tp, e) ->
      let x, names = bind names ~var:x in
      Slam (x, expand_type typedef_map tp, elab' typedef_map names e)
  | App (f, s) ->
      App (elab' typedef_map names f, elab' typedef_map names s)
  | Nil tp ->
      Nil (expand_type typedef_map tp)
  | Snil tp ->
      Snil (expand_type typedef_map tp)
  | Cons (d, x, y) ->
      Cons
        ( elab' typedef_map names d
        , elab' typedef_map names x
        , elab' typedef_map names y )
  | Leaf tp ->
      Leaf (expand_type typedef_map tp)
  | Node (d, l, x, r) ->
      Node
        ( elab' typedef_map names d
        , elab' typedef_map names l
        , elab' typedef_map names x
        , elab' typedef_map names r )
  | Scons (x, y) ->
      Scons (elab' typedef_map names x, elab' typedef_map names y)
  | Lrec (e, e1, (x1, x2, y, e2)) ->
      let e = elab' typedef_map names e in
      let e1 = elab' typedef_map names e1 in
      let x1, names = bind names ~var:x1 in
      let x2, names = bind names ~var:x2 in
      let y, names = bind names ~var:y in
      let e2 = elab' typedef_map names e2 in
      Lrec (e, e1, (x1, x2, y, e2))
  | Trec (e, e1, (x1, y1, x2, y2, e2)) ->
      let e = elab' typedef_map names e in
      let e1 = elab' typedef_map names e1 in
      let x1, names = bind names ~var:x1 in
      let y1, names = bind names ~var:y1 in
      let x2, names = bind names ~var:x2 in
      let y2, names = bind names ~var:y2 in
      let e2 = elab' typedef_map names e2 in
      Trec (e, e1, (x1, y1, x2, y2, e2))
  | Pair (f, s) ->
      Pair (elab' typedef_map names f, elab' typedef_map names s)
  | Letp (e, (f, s, e1)) ->
      let e = elab' typedef_map names e in
      let f, names = bind names ~var:f in
      let s, names = bind names ~var:s in
      let e1 = elab' typedef_map names e1 in
      Letp (e, (f, s, e1))
  | Null ->
      Null
  | Inj ((t1, t2), e) ->
      Inj
        ( (expand_type typedef_map t1, expand_type typedef_map t2)
        , Either.map e ~first:(elab' typedef_map names)
            ~second:(elab' typedef_map names) )
  | Case (e, (x1, e1), (x2, e2)) ->
      let e = elab' typedef_map names e in
      let x1, x1_names = bind names ~var:x1 in
      let e1 = elab' typedef_map x1_names e1 in
      let x2, x2_names = bind names ~var:x2 in
      let e2 = elab' typedef_map x2_names e2 in
      Case (e, (x1, e1), (x2, e2))
  | Scase (e, e1, (x1, x2, e2)) ->
      let e = elab' typedef_map names e in
      let e1 = elab' typedef_map names e1 in
      let x1, names = bind names ~var:x1 in
      let x2, names = bind names ~var:x2 in
      let e2 = elab' typedef_map names e2 in
      Scase (e, e1, (x1, x2, e2))
  | List (tp, l) ->
      let expanded_tp = expand_type typedef_map tp in
      List.fold_right l
        ~f:(fun e acc -> LExpr.Cons (Diamond, elab' typedef_map names e, acc))
        ~init:(LExpr.Nil expanded_tp)
  | Stack (tp, l) ->
      let expanded_tp = expand_type typedef_map tp in
      List.fold_right l
        ~f:(fun e acc -> LExpr.Scons (elab' typedef_map names e, acc))
        ~init:(LExpr.Snil expanded_tp)

(* Build typedef map from program and elaborate with it *)
let build_typedef_map prog =
  List.fold prog ~init:String.Map.empty ~f:(fun acc defn ->
      match defn with
      | LDefn.Typedef (name, ty) ->
          Map.set acc ~key:name ~data:ty
      | _ ->
          acc )

let elab prog t =
  let typedef_map = build_typedef_map prog in
  elab' typedef_map String.Map.empty t
