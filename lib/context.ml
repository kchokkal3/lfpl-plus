open! Core
open! Ast
open! Or_error.Let_syntax

module Binding = struct
  type status = Bound | Read [@@deriving sexp_of]

  type t = LType.t * status option [@@deriving sexp_of]
end

let rec is_diamond_free tp =
  match tp with
  | LType.Unit | LType.Sfun _ ->
      true
  | LType.Prod (tau1, tau2) | LType.Sum (tau1, tau2) ->
      is_diamond_free tau1 && is_diamond_free tau2
  | LType.Stack tau ->
      is_diamond_free tau
  | _ ->
      false

module Key = Var

(* Diamond-free, non-diamond-free *)
type t =
  { dmd_free_ctx: (Key.t, Binding.t) Hashtbl.t
  ; dmd_ctx: (Key.t, Binding.t) Hashtbl.t
  ; latest_dmds: Key.t Stack.t
  ; check_diamonds: bool }

let create ?(check_diamonds = false) () =
  { dmd_free_ctx= Hashtbl.create (module Key)
  ; dmd_ctx= Hashtbl.create (module Key)
  ; latest_dmds= Stack.create ()
  ; check_diamonds }

let duplicate_dmd_free ctx =
  { dmd_free_ctx= ctx.dmd_free_ctx
  ; check_diamonds= ctx.check_diamonds
  ; latest_dmds= Stack.create ()
  ; dmd_ctx= Hashtbl.create (module Key) }

let duplicate ctx =
  { dmd_free_ctx= ctx.dmd_free_ctx
  ; dmd_ctx= Hashtbl.copy ctx.dmd_ctx
  ; latest_dmds= ctx.latest_dmds
  ; check_diamonds= ctx.check_diamonds }

let of_defns ?(check_diamonds = false) l : t =
  { dmd_free_ctx=
      List.Assoc.map l ~f:(fun tp ->
          (tp, Option.some_if (not (is_diamond_free tp)) Binding.Bound) )
      |> Hashtbl.of_alist_exn (module Var)
  ; dmd_ctx= Hashtbl.create (module Key)
  ; latest_dmds= Stack.create ()
  ; check_diamonds }

let add (ctx : t) (key : Key.t) (value : LType.t) : unit Or_error.t =
  let diamond_free = is_diamond_free value in
  if LType.equal Diamond value then Stack.push ctx.latest_dmds key ;
  let ctx = if diamond_free then ctx.dmd_free_ctx else ctx.dmd_ctx in
  match
    Hashtbl.add ctx ~key
      ~data:(value, Option.some_if (not diamond_free) Binding.Bound)
  with
  | `Ok ->
      Ok ()
  | `Duplicate ->
      Or_error.error_string
        [%string "duplicate variable %{Var.sexp_of_t key |> Sexp.to_string}"]

let find (ctx : t) (key : Key.t) : Binding.t option =
  Option.first_some
    (Hashtbl.find ctx.dmd_free_ctx key)
    (Hashtbl.find ctx.dmd_ctx key)

let remove (ctx : t) (key : Key.t) : unit Or_error.t =
  let binding = Hashtbl.find ctx.dmd_free_ctx key in
  match binding with
  | None -> (
      let binding = Hashtbl.find ctx.dmd_ctx key in
      match binding with
      | None ->
          Or_error.error_string "No such binding"
      | Some (tp, _) ->
          Hashtbl.remove ctx.dmd_ctx key ;
          if LType.equal tp Diamond then
            match Stack.pop ctx.latest_dmds with
            | Some k when Key.equal k key ->
                Ok ()
            | _ ->
                Or_error.error_string "Top of latest_dmds stack is incorrect"
          else Ok () )
  | Some _ ->
      Hashtbl.remove ctx.dmd_free_ctx key ;
      Ok ()

let read (ctx : t) (key : Key.t) : unit Or_error.t =
  let binding = Hashtbl.find ctx.dmd_free_ctx key in
  match binding with
  | None -> (
      let binding = Hashtbl.find ctx.dmd_ctx key in
      match binding with
      | None ->
          Or_error.error_string "No such binding"
      | Some (t, _) ->
          Hashtbl.set ctx.dmd_ctx ~key ~data:(t, Some Read) ;
          Ok () )
  | Some _ ->
      Ok ()

let read_latest_dmd (ctx : t) : unit Or_error.t =
  match ctx.check_diamonds with
  | false ->
      Ok ()
  | true ->
      let%bind available_diamond =
        Stack.fold_until ctx.latest_dmds ~init:()
          ~f:(fun () k ->
            match Hashtbl.find ctx.dmd_ctx k with
            | None ->
                Stop
                  (Or_error.error_string "Diamond in latest_dmds not in dmd_ctx")
            | Some (_, binding) -> (
              match Option.value_exn binding with
              | Read ->
                  Continue ()
              | Bound ->
                  Stop (Ok k) ) )
          ~finish:
            (Fn.const
               (Or_error.error_string
                  "Diamond elision could not find usable diamond" ) )
      in
      read ctx available_diamond

(* Merge function for sum case. 
    If a variable is read in either e1 or e2 context, 
    mark it as read in the original context. *)
let merge (ctx : t) (e1_ctx : t) (e2_ctx : t) : unit =
  let dmd_ctx = ctx.dmd_ctx in
  let e1_dmd_ctx = e1_ctx.dmd_ctx in
  let e2_dmd_ctx = e2_ctx.dmd_ctx in
  let keys_to_update = ref [] in
  Hashtbl.iteri dmd_ctx ~f:(fun ~key ~data:_ ->
      match (Hashtbl.find e1_dmd_ctx key, Hashtbl.find e2_dmd_ctx key) with
      | Some (tp, Some Read), _ | _, Some (tp, Some Read) ->
          keys_to_update := (key, tp) :: !keys_to_update
      | _ ->
          () ) ;
  List.iter !keys_to_update ~f:(fun (key, tp) ->
      Hashtbl.set dmd_ctx ~key ~data:(tp, Some Read) )
