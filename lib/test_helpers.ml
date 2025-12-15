open! Core
open! Ast

let pp_synthesize_tp_no_elab s =
  let expr_res = Parser.parse_expr s in
  match expr_res with
  | Error e ->
      print_endline (Sexp.to_string_hum (Error.sexp_of_t e))
  | Ok expr ->
      let tp_res = Typechecker.synthesize_tp ~ctx:(Context.create ()) ~expr in
      print_endline
        (Sexp.to_string_hum (Or_error.sexp_of_t LType.sexp_of_t tp_res))

let pp_typecheck_no_elab s tp =
  let expr_res = Parser.parse_expr s in
  match expr_res with
  | Error e ->
      print_endline (Sexp.to_string_hum (Error.sexp_of_t e))
  | Ok expr ->
      let tc_res = Typechecker.typecheck ~ctx:(Context.create ()) ~expr ~tp in
      print_endline
        (Sexp.to_string_hum (Or_error.sexp_of_t Unit.sexp_of_t tc_res))

let pp_synthesize_tp s =
  let expr_res = Parser.parse_expr s in
  match expr_res with
  | Error e ->
      print_endline (Sexp.to_string_hum (Error.sexp_of_t e))
  | Ok expr ->
      let elaborated = Elab.elab [] expr in
      let tp_res =
        Typechecker.synthesize_tp ~ctx:(Context.create ()) ~expr:elaborated
      in
      print_endline
        (Sexp.to_string_hum (Or_error.sexp_of_t LType.sexp_of_t tp_res))

let pp_typecheck s tp =
  let expr_res = Parser.parse_expr s in
  match expr_res with
  | Error e ->
      print_endline (Sexp.to_string_hum (Error.sexp_of_t e))
  | Ok expr ->
      let elaborated = Elab.elab [] expr in
      let tc_res =
        Typechecker.typecheck ~ctx:(Context.create ()) ~expr:elaborated ~tp
      in
      print_endline
        (Sexp.to_string_hum (Or_error.sexp_of_t Unit.sexp_of_t tc_res))
