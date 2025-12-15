open! Core
open! Format
open Ast

let indent = 4

let box ppf s = open_box indent ; pp_print_string ppf s ; close_box ()

let rec format_string' ppf (t : LExpr.t) =
  match t with
  | Diamond ->
      box ppf "<*>"
  | Var x ->
      box ppf (Var.to_string_hum x)
  | Lam (x, t, e) ->
      open_box indent ;
      pp_print_string ppf
        [%string "fn (%{Var.to_string_hum x} : %{LType.to_string_hum t})."] ;
      pp_print_space ppf () ;
      format_string' ppf e ;
      close_box ()
  | Slam (x, t, e) ->
      open_box indent ;
      pp_print_string ppf
        [%string "sfn (%{Var.to_string_hum x} : %{LType.to_string_hum t})."] ;
      pp_print_space ppf () ;
      format_string' ppf e ;
      close_box ()
  | App (f, s) ->
      open_box indent ;
      format_string' ppf f ;
      pp_print_space ppf () ;
      format_string' ppf s ;
      close_box ()
  | Nil tp ->
      box ppf [%string "nil[%{LType.to_string_hum tp}]"]
  | Cons (d, x, e) ->
      open_box indent ;
      pp_print_string ppf "cons(" ;
      format_string' ppf d ;
      pp_print_char ppf ';' ;
      pp_print_space ppf () ;
      format_string' ppf x ;
      pp_print_char ppf ';' ;
      pp_print_space ppf () ;
      format_string' ppf e ;
      pp_print_char ppf ')' ;
      close_box ()
  | Leaf tp ->
      box ppf [%string "leaf[%{LType.to_string_hum tp}]"]
  | Node (d, l, x, r) ->
      open_box indent ;
      pp_print_string ppf "node(" ;
      format_string' ppf d ;
      pp_print_char ppf ';' ;
      pp_print_space ppf () ;
      format_string' ppf l ;
      pp_print_char ppf ';' ;
      pp_print_space ppf () ;
      format_string' ppf x ;
      pp_print_char ppf ';' ;
      pp_print_space ppf () ;
      format_string' ppf r ;
      pp_print_char ppf ')' ;
      close_box ()
  | Snil tp ->
      box ppf [%string "snil[%{LType.to_string_hum tp}]"]
  | Scons (x, e) ->
      open_box indent ;
      pp_print_string ppf "scons(" ;
      format_string' ppf x ;
      pp_print_char ppf ';' ;
      pp_print_space ppf () ;
      format_string' ppf e ;
      pp_print_char ppf ')' ;
      close_box ()
  | Lrec (e, e1, (x1, x2, y, e2)) ->
      open_box indent ;
      pp_print_string ppf "lrec " ;
      format_string' ppf e ;
      pp_print_space ppf () ;
      pp_print_char ppf '{' ;
      open_hovbox indent ;
      format_string' ppf e1 ;
      close_box () ;
      pp_print_space ppf () ;
      pp_print_string ppf
        [%string
          "| %{Var.to_string_hum x1}, %{Var.to_string_hum x2}, \
           %{Var.to_string_hum y}."] ;
      pp_print_space ppf () ;
      open_hovbox indent ;
      format_string' ppf e2 ;
      close_box () ;
      pp_print_char ppf '}' ;
      close_box ()
  | Trec (e, e1, (x1, y1, x2, y2, e2)) ->
      open_box indent ;
      pp_print_string ppf "trec " ;
      format_string' ppf e ;
      pp_print_space ppf () ;
      pp_print_char ppf '{' ;
      open_hovbox indent ;
      format_string' ppf e1 ;
      close_box () ;
      pp_print_space ppf () ;
      pp_print_string ppf
        [%string
          "| %{Var.to_string_hum x1}, %{Var.to_string_hum y1}, \
           %{Var.to_string_hum x2}, %{Var.to_string_hum y2}."] ;
      pp_print_space ppf () ;
      open_hovbox indent ;
      format_string' ppf e2 ;
      close_box () ;
      pp_print_char ppf '}' ;
      close_box ()
  | Pair (f, s) ->
      open_box indent ;
      pp_print_char ppf '(' ;
      format_string' ppf f ;
      pp_print_char ppf ',' ;
      pp_print_space ppf () ;
      format_string' ppf s ;
      pp_print_char ppf ')' ;
      close_box ()
  | Letp (e, (f, s, e1)) ->
      open_box indent ;
      pp_print_string ppf
        [%string "letp (%{Var.to_string_hum f}, %{Var.to_string_hum s}) ="] ;
      pp_print_space ppf () ;
      open_hovbox indent ;
      format_string' ppf e ;
      close_box () ;
      pp_print_space ppf () ;
      pp_print_string ppf "in" ;
      pp_print_space ppf () ;
      open_hovbox indent ;
      format_string' ppf e1 ;
      close_box () ;
      close_box ()
  | Null ->
      box ppf "()"
  | Inj ((f_tp, s_tp), First e) ->
      open_box indent ;
      pp_print_char ppf '[' ;
      pp_print_string ppf [%string "%{LType.to_string_hum f_tp}"] ;
      pp_print_char ppf ';' ;
      pp_print_space ppf () ;
      pp_print_string ppf [%string "%{LType.to_string_hum s_tp}"] ;
      pp_print_string ppf "](1." ;
      open_hovbox indent ;
      pp_print_char ppf '(' ;
      format_string' ppf e ;
      pp_print_char ppf ')' ;
      close_box () ;
      pp_print_char ppf ')' ;
      close_box ()
  | Inj ((f_tp, s_tp), Second e) ->
      open_box indent ;
      pp_print_char ppf '[' ;
      pp_print_string ppf [%string "%{LType.to_string_hum f_tp}"] ;
      pp_print_char ppf ';' ;
      pp_print_space ppf () ;
      pp_print_string ppf [%string "%{LType.to_string_hum s_tp}"] ;
      pp_print_string ppf "](2." ;
      open_hovbox indent ;
      pp_print_char ppf '(' ;
      format_string' ppf e ;
      pp_print_char ppf ')' ;
      close_box () ;
      pp_print_char ppf ')' ;
      close_box ()
  | Case (e, (x1, e1), (x2, e2)) ->
      open_box indent ;
      pp_print_string ppf "case " ;
      format_string' ppf e ;
      pp_print_space ppf () ;
      pp_print_string ppf "{" ;
      pp_print_space ppf () ;
      open_hvbox 0 ;
      open_hovbox 0 ;
      pp_print_string ppf [%string "%{Var.to_string_hum x1}."] ;
      pp_print_space ppf () ;
      format_string' ppf e1 ;
      close_box () ;
      pp_print_space ppf () ;
      open_hovbox 0 ;
      pp_print_string ppf [%string "| %{Var.to_string_hum x2}."] ;
      pp_print_space ppf () ;
      format_string' ppf e2 ;
      close_box () ;
      close_box () ;
      pp_print_char ppf '}' ;
      close_box ()
  | Scase (e, e1, (x1, x2, e2)) ->
      open_box indent ;
      pp_print_string ppf "scase " ;
      format_string' ppf e ;
      pp_print_space ppf () ;
      pp_print_string ppf "{" ;
      pp_print_space ppf () ;
      open_hvbox 0 ;
      open_hovbox 0 ;
      format_string' ppf e1 ;
      close_box () ;
      pp_print_space ppf () ;
      open_hovbox 0 ;
      pp_print_string ppf
        [%string "| %{Var.to_string_hum x1}, %{Var.to_string_hum x2}."] ;
      pp_print_space ppf () ;
      format_string' ppf e2 ;
      close_box () ;
      close_box () ;
      pp_print_char ppf '}' ;
      close_box ()
  | List (typ, elems) ->
      open_box indent ;
      pp_print_char ppf '[' ;
      open_hovbox indent ;
      pp_print_string ppf [%string "%{LType.to_string_hum typ}"] ;
      close_box () ;
      pp_print_char ppf ']' ;
      pp_print_char ppf '[' ;
      pp_print_list
        ~pp_sep:(fun ppf () -> pp_print_char ppf ';' ; pp_print_space ppf ())
        (fun ppf elem ->
          open_hovbox indent ; format_string' ppf elem ; close_box () )
        ppf elems ;
      pp_print_char ppf ']' ;
      close_box ()
  | Stack (typ, elems) ->
      open_box indent ;
      pp_print_char ppf '[' ;
      open_hovbox indent ;
      pp_print_string ppf [%string "%{LType.to_string_hum typ}"] ;
      close_box () ;
      pp_print_char ppf ']' ;
      pp_print_string ppf "[|" ;
      pp_print_list
        ~pp_sep:(fun ppf () -> pp_print_char ppf ';' ; pp_print_space ppf ())
        (fun ppf elem ->
          open_hovbox indent ; format_string' ppf elem ; close_box () )
        ppf elems ;
      pp_print_string ppf "|]" ;
      close_box ()

let format_string expr =
  let formatter = std_formatter in
  Format.safe_set_geometry ~max_indent:60 ~margin:80 ;
  format_string' formatter expr ;
  Format.pp_print_flush formatter ()
