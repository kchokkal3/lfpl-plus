open! Core
open Angstrom
open Ast

(* Start of util functions *)
let is_whitespace = function
  | '\x20' | '\x0a' | '\x0d' | '\x09' ->
      true
  | _ ->
      false

let comment =
  string "(*" *>
  skip_many (
    (char '*' *> peek_char >>= function
      | Some ')' -> fail "end"
      | _ -> return ())
    <|> skip (fun c -> not (Char.equal c '*'))
  ) *>
  string "*)" *> return ()

let ws_char = skip is_whitespace

let whitespace = skip_many (ws_char <|> comment)

let force_whitespace = skip_many1 (ws_char <|> comment)

let parens p = char '(' *> whitespace *> p <* whitespace <* char ')'

let brackets p = char '[' *> whitespace *> p <* whitespace <* char ']'

let pipe_brackets p =
  string "[|" *> whitespace *> p <* whitespace <* string "|]"

let braces p = char '{' *> whitespace *> p <* whitespace <* char '}'

let chainl1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op e >>= go <|> return acc in
  e >>= fun init -> go init

let chainr1 e op =
  let rec go acc = lift2 (fun f x -> f acc x) op (e >>= go) <|> return acc in
  e >>= fun init -> go init

let uchain1 e op =
  let rec go acc = lift (fun f -> f acc) op >>= go <|> return acc in
  e >>= fun init -> go init

(* End of util functions *)

let diamond_type = string "<>" *> return LType.Diamond

let unit_type = string "1" *> return LType.Unit

let list_type =
  force_whitespace *> string "list" *> return (fun x -> LType.List x)

let stack_type =
  force_whitespace *> string "stack" *> return (fun x -> LType.Stack x)

let tree_type =
  force_whitespace *> string "tree" *> return (fun x -> LType.Tree x)

let func_type =
  whitespace *> string "-@" *> whitespace
  *> return (fun x y -> LType.Fun (x, y))

let sfunc_type =
  whitespace *> string "->" *> whitespace
  *> return (fun x y -> LType.Sfun (x, y))

let prod_type =
  whitespace *> string "*" *> whitespace
  *> return (fun x y -> LType.Prod (x, y))

let sum_type =
  whitespace *> string "+" *> whitespace *> return (fun x y -> LType.Sum (x, y))

let singular = diamond_type <|> unit_type

(* type_parser will be defined after ident *)

let pp_parse_f f sexp_of s =
  let res = parse_string ~consume:All f s in
  print_endline
    (Sexp.to_string_hum (Result.sexp_of_t sexp_of String.sexp_of_t res))

(** An ident can contain alphanumeric characters, underscores and apostrophes.
    However, it cannot start with a number or an apostrophe. *)
let ident =
  whitespace
  *> lift2
       (fun h t -> Char.to_string h ^ t)
       (satisfy (fun c -> Char.is_alpha c || Char.equal '_' c))
       (take_while (fun c ->
            Char.is_alphanum c || Char.equal '_' c || Char.equal '\'' c ) )
  >>= fun v ->
  match v with
  | "list"
  | "stack"
  | "tree"
  | "in"
  | "lrec"
  | "case"
  | "let"
  | "defn"
  | "decl"
  | "typedef"
  | "val"
  | "cons"
  | "snil"
  | "nil"
  | "null"
  | "fn"
  | "sfn" ->
      fail [%string "%{v} is a keyword but used as a variable name"]
  | _ ->
      return v

(* Now define type_parser with access to ident *)
let type_alias = lift (fun name -> LType.TypeAlias name) ident

(* Type parser that doesn't allow type aliases (for typedef RHS) *)
let primitive_type_parser =
  fix (fun tp ->
      let atom = parens tp <|> singular in
      let container = uchain1 atom (list_type <|> stack_type <|> tree_type) in
      let pterm = chainl1 container prod_type in
      let sterm = chainl1 pterm sum_type in
      let fterm = chainr1 sterm (func_type <|> sfunc_type) in
      fterm )

(* Type parser that allows type aliases *)
let type_parser =
  fix (fun tp ->
      let atom = parens tp <|> singular <|> type_alias in
      let container = uchain1 atom (list_type <|> stack_type <|> tree_type) in
      let pterm = chainl1 container prod_type in
      let sterm = chainl1 pterm sum_type in
      let fterm = chainr1 sterm (func_type <|> sfunc_type) in
      fterm )

let pp_parse_type = pp_parse_f type_parser LType.sexp_of_t

let var_expr = lift (fun x -> LExpr.Var (x, None)) ident

let diamond_expr = string "<*>" *> return LExpr.Diamond

let null_expr = string "()" *> return LExpr.Null

let nil_expr = lift (fun t -> LExpr.Nil t) (string "nil" *> brackets type_parser)

let snil_expr =
  lift (fun t -> LExpr.Snil t) (string "snil" *> brackets type_parser)

let leaf_expr =
  lift (fun t -> LExpr.Leaf t) (string "leaf" *> brackets type_parser)

(* An annotation is (x : t) for some ident x and some type t *)
let annotation =
  parens (both (ident <* whitespace <* char ':') (whitespace *> type_parser))

(* fn (x : t). e *)
let func_expr f =
  lift2
    (fun (x, t) e -> LExpr.Lam ((x, None), t, e))
    (string "fn" *> whitespace *> annotation <* char '.' <* whitespace)
    f

(* sfn (x : t). e *)
let sfunc_expr f =
  lift2
    (fun (x, t) e -> LExpr.Slam ((x, None), t, e))
    (string "sfn" *> whitespace *> annotation <* char '.' <* whitespace)
    f

(* A cons is cons(e1; e2; e3) *)
let cons_expr f =
  string "cons"
  *> parens
       (lift3
          (fun e1 e2 e3 -> LExpr.Cons (e1, e2, e3))
          (f <* whitespace <* char ';')
          (whitespace *> f <* whitespace <* char ';')
          (whitespace *> f) )

(* A node is node(e1; e2; e3; e4) *)
let node_expr f =
  string "node"
  *> parens
       (lift4
          (fun e1 e2 e3 e4 -> LExpr.Node (e1, e2, e3, e4))
          (f <* whitespace <* char ';')
          (whitespace *> f <* whitespace <* char ';')
          (whitespace *> f <* whitespace <* char ';')
          (whitespace *> f) )

(* A scons is scons(e2; e3) *)
let scons_expr f =
  string "scons"
  *> parens
       (lift2
          (fun e1 e2 -> LExpr.Scons (e1, e2))
          (f <* whitespace <* char ';')
          (whitespace *> f) )

(* This is just both but for four arguments *)
let all4 a b c d = lift4 (fun a b c d -> (a, b, c, d)) a b c d

(* This is for five arguments *)
let all5 a b c d e =
  lift (fun ((a, b, c, d), e) -> (a, b, c, d, e)) (both (all4 a b c d) e)

(* lrec e{e1 | x1,x2,y.e2} *)
let lrec_expr f =
  lift2
    (fun e (e1, (x1, x2, y, e2)) ->
      LExpr.Lrec (e, e1, ((x1, None), (x2, None), (y, None), e2)) )
    (string "lrec" *> force_whitespace *> f)
    ( whitespace
    *> braces
         (both
            (f <* whitespace <* char '|')
            (all4
               (whitespace *> ident <* whitespace <* char ',')
               (whitespace *> ident <* whitespace <* char ',')
               (whitespace *> ident <* whitespace <* char '.')
               (whitespace *> f) ) ) )

(* trec e{e1 | x1,y1,x2,y2.e2} where x1=d, y1=left_rec, x2=elem, y2=right_rec *)
let trec_expr f =
  lift2
    (fun e (e1, (x1, y1, x2, y2, e2)) ->
      LExpr.Trec (e, e1, ((x1, None), (y1, None), (x2, None), (y2, None), e2)) )
    (string "trec" *> force_whitespace *> f)
    ( whitespace
    *> braces
         (both
            (f <* whitespace <* char '|')
            (all5
               (whitespace *> ident <* whitespace <* char ',')
               (whitespace *> ident <* whitespace <* char ',')
               (whitespace *> ident <* whitespace <* char ',')
               (whitespace *> ident <* whitespace <* char '.')
               (whitespace *> f) ) ) )

(* (x, y) *)
let pair_expr f =
  parens
    (lift2
       (fun x y -> LExpr.Pair (x, y))
       (f <* whitespace <* char ',')
       (whitespace *> f) )

(* letp (x1, x2) = e1 in e2 *)
let letp_expr f =
  lift3
    (fun (x1, x2) e1 e2 -> LExpr.Letp (e1, ((x1, None), (x2, None), e2)))
    ( string "letp" *> whitespace
      *> parens (both (ident <* whitespace <* char ',') (whitespace *> ident))
    <* whitespace <* char '=' )
    (whitespace *> f <* force_whitespace <* string "in")
    (force_whitespace *> f)

(* [t1; t2](1.e) or [t1; t2](2.e) *)
let inj_expr f =
  let left =
    lift2
      (fun (t1, t2) e -> LExpr.Inj ((t1, t2), First e))
      (brackets
         (both
            (type_parser <* whitespace <* char ';')
            (whitespace *> type_parser) ) )
      (parens (char '1' *> whitespace *> char '.' *> whitespace *> f))
  in
  let right =
    lift2
      (fun (t1, t2) e -> LExpr.Inj ((t1, t2), Second e))
      (brackets
         (both
            (type_parser <* whitespace <* char ';')
            (whitespace *> type_parser) ) )
      (parens (char '2' *> whitespace *> char '.' *> whitespace *> f))
  in
  choice [left; right]

(* case e {x1.e1 | x2.e2} *)
let case_expr f =
  lift2
    (fun e ((x1, e1), (x2, e2)) ->
      LExpr.Case (e, ((x1, None), e1), ((x2, None), e2)) )
    (string "case" *> force_whitespace *> f)
    ( whitespace
    *> braces
         (both
            (both
               (ident <* whitespace <* char '.')
               (whitespace *> f <* whitespace <* char '|') )
            (both (ident <* whitespace <* char '.') (whitespace *> f)) ) )

(* scase e {e1 | x1, x2.e2} *)
let scase_expr f =
  lift2
    (fun e (e1, ((x1, x2), e2)) ->
      LExpr.Scase (e, e1, ((x1, None), (x2, None), e2)) )
    (string "scase" *> force_whitespace *> f)
    ( whitespace
    *> braces
         (both
            (whitespace *> f <* whitespace <* char '|')
            (both
               (both
                  (ident <* whitespace <* char ',')
                  (ident <* whitespace <* char '.') )
               (whitespace *> f) ) ) )

(* [type][e1; e2; e3] *)
let list_expr f =
  lift2
    (fun typ elems -> LExpr.List (typ, elems))
    (brackets type_parser)
    (brackets (sep_by (whitespace *> char ';' *> whitespace) f))

(* [type][|e1; e2; e3|] *)
let stack_expr f =
  lift2
    (fun typ elems -> LExpr.Stack (typ, elems))
    (brackets type_parser)
    (pipe_brackets (sep_by (whitespace *> char ';' *> whitespace) f))

let chainl1_wrap e f =
  let rec go acc =
    lift (fun x -> f acc x) (whitespace *> e) >>= go <|> return acc
  in
  e >>= fun init -> go init

let expr_parser =
  fix (fun expr ->
      let term =
        choice
          [ func_expr expr
          ; sfunc_expr expr
          ; cons_expr expr
          ; node_expr expr
          ; scons_expr expr
          ; lrec_expr expr
          ; trec_expr expr
          ; letp_expr expr
          ; pair_expr expr
          ; case_expr expr
          ; inj_expr expr
          ; parens expr
          ; list_expr expr
          ; stack_expr expr
          ; nil_expr
          ; snil_expr
          ; scase_expr expr
          ; leaf_expr
          ; null_expr
          ; diamond_expr
          ; var_expr ]
      in
      chainl1_wrap term (fun x y -> LExpr.App (x, y)) )

let decl_parser =
  (fun name tp -> LDefn.Decl (name, tp))
  <$> string "decl" *> whitespace *> ident
  <* whitespace <* char ':' <* whitespace <*> type_parser

let defn_parser =
  (fun name expr -> LDefn.Defn (name, expr))
  <$> string "defn" *> whitespace *> ident
  <* whitespace <* char '=' <* whitespace <*> expr_parser

let typedef_parser =
  (fun name tp -> LDefn.Typedef (name, tp))
  <$> string "typedef" *> whitespace *> ident
  <* whitespace <* char '=' <* whitespace <*> primitive_type_parser

let val_parser =
  (fun expr -> LDefn.Val expr)
  <$> string "val" *> force_whitespace *> expr_parser

let prog_parser = whitespace *>
  sep_by force_whitespace (choice [decl_parser; defn_parser; typedef_parser; val_parser])
  <* whitespace

let parse str =
  parse_string ~consume:All prog_parser str
  |> Result.map_error ~f:Error.of_string

let parse_expr str =
  parse_string ~consume:All expr_parser str
  |> Result.map_error ~f:Error.of_string

let pp_parse_expr = pp_parse_f expr_parser LExpr.sexp_of_t
