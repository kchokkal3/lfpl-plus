open Lfpl_lib.Parser

(* Types *)

(* Basic types *)
let%expect_test "diamond and unit types" =
  pp_parse_type "<>" ;
  pp_parse_type "(<>)" ;
  pp_parse_type "1" ;
  pp_parse_type "(1)" ;
  [%expect
    {|
    (Ok Diamond)
    (Ok Diamond)
    (Ok Unit)
    (Ok Unit)
    |}]

(* List types *)
let%expect_test "list type constructor" =
  pp_parse_type "<> list" ;
  pp_parse_type "1 list" ;
  pp_parse_type "1list" ;
  pp_parse_type "(<>) list" ;
  pp_parse_type "(1) list" ;
  pp_parse_type "((1) list) list" ;
  pp_parse_type "1 list list" ;
  [%expect
    {|
    (Ok (List Diamond))
    (Ok (List Unit))
    (Error ": end_of_input")
    (Ok (List Diamond))
    (Ok (List Unit))
    (Ok (List (List Unit)))
    (Ok (List (List Unit)))
    |}]

(* Stack types *)
let%expect_test "Stack type constructor" =
  pp_parse_type "<> stack" ;
  pp_parse_type "1 stack" ;
  pp_parse_type "1stack" ;
  pp_parse_type "(<>) stack" ;
  pp_parse_type "(1) stack" ;
  pp_parse_type "((1) stack) stack" ;
  pp_parse_type "1 stack stack" ;
  [%expect
    {|
    (Ok (Stack Diamond))
    (Ok (Stack Unit))
    (Error ": end_of_input")
    (Ok (Stack Diamond))
    (Ok (Stack Unit))
    (Ok (Stack (Stack Unit)))
    (Ok (Stack (Stack Unit)))
    |}]

(* Function types *)
let%expect_test "function types" =
  pp_parse_type "1 -@ 1" ;
  pp_parse_type "1 -@ 1 -@ 1" ;
  pp_parse_type "1* 1 -@ 1" ;
  pp_parse_type "1 (list list)" ;
  pp_parse_type "(1 -@ 1) -@ 1" ;
  [%expect
    {|
    (Ok (Fun (Unit Unit)))
    (Ok (Fun (Unit (Fun (Unit Unit)))))
    (Ok (Fun ((Prod (Unit Unit)) Unit)))
    (Error ": end_of_input")
    (Ok (Fun ((Fun (Unit Unit)) Unit)))
    |}]

(* Sum types *)
let%expect_test "sum types" =
  pp_parse_type "1 + 1" ;
  pp_parse_type "1 + 1 + 1" ;
  pp_parse_type "1 + 1 -@ 1" ;
  pp_parse_type "1 + 1 * 1" ;
  [%expect
    {|
    (Ok (Sum (Unit Unit)))
    (Ok (Sum ((Sum (Unit Unit)) Unit)))
    (Ok (Fun ((Sum (Unit Unit)) Unit)))
    (Ok (Sum (Unit (Prod (Unit Unit)))))
    |}]

(* Structural function types *)
let%expect_test "structural function types" =
  pp_parse_type "1 -> 1" ;
  pp_parse_type "1 -> 1 -> 1" ;
  pp_parse_type "<> -> 1" ;
  pp_parse_type "(1 -> 1) -> 1" ;
  pp_parse_type "1 -@ 1 ->1" ;
  pp_parse_type "1->1 -@ 1" ;
  [%expect
    {|
    (Ok (Sfun (Unit Unit)))
    (Ok (Sfun (Unit (Sfun (Unit Unit)))))
    (Ok (Sfun (Diamond Unit)))
    (Ok (Sfun ((Sfun (Unit Unit)) Unit)))
    (Ok (Fun (Unit (Sfun (Unit Unit)))))
    (Ok (Sfun (Unit (Fun (Unit Unit)))))
    |}]

(* Complex type combinations *)
let%expect_test "complex types" =
  pp_parse_type "1 list list -@ <> -@ (1 -@ 1) -@ (<> * 1) list" ;
  [%expect
    {|
    (Ok
     (Fun
      ((List (List Unit))
       (Fun (Diamond (Fun ((Fun (Unit Unit)) (List (Prod (Diamond Unit))))))))))
    |}]

(* Expressions *)

(* Variables and identifiers *)
let%expect_test "variable names" =
  pp_parse_expr "x" ;
  pp_parse_expr "x_" ;
  pp_parse_expr "_x" ;
  pp_parse_expr "__" ;
  pp_parse_expr "x_1" ;
  pp_parse_expr "x1" ;
  pp_parse_expr "let" ;
  [%expect
    {|
    (Ok (Var (x ())))
    (Ok (Var (x_ ())))
    (Ok (Var (_x ())))
    (Ok (Var (__ ())))
    (Ok (Var (x_1 ())))
    (Ok (Var (x1 ())))
    (Error ": no more choices")
    |}]

(* Null and lambda expressions *)
let%expect_test "null and lambda" =
  pp_parse_expr "()" ;
  pp_parse_expr "fn (x:1).x" ;
  pp_parse_expr "fn ( x :1).x" ;
  pp_parse_expr "fn (x: 1). x" ;
  pp_parse_expr "fn(x: 1). x" ;
  pp_parse_expr "fn(x: 1). fn (y:1). y" ;
  [%expect
    {|
    (Ok Null)
    (Ok (Lam ((x ()) Unit (Var (x ())))))
    (Ok (Lam ((x ()) Unit (Var (x ())))))
    (Ok (Lam ((x ()) Unit (Var (x ())))))
    (Ok (Lam ((x ()) Unit (Var (x ())))))
    (Ok (Lam ((x ()) Unit (Lam ((y ()) Unit (Var (y ())))))))
    |}]

(* Structural lambda expressions *)
let%expect_test "structural lambda" =
  pp_parse_expr "sfn (x:1).x" ;
  pp_parse_expr "sfn ( x :1).x" ;
  pp_parse_expr "sfn (x: 1). x" ;
  pp_parse_expr "sfn(x: 1). x" ;
  pp_parse_expr "sfn(x: <>). sfn (y:1). y" ;
  pp_parse_expr "sfn(x: 1). fn (y:1). x" ;
  [%expect
    {|
    (Ok (Slam ((x ()) Unit (Var (x ())))))
    (Ok (Slam ((x ()) Unit (Var (x ())))))
    (Ok (Slam ((x ()) Unit (Var (x ())))))
    (Ok (Slam ((x ()) Unit (Var (x ())))))
    (Ok (Slam ((x ()) Diamond (Slam ((y ()) Unit (Var (y ())))))))
    (Ok (Slam ((x ()) Unit (Lam ((y ()) Unit (Var (x ())))))))
    |}]

(* Application *)
let%expect_test "application" =
  pp_parse_expr "x (x)" ;
  pp_parse_expr "x (x) (x)" ;
  pp_parse_expr "(fn(x:1). x) (x)" ;
  pp_parse_expr "fn(x:1). x (x)" ;
  [%expect
    {|
    (Ok (App ((Var (x ())) (Var (x ())))))
    (Ok (App ((App ((Var (x ())) (Var (x ())))) (Var (x ())))))
    (Ok (App ((Lam ((x ()) Unit (Var (x ())))) (Var (x ())))))
    (Ok (Lam ((x ()) Unit (App ((Var (x ())) (Var (x ())))))))
    |}]

(* List constructors *)
let%expect_test "cons expressions" =
  pp_parse_expr "cons(x;x;x)" ;
  pp_parse_expr "cons(x; x; x)" ;
  pp_parse_expr "cons(x; x; cons(x; y;d))" ;
  [%expect
    {|
    (Ok (Cons ((Var (x ())) (Var (x ())) (Var (x ())))))
    (Ok (Cons ((Var (x ())) (Var (x ())) (Var (x ())))))
    (Ok
     (Cons
      ((Var (x ())) (Var (x ())) (Cons ((Var (x ())) (Var (y ())) (Var (d ())))))))
    |}]

(* List recursion *)
let%expect_test "lrec expressions" =
  pp_parse_expr "lrec e{nil[1]|x1,x2,y. y}" ;
  pp_parse_expr "lrec e {nil[1+1]|x1,x2,y. y}" ;
  pp_parse_expr "lrec e{nil[1 list] |x1,x2,y. y}" ;
  pp_parse_expr "lrec e{nil[1]|x1, x2,y. y}" ;
  pp_parse_expr "lrec e{nil[1]|x1,x2, y. y }" ;
  pp_parse_expr "lrec e {nil[1] | x1 , x2, y. y}" ;
  [%expect
    {|
    (Ok (Lrec ((Var (e ())) (Nil Unit) ((x1 ()) (x2 ()) (y ()) (Var (y ()))))))
    (Ok
     (Lrec
      ((Var (e ())) (Nil (Sum (Unit Unit)))
       ((x1 ()) (x2 ()) (y ()) (Var (y ()))))))
    (Ok
     (Lrec
      ((Var (e ())) (Nil (List Unit)) ((x1 ()) (x2 ()) (y ()) (Var (y ()))))))
    (Ok (Lrec ((Var (e ())) (Nil Unit) ((x1 ()) (x2 ()) (y ()) (Var (y ()))))))
    (Ok (Lrec ((Var (e ())) (Nil Unit) ((x1 ()) (x2 ()) (y ()) (Var (y ()))))))
    (Ok (Lrec ((Var (e ())) (Nil Unit) ((x1 ()) (x2 ()) (y ()) (Var (y ()))))))
    |}]

(* Pairs *)
let%expect_test "pair expressions" =
  pp_parse_expr "(x,y)" ;
  pp_parse_expr "(x, y)" ;
  pp_parse_expr "(x,y )" ;
  pp_parse_expr "( x , y )" ;
  pp_parse_expr "( x,y )" ;
  [%expect
    {|
    (Ok (Pair ((Var (x ())) (Var (y ())))))
    (Ok (Pair ((Var (x ())) (Var (y ())))))
    (Ok (Pair ((Var (x ())) (Var (y ())))))
    (Ok (Pair ((Var (x ())) (Var (y ())))))
    (Ok (Pair ((Var (x ())) (Var (y ())))))
    |}]

(* Let-pair *)
let%expect_test "letp expressions" =
  pp_parse_expr "letp(x1, x2) = y in y" ;
  pp_parse_expr "letp(x1, x2) = (x, y) in y" ;
  pp_parse_expr "letp(x1, x2) = y in (x, y)" ;
  pp_parse_expr "letp (x1, x2) = y in (x, y)" ;
  [%expect
    {|
    (Ok (Letp ((Var (y ())) ((x1 ()) (x2 ()) (Var (y ()))))))
    (Ok
     (Letp ((Pair ((Var (x ())) (Var (y ())))) ((x1 ()) (x2 ()) (Var (y ()))))))
    (Ok
     (Letp ((Var (y ())) ((x1 ()) (x2 ()) (Pair ((Var (x ())) (Var (y ()))))))))
    (Ok
     (Letp ((Var (y ())) ((x1 ()) (x2 ()) (Pair ((Var (x ())) (Var (y ()))))))))
    |}]

(* Injections *)
let%expect_test "injection expressions" =
  pp_parse_expr "[1; 1](1.x)" ;
  pp_parse_expr "[1* 1; 1 list](1.(x, y))" ;
  pp_parse_expr "[1;1](1.[1;1](2. y))" ;
  pp_parse_expr "[1; <> list ](2.y)" ;
  [%expect
    {|
    (Ok (Inj ((Unit Unit) (First (Var (x ()))))))
    (Ok
     (Inj
      (((Prod (Unit Unit)) (List Unit))
       (First (Pair ((Var (x ())) (Var (y ()))))))))
    (Ok (Inj ((Unit Unit) (First (Inj ((Unit Unit) (Second (Var (y ())))))))))
    (Ok (Inj ((Unit (List Diamond)) (Second (Var (y ()))))))
    |}]

(* Case expressions *)
let%expect_test "case expressions" =
  pp_parse_expr "case x {x1.e1 | x2.e2}" ;
  pp_parse_expr "case (x) {x1.e1 | x2.e2}" ;
  pp_parse_expr "case [1; <>](1. ()) {x. () | y. ()}" ;
  [%expect
    {|
    (Ok (Case ((Var (x ())) ((x1 ()) (Var (e1 ()))) ((x2 ()) (Var (e2 ()))))))
    (Ok (Case ((Var (x ())) ((x1 ()) (Var (e1 ()))) ((x2 ()) (Var (e2 ()))))))
    (Ok (Case ((Inj ((Unit Diamond) (First Null))) ((x ()) Null) ((y ()) Null))))
    |}]

let%expect_test "parse empty list" =
  pp_parse_expr "[<>][]" ; [%expect {| (Ok (List (Diamond ()))) |}]

let%expect_test "parse single element list" =
  pp_parse_expr "[1][()]" ; [%expect {| (Ok (List (Unit (Null)))) |}]

let%expect_test "parse multi-element list" =
  pp_parse_expr "[<>][<*>; <*>; <*>]" ;
  [%expect {| (Ok (List (Diamond (Diamond Diamond Diamond)))) |}]

let%expect_test "parse list with complex type" =
  pp_parse_expr "[<> list][[<>][]; [<>][<*>]]" ;
  [%expect
    {| (Ok (List ((List Diamond) ((List (Diamond ())) (List (Diamond (Diamond))))))) |}]

let%expect_test "parse nested list expression" =
  pp_parse_expr "[1 * <>][((), <*>); ((), <*>)]" ;
  [%expect
    {|
    (Ok
     (List ((Prod (Unit Diamond)) ((Pair (Null Diamond)) (Pair (Null Diamond))))))
    |}]

let%expect_test "parse leaf expression" =
  pp_parse_expr "leaf[<>]" ; [%expect {| (Ok (Leaf Diamond)) |}]

let%expect_test "parse node expression" =
  pp_parse_expr "node(<*>; leaf[1]; (); leaf[1])" ;
  [%expect {| (Ok (Node (Diamond (Leaf Unit) Null (Leaf Unit)))) |}]

let%expect_test "parse trec expression" =
  pp_parse_expr "trec t {() | d, x, y1, y2. (y1, y2)}" ;
  [%expect
    {|
    (Ok
     (Trec
      ((Var (t ())) Null
       ((d ()) (x ()) (y1 ()) (y2 ()) (Pair ((Var (y1 ())) (Var (y2 ()))))))))
    |}]

let%expect_test "parse trec with whitespace" =
  pp_parse_expr "trec t { () | d , x , y1 , y2 . (y1, y2) }" ;
  [%expect
    {|
    (Ok
     (Trec
      ((Var (t ())) Null
       ((d ()) (x ()) (y1 ()) (y2 ()) (Pair ((Var (y1 ())) (Var (y2 ()))))))))
    |}]

(* Stack constructors *)
let%expect_test "scons expressions" =
  pp_parse_expr "scons(x;x)" ;
  pp_parse_expr "scons(x; x)" ;
  pp_parse_expr "scons(x; scons(y;d))" ;
  [%expect
    {|
    (Ok (Scons ((Var (x ())) (Var (x ())))))
    (Ok (Scons ((Var (x ())) (Var (x ())))))
    (Ok (Scons ((Var (x ())) (Scons ((Var (y ())) (Var (d ())))))))
    |}]

(* Stack eliminators *)
let%expect_test "scase expressions" =
  pp_parse_expr "scase x {e1 | x1, x2.e2}" ;
  pp_parse_expr "scase x {e1 | x1,x2 . e2}" ;
  pp_parse_expr "scase (x) {e1 | x1,  x2.e2}" ;
  pp_parse_expr "scase a {() | _, y. ()}" ;
  [%expect
    {|
    (Ok (Scase ((Var (x ())) (Var (e1 ())) ((x1 ()) (x2 ()) (Var (e2 ()))))))
    (Ok (Scase ((Var (x ())) (Var (e1 ())) ((x1 ()) (x2 ()) (Var (e2 ()))))))
    (Ok (Scase ((Var (x ())) (Var (e1 ())) ((x1 ()) (x2 ()) (Var (e2 ()))))))
    (Ok (Scase ((Var (a ())) Null ((_ ()) (y ()) Null))))
    |}]
