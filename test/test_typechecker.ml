open Lfpl_lib.Ast
open Lfpl_lib.Test_helpers

let%expect_test _ =
  pp_synthesize_tp "()" ;
  pp_synthesize_tp "nil[1]" ;
  pp_synthesize_tp "nil[<>]" ;
  pp_synthesize_tp "nil[1 list]" ;
  pp_synthesize_tp "fn(x : 1). x" ;
  pp_synthesize_tp "fn(x : 1). ()" ;
  pp_synthesize_tp "fn(x : <>). fn(y : 1). x" ;
  [%expect
    {|
    (Ok Unit)
    (Ok (List Unit))
    (Ok (List Diamond))
    (Ok (List (List Unit)))
    (Ok (Fun (Unit Unit)))
    (Ok (Fun (Unit Unit)))
    (Ok (Fun (Diamond (Fun (Unit Diamond)))))
    |}]

(* Test variables and context *)
let%expect_test _ =
  pp_synthesize_tp "x" ;
  pp_synthesize_tp "fn (x : 1). y" ;
  [%expect
    {|
    (Error "Variable '(x ())' not bound")
    (Error "Variable '(y ())' not bound")
    |}]

(* Test contraction (using a variable twice) *)
let%expect_test _ =
  pp_synthesize_tp "fn(x : 1). (x, x)" ;
  pp_synthesize_tp "fn(x : <>). cons(x; (); cons(x; (); nil[1]))" ;
  [%expect
    {|
    (Ok (Fun (Unit (Prod (Unit Unit)))))
    (Error "Variable 'x' used more than once")
    |}]

(* Test function app_synthesize_tplication *)
let%expect_test _ =
  pp_synthesize_tp "(fn(x : 1). x) ()" ;
  pp_synthesize_tp "(fn(x : <>). ()) ()" ;
  pp_synthesize_tp "(fn(x : 1). fn(y : <>). y) () ()" ;
  [%expect
    {|
    (Ok Unit)
    (Error "Expected Diamond, got Unit")
    (Error "Expected Diamond, got Unit")
    |}]

(* Test pairs and products *)
let%expect_test _ =
  pp_synthesize_tp "((), ())" ;
  pp_synthesize_tp "(nil[1], nil[<>])" ;
  pp_synthesize_tp "(fn(x : 1). x, fn(y : <>). y)" ;
  [%expect
    {|
    (Ok (Prod (Unit Unit)))
    (Ok (Prod ((List Unit) (List Diamond))))
    (Ok (Prod ((Fun (Unit Unit)) (Fun (Diamond Diamond)))))
    |}]

(* Test letp *)
let%expect_test _ =
  pp_synthesize_tp "letp (x, y) = ((), ()) in x" ;
  pp_synthesize_tp "letp (x, y) = ((), nil[1]) in y" ;
  pp_synthesize_tp "letp (x, y) = ((), ()) in (x, y)" ;
  pp_synthesize_tp "letp (x, y) = () in x" ;
  [%expect
    {|
    (Ok Unit)
    (Ok (List Unit))
    (Ok (Prod (Unit Unit)))
    (Error "Letp: Expected product type for scrutinee, got Unit")
    |}]

(* Test cons and lists *)
let%expect_test _ =
  pp_synthesize_tp "fn(x : <>). cons(x; (); nil[1])" ;
  pp_synthesize_tp "fn(x : <>). cons(x; (); cons((); (); nil[1]))" ;
  pp_synthesize_tp "fn(x : <>). cons(x; nil[1]; nil[1])" ;
  [%expect
    {|
    (Ok (Fun (Diamond (List Unit))))
    (Error "Expected Diamond, got Unit")
    (Error "Nil: Expected (List(List Unit)), got (List Unit)")
    |}]

(* Test lrec *)
let%expect_test _ =
  pp_synthesize_tp "lrec nil[1] {() | x1, x2, y. ()}" ;
  pp_synthesize_tp "lrec cons((); (); nil[1]) {() | x1, x2, y. ()}" ;
  pp_synthesize_tp "lrec nil[<>] {nil[1] | x1, x2, y. cons((); x2; y)}" ;
  pp_synthesize_tp "lrec () {() | x1, x2, y. ()}" ;
  [%expect
    {|
    (Ok Unit)
    (Error "Expected Diamond, got Unit")
    (Error "Expected Diamond, got Unit")
    (Error "Lrec: Expected list type for scrutinee, got Unit")
    |}]

(* Test sum types and injection *)
let%expect_test _ =
  pp_synthesize_tp "[1; <>](1. ())" ;
  pp_synthesize_tp "[1; <>](2. ())" ;
  pp_synthesize_tp "[1 list; <> list](1. nil[1])" ;
  pp_synthesize_tp "[1; <>](1. nil[1])" ;
  [%expect
    {|
    (Ok (Sum (Unit Diamond)))
    (Error "Injection: Expected Diamond, got Unit")
    (Ok (Sum ((List Unit) (List Diamond))))
    (Error "Injection: Expected Unit, got (List Unit)")
    |}]

(* Test case expressions *)
let%expect_test _ =
  pp_synthesize_tp "case [1; <>](1. ()) {x. () | y. ()}" ;
  pp_synthesize_tp "case [1; <>](2. ()) {x. () | y. ()}" ;
  pp_synthesize_tp "case [1; <>](1. ()) {x. x | y. ()}" ;
  pp_synthesize_tp "case () {x. () | y. ()}" ;
  [%expect
    {|
    (Ok Unit)
    (Error "Injection: Expected Diamond, got Unit")
    (Ok Unit)
    (Error "Case: Expected sum type for scrutinee, got Unit")
    |}]

(* Test typechecking mode (against a specific type) *)
let%expect_test _ =
  pp_typecheck "()" LType.Unit ;
  pp_typecheck "()" LType.Diamond ;
  pp_typecheck "fn(x : 1). x" (LType.Fun (LType.Unit, LType.Unit)) ;
  pp_typecheck "fn(x : 1). x" (LType.Fun (LType.Diamond, LType.Diamond)) ;
  pp_typecheck "nil[1]" (LType.List LType.Unit) ;
  pp_typecheck "nil[<>]" (LType.List LType.Unit) ;
  [%expect
    {|
    (Ok ())
    (Error "Expected Diamond, got Unit")
    (Ok ())
    (Error "Lam: Expected argument type Diamond, got Unit")
    (Ok ())
    (Error "Nil: Expected (List Unit), got (List Diamond)")
    |}]

(* Test complex nested expressions *)
let%expect_test _ =
  pp_synthesize_tp "fn(f : 1 -@ 1). fn(x : 1). f x" ;
  pp_synthesize_tp "fn(f : 1 -@ 1). fn(x : 1). f (f x)" ;
  pp_synthesize_tp "letp (f, x) = (fn(y : 1). y, ()) in f x" ;
  [%expect
    {|
    (Ok (Fun ((Fun (Unit Unit)) (Fun (Unit Unit)))))
    (Error "Variable 'f' used more than once")
    (Ok Unit)
    |}]

(* Test lrec with complex types *)
let%expect_test _ =
  pp_synthesize_tp "lrec nil[1] {nil[1] | x1, x2, y. cons((); x2; y)}" ;
  pp_synthesize_tp "lrec nil[1 * <>] {() | x1, x2, y. ()}" ;
  pp_synthesize_tp "fn(xs : 1 list). lrec xs {() | x1, x2, y. ()}" ;
  [%expect
    {|
    (Error "Expected Diamond, got Unit")
    (Ok Unit)
    (Ok (Fun ((List Unit) Unit)))
    |}]

(* Test checking that lrec creates fresh context *)
let%expect_test _ =
  pp_synthesize_tp "fn(x : 1). lrec nil[<>] {x | y1, y2, y3. x}" ;
  [%expect {| (Ok (Fun (Unit Unit))) |}]

(* Test case with different branch types *)
let%expect_test _ =
  pp_synthesize_tp "case [1; <>](1. ()) {x. x | y. ()}" ;
  pp_synthesize_tp "case [1; <>](1. ()) {x. () | y. y}" ;
  [%expect
    {|
    (Ok Unit)
    (Error "Var y Expected Unit, got Diamond")
    |}]

(* Tests that List constructor errors without elaboration *)
let%expect_test
    "List constructor should error in synthesize without elaboration" =
  pp_synthesize_tp_no_elab "[<>][]" ;
  [%expect {| (Error "List syntactic sugar should've been elaborated") |}]

let%expect_test "List constructor should error in typecheck without elaboration"
    =
  pp_typecheck_no_elab "[1][()]" (LType.List LType.Unit) ;
  [%expect {| (Error "List syntactic sugar should've been elaborated") |}]

let%expect_test "Multi-element list should error without elaboration" =
  pp_synthesize_tp_no_elab "[<>][<*>; <*>]" ;
  [%expect {| (Error "List syntactic sugar should've been elaborated") |}]

(* Tests that List elaborates correctly and typechecks *)
let%expect_test "Empty list elaborates and typechecks" =
  pp_synthesize_tp "[<>][]" ; [%expect {| (Ok (List Diamond)) |}]

let%expect_test "Single element list elaborates and typechecks" =
  pp_synthesize_tp "[1][()]" ; [%expect {| (Ok (List Unit)) |}]

let%expect_test "Multi-element list elaborates and typechecks" =
  pp_synthesize_tp "[<>][<*>; <*>; <*>]" ;
  [%expect {| (Ok (List Diamond)) |}]

let%expect_test "Nested list elaborates and typechecks" =
  pp_synthesize_tp "[<> list][[<>][]; [<>][<*>]]" ;
  [%expect {| (Ok (List (List Diamond))) |}]

(* Tree tests *)
let%expect_test "Leaf expression typechecks" =
  pp_synthesize_tp "leaf[<>]" ;
  [%expect {| (Ok (Tree Diamond)) |}]

let%expect_test "Node expression typechecks" =
  pp_synthesize_tp "node(<*>; leaf[1]; (); leaf[1])" ;
  [%expect {| (Ok (Tree Unit)) |}]

let%expect_test "Trec with diamond-free base case typechecks" =
  pp_synthesize_tp "trec leaf[1] {[1;1](1.()) | d, y1, x, y2. y1}" ;
  [%expect {| (Ok (Sum (Unit Unit))) |}]

let%expect_test "Trec with non-diamond-free base case fails" =
  pp_synthesize_tp "fn(z : <>). trec leaf[1] {z | d, y1, x, y2. ()}" ;
  [%expect {| (Error "Variable '(z (0))' not bound") |}]
