open! Core
open! Ast
open! Or_error.Let_syntax

let ensure_tp ~tp ~expected_tp ~error_msg =
  match LType.equal tp expected_tp with
  | true ->
      Ok ()
  | false ->
      Or_error.error_string error_msg

let rec synthesize_tp ~(ctx : Context.t) ~(expr : LExpr.t) : LType.t Or_error.t
    =
  match expr with
  | LExpr.Diamond ->
      Ok LType.Diamond
  | LExpr.Var (x, i) -> (
      let%bind t, status =
        Context.find ctx (x, i)
        |> Or_error.of_option
             ~error:
               (Error.of_string
                  [%string
                    "Variable '%{Var.sexp_of_t (x,i) |> Sexp.to_string_hum}' \
                     not bound"] )
      in
      match status with
      | None ->
          Ok t
      | Some Read ->
          Or_error.error_string [%string "Variable '%{x}' used more than once"]
      | Some Bound ->
          let%map () = Context.read ctx (x, i) in
          t )
  | LExpr.Lam (v, v_tp, expr) ->
      let%bind () = Context.add ctx v v_tp in
      let%bind expr_tp = synthesize_tp ~ctx ~expr in
      let%bind () = Context.remove ctx v in
      Ok (LType.Fun (v_tp, expr_tp))
  | LExpr.Slam (v, v_tp, expr) ->
      let ctx = Context.duplicate_dmd_free ctx in
      let%bind () = Context.add ctx v v_tp in
      let%bind expr_tp = synthesize_tp ~ctx ~expr in
      let%bind () = Context.remove ctx v in
      Ok (LType.Sfun (v_tp, expr_tp))
  | LExpr.App (f, a) -> (
      let%bind f_tp = synthesize_tp ~ctx ~expr:f in
      match f_tp with
      | LType.Fun (a_tp, ret_tp) | LType.Sfun (a_tp, ret_tp) ->
          let%bind () = typecheck ~ctx ~expr:a ~tp:a_tp in
          Ok ret_tp
      | _ ->
          Or_error.error_string
            [%string
              "Application: Expected function type, got %{LType.to_string f_tp}"]
      )
  | LExpr.Nil tp ->
      Ok (LType.List tp)
  | LExpr.Snil tp ->
      Ok (LType.Stack tp)
  | LExpr.Cons (d, x, y) ->
      let%bind () = typecheck ~ctx ~expr:d ~tp:LType.Diamond in
      let%bind x_tp = synthesize_tp ~ctx ~expr:x in
      let%bind () = typecheck ~ctx ~expr:y ~tp:(LType.List x_tp) in
      Ok (LType.List x_tp)
  | LExpr.Leaf tp ->
      Ok (LType.Tree tp)
  | LExpr.Node (d, l, x, r) ->
      let%bind () = typecheck ~ctx ~expr:d ~tp:LType.Diamond in
      let%bind x_tp = synthesize_tp ~ctx ~expr:x in
      let%bind () = typecheck ~ctx ~expr:l ~tp:(LType.Tree x_tp) in
      let%bind () = typecheck ~ctx ~expr:r ~tp:(LType.Tree x_tp) in
      Ok (LType.Tree x_tp)
  | LExpr.Scons (x, y) ->
      let%bind x_tp = synthesize_tp ~ctx ~expr:x in
      let%bind () = typecheck ~ctx ~expr:y ~tp:(LType.Stack x_tp) in
      Ok (LType.Stack x_tp)
  | LExpr.Lrec (e, e1, (x1, x2, y, e2)) -> (
      let%bind e_tp = synthesize_tp ~ctx ~expr:e in
      match e_tp with
      | LType.List sigma ->
          let%bind tau = synthesize_tp ~ctx ~expr:e1 in
          let new_ctx = Context.duplicate_dmd_free ctx in
          let%bind () = Context.add new_ctx x1 LType.Diamond in
          let%bind () = Context.add new_ctx x2 sigma in
          let%bind () = Context.add new_ctx y tau in
          let%bind () = typecheck ~ctx:new_ctx ~expr:e2 ~tp:tau in
          Ok tau
      | _ ->
          Or_error.error_string
            [%string
              "Lrec: Expected list type for scrutinee, got %{LType.to_string \
               e_tp}"] )
  | LExpr.Trec (e, e1, (x1, y1, x2, y2, e2)) -> (
      let%bind e_tp = synthesize_tp ~ctx ~expr:e in
      match e_tp with
      | LType.Tree sigma ->
          (* Base case uses empty non-diamond-free context to ensure diamond-free *)
          let base_ctx = Context.duplicate_dmd_free ctx in
          let%bind tau = synthesize_tp ~ctx:base_ctx ~expr:e1 in
          let new_ctx = Context.duplicate_dmd_free ctx in
          let%bind () = Context.add new_ctx x1 LType.Diamond in
          let%bind () = Context.add new_ctx y1 tau in
          let%bind () = Context.add new_ctx x2 sigma in
          let%bind () = Context.add new_ctx y2 tau in
          let%bind () = typecheck ~ctx:new_ctx ~expr:e2 ~tp:tau in
          Ok tau
      | _ ->
          Or_error.error_string
            [%string
              "Trec: Expected tree type for scrutinee, got %{LType.to_string \
               e_tp}"] )
  | LExpr.Pair (e1, e2) ->
      let%bind e1_tp = synthesize_tp ~ctx ~expr:e1 in
      let%bind e2_tp = synthesize_tp ~ctx ~expr:e2 in
      Ok (LType.Prod (e1_tp, e2_tp))
  | LExpr.Letp (e1, (x1, x2, e2)) -> (
      let%bind e1_tp = synthesize_tp ~ctx ~expr:e1 in
      match e1_tp with
      | LType.Prod (tau1, tau2) ->
          let%bind () = Context.add ctx x1 tau1 in
          let%bind () = Context.add ctx x2 tau2 in
          let%bind tau = synthesize_tp ~ctx ~expr:e2 in
          let%bind () = Context.remove ctx x2 in
          let%bind () = Context.remove ctx x1 in
          Ok tau
      | _ ->
          Or_error.error_string
            [%string
              "Letp: Expected product type for scrutinee, got \
               %{LType.to_string e1_tp}"] )
  | LExpr.Null ->
      Ok LType.Unit
  | LExpr.Inj ((tau1, tau2), either) -> (
    match either with
    | First e ->
        let%bind e_tp = synthesize_tp ~ctx ~expr:e in
        let%bind () =
          ensure_tp ~tp:e_tp ~expected_tp:tau1
            ~error_msg:
              [%string
                "Injection: Expected %{LType.to_string tau1}, got \
                 %{LType.to_string e_tp}"]
        in
        Ok (LType.Sum (tau1, tau2))
    | Second e ->
        let%bind e_tp = synthesize_tp ~ctx ~expr:e in
        let%bind () =
          ensure_tp ~tp:e_tp ~expected_tp:tau2
            ~error_msg:
              [%string
                "Injection: Expected %{LType.to_string tau2}, got \
                 %{LType.to_string e_tp}"]
        in
        Ok (LType.Sum (tau1, tau2)) )
  | LExpr.Case (e, (x1, e1), (x2, e2)) -> (
      let%bind e_tp = synthesize_tp ~ctx ~expr:e in
      match e_tp with
      | LType.Sum (tau1, tau2) ->
          let e1_ctx = Context.duplicate ctx in
          let%bind () = Context.add e1_ctx x1 tau1 in
          let%bind tau = synthesize_tp ~ctx:e1_ctx ~expr:e1 in
          let%bind () = Context.remove e1_ctx x1 in
          let e2_ctx = Context.duplicate ctx in
          let%bind () = Context.add e2_ctx x2 tau2 in
          let%bind () = typecheck ~ctx:e2_ctx ~expr:e2 ~tp:tau in
          let%bind () = Context.remove e2_ctx x2 in
          Context.merge ctx e1_ctx e2_ctx ;
          Ok tau
      | _ ->
          Or_error.error_string
            [%string
              "Case: Expected sum type for scrutinee, got %{LType.to_string \n\
              \               e_tp}"] )
  | LExpr.Scase (e, e1, (x1, x2, e2)) -> (
      let%bind e_tp = synthesize_tp ~ctx ~expr:e in
      match e_tp with
      | LType.Stack tau ->
          (* Copy context for first branch *)
          let e1_ctx = Context.duplicate ctx in
          let%bind ret_tp = synthesize_tp ~ctx:e1_ctx ~expr:e1 in
          (* Copy context for second branch *)
          let e2_ctx = Context.duplicate ctx in
          let%bind () = Context.add e2_ctx x1 tau in
          let%bind () = Context.add e2_ctx x2 e_tp in
          let%bind () = typecheck ~ctx:e2_ctx ~expr:e2 ~tp:ret_tp in
          let%bind () = Context.remove e2_ctx x2 in
          let%bind () = Context.remove e2_ctx x1 in
          (* Merge: keep only variables that were read in BOTH branches *)
          Context.merge ctx e1_ctx e2_ctx ;
          Ok ret_tp
      | _ ->
          Or_error.error_string
            [%string
              "Case: Expected stack type for scrutinee, got %{LType.to_string \
               e_tp}"] )
  | LExpr.List _ ->
      Or_error.error_string
        [%string "List syntactic sugar should've been elaborated"]
  | LExpr.Stack _ ->
      Or_error.error_string
        [%string "Stack syntactic sugar should've been elaborated"]

and typecheck ~(ctx : Context.t) ~(expr : LExpr.t) ~(tp : LType.t) :
    unit Or_error.t =
  match expr with
  | LExpr.Diamond ->
      let%bind () = Context.read_latest_dmd ctx in
      ensure_tp ~tp:LType.Diamond ~expected_tp:tp
        ~error_msg:[%string "Expected %{tp#LType}, got <>"]
  | LExpr.Var x ->
      let%bind x_tp = synthesize_tp ~ctx ~expr in
      ensure_tp ~tp:x_tp ~expected_tp:tp
        ~error_msg:
          [%string
            "Var %{Var.to_string_hum x} Expected %{tp#LType}, got %{x_tp#LType}"]
  | LExpr.Lam (v, v_tp, expr) -> (
    match tp with
    | LType.Fun (arg_tp, ret_tp) ->
        if LType.equal arg_tp v_tp then
          let%bind () = Context.add ctx v arg_tp in
          let%bind () = typecheck ~ctx ~expr ~tp:ret_tp in
          Context.remove ctx v
        else
          Or_error.error_string
            [%string
              "Lam: Expected argument type %{LType.to_string arg_tp}, got \
               %{LType.to_string v_tp}"]
    | _ ->
        Or_error.error_string
          [%string "Lam: Expected function type, got %{LType.to_string tp}"] )
  | LExpr.Slam (v, v_tp, expr) -> (
    match tp with
    | LType.Sfun (arg_tp, ret_tp) ->
        if LType.equal arg_tp v_tp then
          let ctx = Context.duplicate_dmd_free ctx in
          let%bind () = Context.add ctx v arg_tp in
          let%bind () = typecheck ~ctx ~expr ~tp:ret_tp in
          Context.remove ctx v
        else
          Or_error.error_string
            [%string
              "Lam: Expected argument type %{LType.to_string arg_tp}, got \
               %{LType.to_string v_tp}"]
    | _ ->
        Or_error.error_string
          [%string "Lam: Expected function type, got %{LType.to_string tp}"] )
  | LExpr.App (f, a) -> (
      let%bind f_tp = synthesize_tp ~ctx ~expr:f in
      match f_tp with
      | LType.Fun (a_tp, ret_tp) | LType.Sfun (a_tp, ret_tp) -> (
        match LType.equal ret_tp tp with
        | true ->
            typecheck ~ctx ~expr:a ~tp:a_tp
        | false ->
            Or_error.error_string
              [%string
                "Application: Expected %{LType.to_string tp}, got \
                 %{LType.to_string ret_tp}"] )
      | _ ->
          Or_error.error_string
            [%string
              "Application: Expected function type, got %{LType.to_string f_tp}"]
      )
  | LExpr.Nil expected_tp -> (
    match tp with
    | LType.List tp ->
        if LType.equal expected_tp tp then Ok ()
        else
          Or_error.error_string
            [%string
              "Nil: Expected %{LType.to_string (LType.List tp)}, got \
               %{LType.to_string (LType.List expected_tp)}"]
    | _ ->
        Or_error.error_string
          [%string "Nil: Expected list type, got %{LType.to_string tp}"] )
  | LExpr.Cons (d, x, y) -> (
    match tp with
    | LType.List inner_tp ->
        let%bind () = typecheck ~ctx ~expr:d ~tp:LType.Diamond in
        let%bind () = typecheck ~ctx ~expr:x ~tp:inner_tp in
        let%bind () = typecheck ~ctx ~expr:y ~tp:(LType.List inner_tp) in
        Ok ()
    | _ ->
        Or_error.error_string
          [%string "Cons: Expected list type, got %{LType.to_string tp}"] )
  | LExpr.Leaf expected_tp -> (
    match tp with
    | LType.Tree tp ->
        if LType.equal expected_tp tp then Ok ()
        else
          Or_error.error_string
            [%string
              "Leaf: Expected %{LType.to_string (LType.Tree tp)}, got \
               %{LType.to_string (LType.Tree expected_tp)}"]
    | _ ->
        Or_error.error_string
          [%string "Tree: Expected tree type, got %{LType.to_string tp}"] )
  | LExpr.Node (d, l, x, r) -> (
    match tp with
    | LType.Tree inner_tp ->
        let%bind () = typecheck ~ctx ~expr:d ~tp:LType.Diamond in
        let%bind () = typecheck ~ctx ~expr:l ~tp:(LType.Tree inner_tp) in
        let%bind () = typecheck ~ctx ~expr:x ~tp:inner_tp in
        let%bind () = typecheck ~ctx ~expr:r ~tp:(LType.Tree inner_tp) in
        Ok ()
    | _ ->
        Or_error.error_string
          [%string "Node: Expected tree type, got %{LType.to_string tp}"] )
  | LExpr.Snil expected_tp -> (
    match tp with
    | LType.Stack tp ->
        if LType.equal expected_tp tp then Ok ()
        else
          Or_error.error_string
            [%string
              "Snil: Expected %{LType.to_string (LType.Stack tp)}, got \
               %{LType.to_string (LType.List expected_tp)}"]
    | _ ->
        Or_error.error_string
          [%string "Snil: Expected stack type, got %{LType.to_string tp}"] )
  | LExpr.Scons (x, y) -> (
    match tp with
    | LType.Stack inner_tp ->
        let%bind () = typecheck ~ctx ~expr:x ~tp:inner_tp in
        let%bind () = typecheck ~ctx ~expr:y ~tp:(LType.Stack inner_tp) in
        Ok ()
    | _ ->
        Or_error.error_string
          [%string "Cons: Expected list type, got %{LType.to_string tp}"] )
  | LExpr.Lrec (e, e1, (x1, x2, y, e2)) -> (
      let%bind e_tp = synthesize_tp ~ctx ~expr:e in
      match e_tp with
      | LType.List sigma ->
          let%bind () =
            typecheck ~ctx ~expr:e1 ~tp
            |> Or_error.tag ~tag:"Lrec: base case type mismatch"
          in
          let new_ctx = Context.duplicate_dmd_free ctx in
          let%bind () = Context.add new_ctx x1 LType.Diamond in
          let%bind () = Context.add new_ctx x2 sigma in
          let%bind () = Context.add new_ctx y tp in
          let%bind tp =
            typecheck ~ctx:new_ctx ~expr:e2 ~tp
            |> Or_error.tag ~tag:"Lrec: recursive case type mismatch"
          in
          Ok tp
      | _ ->
          Or_error.error_string
            [%string
              "Lrec: Expected list type for scrutinee, got %{LType.to_string \
               e_tp}"] )
  | LExpr.Trec (e, e1, (x1, y1, x2, y2, e2)) -> (
      let%bind e_tp = synthesize_tp ~ctx ~expr:e in
      match e_tp with
      | LType.Tree sigma ->
          (* Base case uses empty non-diamond-free context to ensure diamond-free *)
          let base_ctx = Context.duplicate_dmd_free ctx in
          let%bind () =
            typecheck ~ctx:base_ctx ~expr:e1 ~tp
            |> Or_error.tag ~tag:"Trec: base case type mismatch"
          in
          let new_ctx = Context.duplicate_dmd_free ctx in
          let%bind () = Context.add new_ctx x1 LType.Diamond in
          let%bind () = Context.add new_ctx y1 tp in
          let%bind () = Context.add new_ctx x2 sigma in
          let%bind () = Context.add new_ctx y2 tp in
          let%bind tp =
            typecheck ~ctx:new_ctx ~expr:e2 ~tp
            |> Or_error.tag ~tag:"Trec: recursive case type mismatch"
          in
          Ok tp
      | _ ->
          Or_error.error_string
            [%string
              "Trec: Expected tree type for scrutinee, got %{LType.to_string \
               e_tp}"] )
  | LExpr.Pair (e1, e2) -> (
    match tp with
    | LType.Prod (e1_tp, e2_tp) ->
        let%bind () = typecheck ~ctx ~expr:e1 ~tp:e1_tp in
        typecheck ~ctx ~expr:e2 ~tp:e2_tp
    | _ ->
        Or_error.error_string
          [%string "Pair: Expected product type, got %{LType.to_string tp}"] )
  | LExpr.Letp (e1, (x1, x2, e2)) -> (
      let%bind e1_tp = synthesize_tp ~ctx ~expr:e1 in
      match e1_tp with
      | LType.Prod (tau1, tau2) ->
          let%bind () = Context.add ctx x1 tau1 in
          let%bind () = Context.add ctx x2 tau2 in
          let%bind () = typecheck ~ctx ~expr:e2 ~tp in
          let%bind () = Context.remove ctx x2 in
          let%bind () = Context.remove ctx x1 in
          Ok ()
      | _ ->
          Or_error.error_string
            [%string
              "Letp: Expected product type for scrutinee, got \
               %{LType.to_string e1_tp}"] )
  | LExpr.Null ->
      ensure_tp ~tp:LType.Unit ~expected_tp:tp
        ~error_msg:[%string "Expected %{tp#LType}, got Unit"]
  | LExpr.Inj ((tau1, tau2), either) -> (
    match tp with
    | LType.Sum (expected_tau1, expected_tau2) ->
        if LType.equal expected_tau1 tau1 && LType.equal expected_tau2 tau2 then
          match either with
          | First e ->
              typecheck ~ctx ~expr:e ~tp:tau1
          | Second e ->
              typecheck ~ctx ~expr:e ~tp:tau2
        else
          Or_error.error_string
            [%string
              "Injection: Expected %{LType.to_string (LType.Sum \
               (expected_tau1, expected_tau2))}, got %{LType.to_string \
               (LType.Sum (tau1, tau2))}"]
    | _ ->
        Or_error.error_string
          [%string "Injection: Expected sum type, got %{LType.to_string tp}"] )
  | LExpr.Case (e, (x1, e1), (x2, e2)) -> (
      let%bind e_tp = synthesize_tp ~ctx ~expr:e in
      match e_tp with
      | LType.Sum (tau1, tau2) ->
          (* Copy context for first branch *)
          let e1_ctx = Context.duplicate ctx in
          let%bind () = Context.add e1_ctx x1 tau1 in
          let%bind () = typecheck ~ctx:e1_ctx ~expr:e1 ~tp in
          let%bind () = Context.remove e1_ctx x1 in
          (* Copy context for second branch *)
          let e2_ctx = Context.duplicate ctx in
          let%bind () = Context.add e2_ctx x2 tau2 in
          let%bind () = typecheck ~ctx:e2_ctx ~expr:e2 ~tp in
          let%bind () = Context.remove e2_ctx x2 in
          (* Merge: keep only variables that were read in BOTH branches *)
          Context.merge ctx e1_ctx e2_ctx ;
          Ok ()
      | _ ->
          Or_error.error_string
            [%string
              "Case: Expected sum type for scrutinee, got %{LType.to_string \
               e_tp}"] )
  | LExpr.Scase (e, e1, (x1, x2, e2)) -> (
      let%bind e_tp = synthesize_tp ~ctx ~expr:e in
      match e_tp with
      | LType.Stack tau ->
          (* Copy context for first branch *)
          let e1_ctx = Context.duplicate ctx in
          let%bind () = typecheck ~ctx:e1_ctx ~expr:e1 ~tp in
          (* Copy context for second branch *)
          let e2_ctx = Context.duplicate ctx in
          let%bind () = Context.add e2_ctx x1 tau in
          let%bind () = Context.add e2_ctx x2 e_tp in
          let%bind () = typecheck ~ctx:e2_ctx ~expr:e2 ~tp in
          let%bind () = Context.remove e2_ctx x2 in
          let%bind () = Context.remove e2_ctx x1 in
          (* Merge: keep only variables that were read in BOTH branches *)
          Context.merge ctx e1_ctx e2_ctx ;
          Ok ()
      | _ ->
          Or_error.error_string
            [%string
              "Case: Expected stack type for scrutinee, got %{LType.to_string \
               e_tp}"] )
  | LExpr.List _ ->
      Or_error.error_string
        [%string "List syntactic sugar should've been elaborated"]
  | LExpr.Stack _ ->
      Or_error.error_string
        [%string "Stack syntactic sugar should've been elaborated"]

let rec check_val (t : LExpr.t) : unit Or_error.t =
  match t with
  | LExpr.Diamond ->
      Ok ()
  | LExpr.Var _ ->
      Ok ()
  | LExpr.App (f, s) ->
      let%bind () = check_val f in
      check_val s
  | LExpr.Cons (d, x, y) ->
      let%bind () = check_val d in
      let%bind () = check_val x in
      check_val y
  | LExpr.Scons (x, y) ->
      let%bind () = check_val x in
      check_val y
  | LExpr.Node (d, l, x, r) ->
      let%bind () = check_val d in
      let%bind () = check_val l in
      let%bind () = check_val x in
      check_val r
  | LExpr.Inj (_, e) ->
      Either.value_map e ~first:check_val ~second:check_val
  | LExpr.Nil _ ->
      Ok ()
  | LExpr.Snil _ ->
      Ok ()
  | LExpr.Leaf _ ->
      Ok ()
  | LExpr.Pair (f, s) ->
      let%bind () = check_val f in
      check_val s
  | LExpr.Null ->
      Ok ()
  | LExpr.List _ ->
      Or_error.error_string [%string "List should've been elaborated"]
  | LExpr.Stack _ ->
      Or_error.error_string [%string "Stack should've been elaborated"]
  | LExpr.Lam _
  | LExpr.Slam _
  | LExpr.Lrec _
  | LExpr.Trec _
  | LExpr.Scase _
  | LExpr.Case _
  | LExpr.Letp _ ->
      Or_error.error_string
        [%string "Negative expressions are not allowed in values"]
