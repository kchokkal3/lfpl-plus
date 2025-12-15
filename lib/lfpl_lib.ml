open! Core
open! Ast
open Or_error.Let_syntax
module Ast = Ast
module Parser = Parser
module Typechecker = Typechecker
module Elab = Elab
module Formatter = Lfpl_formatter
module Test_helpers = Test_helpers

let format ?inplace content =
  let stripped = String.strip content in
  let res =
    let%bind prog =
      Parser.parse stripped |> Or_error.tag ~tag:"Parsing failed!"
    in
    let print oc =
      let print_string s = fprintf oc "%s" s in
      List.iter prog ~f:(fun d ->
          ( match d with
          | Decl (name, tp) ->
              print_string [%string "decl %{name} : "] ;
              print_string (LType.to_string_hum tp) ;
              Out_channel.newline oc
          | Typedef (name, tp) ->
              print_string [%string "typedef %{name} = "] ;
              print_string (LType.to_string_hum tp) ;
              Out_channel.newline oc
          | Val expr ->
              print_string [%string "val "] ;
              Formatter.format_string expr ;
              Out_channel.newline oc
          | Defn (name, expr) ->
              print_string [%string "defn %{name} = "] ;
              Formatter.format_string expr ;
              Out_channel.newline oc ) ;
          Out_channel.newline oc )
    in
    ( match inplace with
    | None ->
        print stdout
    | Some file ->
        Out_channel.with_file file ~f:(fun oc ->
            Format.set_formatter_out_channel oc ;
            print oc ) ) ;
    Ok ()
  in
  match res with
  | Ok () ->
      ()
  | Error e ->
      Error.sexp_of_t e |> Sexp.to_string_hum |> print_endline

let eval ~verbose content =
  let stripped = String.strip content in
  let res =
    let%bind prog =
      Parser.parse stripped |> Or_error.tag ~tag:"Parsing failed!"
    in
    (* Build typedef map for type expansion *)
    let typedef_map = Elab.build_typedef_map prog in
    (* Expand typedefs in declarations and filter out typedef declarations *)
    let decls =
      List.filter_map prog ~f:(function
        | Val _ | Defn _ | Typedef _ ->
            None
        | Decl (name, tp) ->
            Some (name, Elab.expand_type typedef_map tp) )
    in
    let defns =
      List.filter_map prog ~f:(function
        | Val _ | Decl _ | Typedef _ ->
            None
        | Defn (name, expr) ->
            Some (name, expr) )
    in
    let vals =
      List.filter_map prog ~f:(function
        | Defn _ | Decl _ | Typedef _ ->
            None
        | Val expr ->
            Some expr )
    in
    let%bind bind_env, bind_tps =
      List.fold_result defns ~init:(Interpreter.Environment.empty, [])
        ~f:(fun (bind_env, bind_tps) (name, expr) ->
          let expr = Elab.elab prog expr in
          let%bind () =
            match
              List.find bind_tps ~f:(fun (n, _) -> Var.equal n (name, None))
            with
            | Some (n, _) ->
                Or_error.error_string
                  [%string "%{Var.to_string_hum n} is already defined"]
            | None ->
                Ok ()
          in
          let%bind tp =
            print_endline [%string "Typechecking %{name}"] ;
            let expected_tp = List.Assoc.find decls ~equal:String.equal name in
            match expected_tp with
            | None ->
                Typechecker.synthesize_tp
                  ~ctx:(Context.of_defns ~check_diamonds:true bind_tps)
                  ~expr
                |> Or_error.tag
                     ~tag:[%string "Could not synthesize type for defn %{name}"]
            | Some expected_tp ->
                Typechecker.typecheck
                  ~ctx:(Context.of_defns ~check_diamonds:true bind_tps)
                  ~expr ~tp:expected_tp
                |> Or_error.map ~f:(Fn.const expected_tp)
                |> Or_error.tag
                     ~tag:[%string "Could not synthesize type for defn %{name}"]
          in
          let eval_expr = Interpreter.eval ~env:bind_env ~expr in
          Ok
            ( Interpreter.Environment.add bind_env (name, None) eval_expr
            , ((name, None), tp) :: bind_tps ) )
    in
    if verbose then (
      print_endline "===== Printing Definition Types =====" ;
      List.iter (List.rev bind_tps) ~f:(fun (name, tp) ->
          print_endline
            [%string "%{Var.to_string_hum name} has %{LType.to_string_hum tp}"] ) ;
      print_endline "" )
    else () ;
    print_endline "========== Printing Values ==========" ;
    let vals = List.map vals ~f:(Elab.elab prog) in
    let%bind () = List.map vals ~f:Typechecker.check_val |> Or_error.all_unit in
    List.fold_result ~init:() vals ~f:(fun () v ->
        let%map _ =
          Typechecker.synthesize_tp ~ctx:(Context.of_defns bind_tps) ~expr:v
        in
        let value = Interpreter.eval ~env:bind_env ~expr:v in
        let value_str = Interpreter.Value.to_string_hum value in
        print_endline [%string "val %{LExpr.to_string_hum v} = %{value_str}"] )
  in
  match res with
  | Ok () ->
      ()
  | Error e ->
      Error.sexp_of_t e |> Sexp.to_string_hum |> print_endline
