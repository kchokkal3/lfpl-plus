open! Core
open! Lfpl_lib
open! Command.Let_syntax

let eval_command =
  Command.basic ~summary:"run lfpl files"
    (let%map_open filename =
       anon (maybe_with_default "-" ("filename" %: Filename_unix.arg_type))
     and verbose = flag "verbose" ~doc:"Include verbose output" no_arg in
     fun () ->
       let content = In_channel.read_all filename in
       Lfpl_lib.eval content ~verbose )

let format_command =
  Command.basic ~summary:"format lfpl files"
    (let%map_open filename =
       anon (maybe_with_default "-" ("filename" %: Filename_unix.arg_type))
     and inplace_opt = flag "i" ~doc:"Format in-place" no_arg in
     fun () ->
       let content = In_channel.read_all filename in
       Lfpl_lib.format ?inplace:(Option.some_if inplace_opt filename) content )

let () =
  Command_unix.run
    (Command.group ~summary:"LFPL Interpreter"
       [("eval", eval_command); ("format", format_command)] )
