# LFPL+

LFPL+ is an implementation for running LFPL (with extensions) programs. The
accompanying LFPL+ report contains more information on our extensions and
modifications to the LFPL typing rules. 

## Usage

First, install the dependences with:

``` shell
opam install . --deps-only
```

Then, you can build and install the interpreter with

``` shell
dune build --release && dune install
```

You can now run LFPL+ files with

``` shell
lfpl eval FILENAME
```

and format them with

``` shell
lfpl format FILENAME
```

You can pass the `--help` flag to the `lfpl` command, or any subcommand to see flags and other information.

## Code Structure

The CLI is provided in the `bin/` folder. This is the entrypoint for the binary and parses/passes CLI input to the actual LFPL+ interpreter.

The interpreter is contained in the `lib/` folder. It is made up of various modules:

- `ast.ml`: Provides the LFPL+ AST for expressions (`LExpr.t`), types (`LType.t`), and definitions (`LDefn.t`)
- `parser.ml`: Provides a parser for LFPL+ expressions and programs. This is built using *angstrom*, a parser combinator library.
- `elab.ml`: Provides an elaborater, that expands some syntactic sugar (like the list/stack types) and makes variables names unique (more below).
- `context.ml`: Provides our implementation of a context for doing subtractive typechecking. More discussion of this context implementation is given in the accompanying report.
- `typechecker.ml`: Provides functions to typecheck/synthesize the type of an LFPL+ expression. More discussion of this implementation is given in the accompanying report.
- `interpreter.ml`: Provides functionality to interpret LFPL+ expressions based on the provided denotational semantics. Notably, this is almost a 1-1 translation of the semantics. It internally defines and uses a `Value.t` type and an `Environment.t` type for representing evaluation environments.
- `lfpl_lib.ml`: The top-level for the library. Exports the `format` and `eval` functions, which should be used as entrypoints to the library.
- `test_helpers.ml`: Provides small helper functions for the tests in the `tests/` folder.
- `lfpl_formatter.ml`: Provides a formatter for LFPL+ expressions

### Notable Implementation Details

All of the following details are further discussed in the accompanying report, but we provide a quick overview here.

For an overview of what the interpreter process is, at a high level, `eval` in `lfpl_lib.ml` is function to look at. One interesting thing is that we allow definitions to only refer to earlier definitions by setting their starting context.

The elaborater performs a pass through a given expression, making variables with the same name in the same scope unique. This allows us to simplify our typechecker as we do not have to worry about shadowing.

Our context implementation, in `context.ml`, is structured for our specific use-case of needing to split it up into diamond-free and non-diamond-free parts. Moreover, to support diamond elision, we keep track of the latest bound diamonds.

## Syntax

```
var := ident

tp := 
    | 1         (* Unit *)
    | (tp)      (* Parenthesized type *)
    | ident     (* Type Alias *)
    | tp list   (* List *)
    | tp stack  (* Stack *)
    | tp tree   (* Tree *)
    | tp * tp   (* Product *)
    | tp + tp   (* Sum *)
    | tp -@ tp  (* Functions *)
    | tp -> tp  (* Structural Functions *)

inj_lbl := 
    | 1
    | 2

expr :=
    (* Basic Expressions *)
    | <*>                                   (* Diamond (elision, values) *)
    | ()                                    (* Null *)
    | var                                   (* Variables *)
    | (expr)                                (* Parenthesized expression *)
    (* Functions *)
    | fn (ident : tp). expr                 (* Functions *
    | sfn (ident : tp). expr                (* Structural Functions *)
    | expr expr                             (* Application *)
    (* Lists, Stacks, Trees *)
    | nil[tp]                               (* List nil *)
    | cons(expr; expr; expr)                (* List cons *)
    | lrec expr { expr | v, v, v. expr }    (* List recursor, v is var *)
    | snil[tp]                              (* Stack nil *)
    | scons(expr; expr)                     (* Stack cons *)
    | scase expr { expr | var, var. expr }  (* Stack elimination *)
    | leaf[tp]                              (* Tree leaf *)
    | node(expr; expr; expr)                (* Tree node *)
    | trec expr { expr | v, v, v, v. expr } (* Tree recursor, v is var *)
    (* Products, Sums *)
    | [tp; tp](inj_lbl.expr)                (* Sum Injection *)
    | case expr { var. expr | var. expr }   (* Sum Case *)
    | (expr, expr)                          (* Pair introduction *)
    | letp (var, var) = expr in expr        (* Pair elimination *)
    (* Syntactic Sugar - only in values*)
    | [tp][expr, ..., expr]                 (* List syntactic sugar *)
    | [tp][|expr, ..., expr|]               (* Stack syntactic sugar *)
   
```


The type precedence is as follows, from highest to lowest:

1. List, Stack, Tree 
2. Products (left-associative)
3. Sums (left-associative)
4. Functions, Structural Functions (right-associative)
