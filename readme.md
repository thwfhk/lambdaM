**LambdaM**: A Simple Language with **Termination Checking** based on **Dependent Types**

---

The name lambdaM means *lambda calculus with metrics.*

This is a term project of the course [*Design Principles of Programming Languages*](https://xiongyingfei.github.io/DPPL/2020/main.htm).

## Report

See the `report.pdf` in the `tex` directory.

## Build

To build the lambdaM:

- Run `make` to build lambdaM
- Run `make clean` to clean up the directory.

## Test

To test with the examples in `examples.ml`:

- Run `utop -init init.ml` or `ocaml -init init.ml` to test the code in the REPL of OCaml.
- Use `prty function_name_here` to print the type of functions.
- Use `prty test_term_here` to print the type of terms and use `prtm test_term_here` to print the results of terms.


You can also write abstract syntax trees by yourself and test them using `prty` and `prtm`.