open Syntax
open Print
open Eval
open Typecheck
open Metric

let ctxlen = 0
let ctx = []
let mctx = []


(* --------------- bool --------------- *)

(* not operator for bool *)
let notbool = 
  TmAbs("b", TyBool, TmIf(TmVar(0, 2+ctxlen), TmFalse, TmTrue))


(* --------------- natural number --------------- *)

let zero = TmZero
let one = TmSucc(TmZero)
let two = TmSucc(one)
let three = TmSucc(two)

(* check if a number is even *)
let iseven = 
  TmFix(
    TmAbs("iseven", TyPi("_", TyNat, TyBool),
      TmAbs("n", TyNat, 
        TmIf(
          TmIsZero(TmVar(0, 2+ctxlen)),
          TmTrue,
          TmApp(notbool, TmApp(TmVar(1, 2+ctxlen), TmPred(TmVar(0, 2+ctxlen))))
        )
      )
    )
  )

(* check if a number is less than 2 *)
let less2 = 
  let n = TmVar(0, 1+ctxlen) in
  TmAbs("n", TyNat,
    TmIf(
      TmIsZero(n),
      TmTrue,
      TmIf(
        TmIsZero(TmPred(n)),
        TmTrue,
        TmFalse
      )
    )
  )

(* plus two numbers *)
let plus = 
  TmFix(
    TmAbs("plus", TyPi("X", TyNat, TyPi("Y", TyNat, TyNat)),
      TmAbs("x", TyNat, 
        TmAbs("y", TyNat,
          TmIf(
            TmIsZero(TmVar(1, 3+ctxlen)),
            TmVar(0, 3+ctxlen),
            TmApp(TmApp(TmVar(2, 3+ctxlen), TmPred(TmVar(1, 3+ctxlen))), TmSucc(TmVar(0, 3+ctxlen)))
          )
        )
      )
    )
  )


(* --------------- vector --------------- *)

(* make a three length vector *)
let mkthree =
  TmAbs("z", TyNat,
    TmAbs("y", TyNat,
      TmAbs("x", TyNat,
        TmCons(two, TmVar(2, 3+ctxlen),
          TmCons(one, TmVar(1, 3+ctxlen),
            TmCons(zero, TmVar(0, 3+ctxlen), TmNil)
          )
        )
      )
    )
  )

let vec1 = TmCons(one, one, TmNil)  (* [1;2] *)
let vec2 = TmCons(one, one, TmCons(zero, two, TmNil))  (* [1;2] *)
let vec3 = TmApp(TmApp(TmApp(mkthree, one), two), three) (* [1;2;3] *)

(* --------------- some recursive functions with metric --------------- *)

(* [Recursive Function 1] calculate the sum of a vector *)
let sum = 
  TmFun(
    "sum",
    [TyNat],
    TyPi("V", TyVector(TmVar(0, 1+ctxlen)), TyNat),
    TmAbs("v", TyVector(TmVar(0, 2+ctxlen)),
      TmIf(
        TmIsNil(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen)),
        TmZero,
        TmApp(
          TmApp(
            plus,
            TmHead(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen))
          ),
          TmApp(
            TmFunApp("sum", TmVar(2, 3+ctxlen), [TmPred(TmVar(1, 3+ctxlen))]),
            TmTail(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen))
          )
        )
      )
    )
  )

(* a wrong version of sum which loops forever *)
let sumR = 
  TmFun(
    "sumR",
    [TyNat],
    TyPi("V", TyVector(TmVar(0, 1+ctxlen)), TyNat),
    TmAbs("v", TyVector(TmVar(0, 2+ctxlen)),
      TmIf(
        TmIsNil(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen)),
        TmZero,
        TmApp(
          TmApp(
            plus,
            TmHead(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen))
          ),
          TmApp(
            TmFunApp("sumR", TmVar(2, 3+ctxlen), [TmSucc(TmVar(1, 3+ctxlen))]),
            TmTail(TmVar(1, 3+ctxlen), TmVar(0, 3+ctxlen))
          )
        )
      )
    )
  )



(* [Recursive Function 2] compare the length of two vectors using recursion *)
let lenless = 
  let n1'  = TmVar(1, 2+ctxlen) in
  let n2'  = TmVar(1, 3+ctxlen) in
  let n1'' = TmVar(1, 3+ctxlen) in 
  let n2'' = TmVar(1, 4+ctxlen) in 
  let lenless = TmVar(4, 5+ctxlen) in
  let n1   = TmVar(3, 5+ctxlen) in
  let n2   = TmVar(2, 5+ctxlen) in
  let v1   = TmVar(1, 5+ctxlen) in
  let v2   = TmVar(0, 5+ctxlen) in
  TmFun(
    "lenless",
    [TyNat; TyNat],
    TyPi("V1", TyVector(n1'), TyPi("V2", TyVector(n2'), TyBool)),
    TmAbs("v1", TyVector(n1''), TmAbs("v2", TyVector(n2''),
      TmIf(
        TmIsNil(n1, v1),
        TmTrue,
        TmIf(
          TmIsNil(n2, v2),
          TmFalse,
          TmApp(TmApp(TmFunApp("lenless", lenless, [TmPred(n1); TmPred(n2)]), 
            TmTail(n1, v1)), TmTail(n2, v2))
        )
      )
    ))
  )

(* a wrong version of lenless which loops forever *)
let lenlessR = 
  let n1'  = TmVar(1, 2+ctxlen) in
  let n2'  = TmVar(1, 3+ctxlen) in
  let n1'' = TmVar(1, 3+ctxlen) in 
  let n2'' = TmVar(1, 4+ctxlen) in 
  let lenless = TmVar(4, 5+ctxlen) in
  let n1   = TmVar(3, 5+ctxlen) in
  let n2   = TmVar(2, 5+ctxlen) in
  let v1   = TmVar(1, 5+ctxlen) in
  let v2   = TmVar(0, 5+ctxlen) in
  TmFun(
    "lenless",
    [TyNat; TyNat],
    TyPi("V1", TyVector(n1'), TyPi("V2", TyVector(n2'), TyBool)),
    TmAbs("v1", TyVector(n1''), TmAbs("v2", TyVector(n2''),
      TmIf(
        TmIsNil(n1, v1),
        TmTrue,
        TmIf(
          TmIsNil(n2, v2),
          TmFalse,
          TmApp(TmApp(TmFunApp("lenless", lenless, [n1; TmSucc(n2)]), 
            v1), TmCons(n2, one, v2))
        )
      )
    ))
  )



(* [Recursive Function 3] return the elements in even positions of a list *)
let evens = 
  let n' = TmVar(0, 1+ctxlen) in
  let n = TmVar(2, 4+ctxlen) in
  let v = TmVar(1, 4+ctxlen) in
  let d = TmVar(0, 4+ctxlen) in
  let evens = TmVar(3, 4+ctxlen) in
  TmFun(
    "evens",
    [TyNat],
    TyPi("v", TyVector(n'), TyPi("d", TyNat, TySigma("m", TyNat, TyVector(TmVar(0, 4+ctxlen))))),
    TmAbs("v", TyVector(TmVar(0, 2+ctxlen)), 
      TmAbs("d", TyNat,
        TmIf(
          TmIsNil(n, v), 
          TmPair(zero, TmNil, TySigma("m", TyNat, TyVector(TmVar(0, 5+ctxlen)))),
          TmIf(
            TmApp(iseven, d),
            TmPair(
              TmSucc(TmProj1(TmApp(TmApp(TmFunApp("evens", evens, [TmPred(n)]), TmTail(n, v)), TmSucc(d)))),
              TmCons(
                TmProj1(TmApp(TmApp(TmFunApp("evens", evens, [TmPred(n)]), TmTail(n, v)), TmSucc(d))),
                TmHead(n, v),
                TmProj2(TmApp(TmApp(TmFunApp("evens", evens, [TmPred(n)]), TmTail(n, v)), TmSucc(d)))
              ),
              TySigma("m", TyNat, TyVector(TmVar(0, 5+ctxlen)))
            ),
            TmPair(
              TmProj1(TmApp(TmApp(TmFunApp("evens", evens, [TmPred(n)]), TmTail(n, v)), TmSucc(d))),
              TmProj2(TmApp(TmApp(TmFunApp("evens", evens, [TmPred(n)]), TmTail(n, v)), TmSucc(d))),
              TySigma("m", TyNat, TyVector(TmVar(0, 5+ctxlen)))
            )
          )
        )
      )
    )
  )



(* [Recursive Function 4] concatenate an element to the tail of a vector *)
let snoc = 
  let x = TmVar(0, 4+ctxlen) in
  let v = TmVar(1, 4+ctxlen) in
  let n = TmVar(2, 4+ctxlen) in
  let snoc' = TmVar(3, 4+ctxlen) in
  TmFun(
    "snoc",
    [TyNat],
    TyPi("v", TyVector(TmVar(0, 1+ctxlen)), TyPi("x", TyNat, TyVector(TmSucc(TmVar(2, 3+ctxlen))))),
    TmAbs("v", TyVector(TmVar(0, 2+ctxlen)),
      TmAbs("x", TyNat,
        TmIf(
          TmIsNil(n, v),
          TmCons(n, x, v),
          TmCons(n, TmHead(n, v), TmApp(TmApp(TmFunApp("snoc", snoc', [TmPred(n)]), TmTail(n, v)), x))
        )
      )
    )
  )



(* Recursive Function 5] concatenate two vectors *)
let append = 
  let v2 = TmVar(0, 5+ctxlen) in
  let v1 = TmVar(1, 5+ctxlen) in
  let n1 = TmVar(2, 5+ctxlen) in
  let n2 = TmVar(3, 5+ctxlen) in
  let append' = TmVar(4, 5+ctxlen) in
  TmFun(
    "append",
    [TyNat],
    TyPi("n1", TyNat, 
      TyPi("v1", TyVector(TmVar(0, 2+ctxlen)), 
        TyPi("v2", TyVector(TmVar(2, 3+ctxlen)), 
          TySigma(
            "m",
            TyNat,
            TyVector(TmVar(0, 5+ctxlen))
          )
        )
      )
    ),
    TmAbs("n1", TyNat,
      TmAbs("v1", TyVector(TmVar(0, 3+ctxlen)),
        TmAbs("v2", TyVector(TmVar(2, 4+ctxlen)),
          TmIf(
            TmIsNil(n2, v2),
            TmPair(n1, v1, TySigma("m", TyNat, TyVector(TmVar(0, 6+ctxlen)))),
            TmPair(
              TmProj1(
                TmApp(TmApp(TmApp(TmFunApp("append", append', [TmPred(n2)]), 
                  TmSucc(n1)), 
                  TmApp(TmApp(TmFunApp("snoc", snoc, [n1]), v1), TmHead(n2, v2))),
                  TmTail(n2, v2)
                )
              ),
              TmProj2(
                TmApp(TmApp(TmApp(TmFunApp("append", append', [TmPred(n2)]), 
                  TmSucc(n1)), 
                  TmApp(TmApp(TmFunApp("snoc", snoc, [n1]), v1), TmHead(n2, v2))),
                  TmTail(n2, v2)
                )
              ),
              TySigma("m", TyNat, TyVector(TmVar(0, 6+ctxlen)))
            )
          )
        )
      )
    )
  )



(* [Recursive Function 6] calculate the f function *)
let f = 
  let v2 = TmVar(0, 5+ctxlen) in
  let v1 = TmVar(1, 5+ctxlen) in
  let n2 = TmVar(2, 5+ctxlen) in
  let n1 = TmVar(3, 5+ctxlen) in
  let f = TmVar(4, 5+ctxlen) in
  TmFun(
    "f",
    [TyNat; TyNat],
    TyPi("v1", TyVector(TmVar(1, 2+ctxlen)), 
      TyPi("v2", TyVector(TmVar(1, 3+ctxlen)), 
        TySigma("m", TyNat, TyVector(TmVar(0, 5+ctxlen)))
      )
    ),
    TmAbs("v1", TyVector(TmVar(1, 3+ctxlen)),
      TmAbs("v2", TyVector(TmVar(1, 4+ctxlen)),
        TmIf(
          TmApp(less2, n1),
          TmIf(
            TmApp(less2, n2),
            TmPair(
              TmProj1(TmApp(TmApp(TmApp(TmFunApp("append", append, [n2]), n1), v1), v2)), 
              TmProj2(TmApp(TmApp(TmApp(TmFunApp("append", append, [n2]), n1), v1), v2)),
              TySigma("m", TyNat, TyVector(TmVar(0, 6+ctxlen)))
            ),
            TmApp(TmApp(TmApp(TmFunApp("append", append, 
              [TmProj1(
                TmApp(TmApp(TmFunApp("f", f, 
                  [TmSucc(n1); TmPred(TmPred(n2))]),
                  TmCons(n1, zero, v1)),
                  TmTail(TmPred(n2), TmTail(n2, v2)))
              )]),
              n1),
              v1),
              TmProj2(
                TmApp(TmApp(TmFunApp("f", f, 
                  [TmSucc(n1); TmPred(TmPred(n2))]),
                  TmCons(n1, zero, v1)),
                  TmTail(TmPred(n2), TmTail(n2, v2)))
              )
            )
          ),
          TmIf(
            TmApp(less2, n2),
            TmApp(TmApp(TmApp(TmFunApp("append", append, 
              [n2]),
              TmProj1(
                TmApp(TmApp(TmFunApp("f", f, 
                  [TmPred(TmPred(n1)); TmSucc(n2)]),
                  TmTail(TmPred(n1), TmTail(n1, v1))),
                  TmCons(n2, zero, v2))
              )),
              TmProj2(
                TmApp(TmApp(TmFunApp("f", f, 
                  [TmPred(TmPred(n1)); TmSucc(n2)]),
                  TmTail(TmPred(n1), TmTail(n1, v1))),
                  TmCons(n2, zero, v2))
              )),
              v2
            ),
            TmApp(TmApp(TmApp(TmFunApp("append", append, 
              [TmProj1(
                TmApp(TmApp(TmFunApp("f", f, 
                  [TmSucc(n1); TmPred(TmPred(n2))]),
                  TmCons(n1, zero, v1)),
                  TmTail(TmPred(n2), TmTail(n2, v2)))
              )]),
              TmProj1(
                TmApp(TmApp(TmFunApp("f", f, 
                  [TmPred(TmPred(n1)); TmSucc(n2)]),
                  TmTail(TmPred(n1), TmTail(n1, v1))),
                  TmCons(n2, zero, v2))
              )),
              TmProj2(
                TmApp(TmApp(TmFunApp("f", f, 
                  [TmPred(TmPred(n1)); TmSucc(n2)]),
                  TmTail(TmPred(n1), TmTail(n1, v1))),
                  TmCons(n2, zero, v2))
              )),
              TmProj2(
                TmApp(TmApp(TmFunApp("f", f, 
                  [TmSucc(n1); TmPred(TmPred(n2))]),
                  TmCons(n1, zero, v1)),
                  TmTail(TmPred(n2), TmTail(n2, v2)))
              )
            )
          )
        )
      )
    )
  )


(* --------------- test --------------- *)

(* test sum *)
let test1 = TmApp(TmApp(sum, three), vec3)

(* test lenless *)
let test2 = TmApp(TmApp(TmApp(TmApp(lenless, two), three), vec2), vec3)

(* test even *)
let test3 = TmApp(TmApp(TmApp(evens, three), vec3), zero)

(* test snoc *)
let test4 = TmApp(TmApp(TmFunApp("snoc", snoc, [three]), vec3), TmHead(two, vec2))

(* test append *)
let test5 = TmApp(TmApp(TmApp(TmApp(append, two), three), vec3), vec2)

(* test f *)
let test6 = TmApp(TmApp(TmFunApp("f", f, [three; three]), vec3), vec3)


(* --------------- utilities for printing --------------- *)

let prty t = 
  let () = printType ctx (typeof ctx mctx t); pr"\n" in
  pr "The term passed the type checking and termination checking.\n"
let prtm t = printTerm ctx (eval ctx t); pr"\n"
let detm t = debugTerm ctx (eval ctx (eval ctx t)); pr"\n"