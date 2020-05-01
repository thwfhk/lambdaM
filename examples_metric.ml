open Syntax
open Eval
open Typecheck

let ctxlen = 0
let ctx = []
let mctx = []

let zero = TmZero
let one = TmSucc(TmZero)
let two = TmSucc(one)
let three = TmSucc(two)

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

let vec3 = TmApp(TmApp(TmApp(mkthree, one), two), three)
let vec2 = TmCons(one, one, TmCons(zero, two, TmNil))

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

let notbool = 
  TmAbs("b", TyBool, TmIf(TmVar(0, 2+ctxlen), TmFalse, TmTrue))

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

(* calculate the sum of a vector *)
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

(* a wrong sum which loops forever *)
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

let test1 = TmApp(TmApp(sum, three), vec3)

(* compare the length of two vectors using recursion *)
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

(* a wrong lenless which loops forever *)
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

let test2 = TmApp(TmApp(TmApp(TmApp(lenless, two), three), vec2), vec3)

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
              TmSucc(TmProj1(TmApp(TmApp(TmApp(evens, TmPred(n)), TmTail(n, v)), TmSucc(d)))),
              TmCons(
                TmProj1(TmApp(TmApp(TmApp(evens, TmPred(n)), TmTail(n, v)), TmSucc(d))),
                TmHead(n, v),
                TmProj2(TmApp(TmApp(TmApp(evens, TmPred(n)), TmTail(n, v)), TmSucc(d)))
              ),
              TySigma("m", TyNat, TyVector(TmVar(0, 5+ctxlen)))
            ),
            TmPair(
              TmProj1(TmApp(TmApp(TmApp(evens, TmPred(n)), TmTail(n, v)), TmSucc(d))),
              TmProj2(TmApp(TmApp(TmApp(evens, TmPred(n)), TmTail(n, v)), TmSucc(d))),
              TySigma("m", TyNat, TyVector(TmVar(0, 5+ctxlen)))
            )
          )
        )
      )
    )
  )

let test3 = TmApp(TmApp(TmApp(evens, three), vec3), zero)

let prty t = printType ctx (typeof ctx mctx t); pr"\n"
let prtm t = printTerm ctx (eval ctx t); pr"\n"