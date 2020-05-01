open Syntax
open Eval
open Typecheck

let ctxlen = 0
let ctx = []
let mctx = []

let fool = 
  TmFix(
    TmAbs("fool", TyPi("X",TyNat,TyBool),
      TmAbs("x", TyNat,
        TmIf(
          TmIsZero(TmVar(0, ctxlen+2)),
          TmTrue,
          TmApp(TmVar(1, ctxlen+2), TmPred(TmVar(0, ctxlen+2)))
        )
      )
    )
  )

let fool_2 = TmApp(fool, TmSucc(TmZero))

let plus = 
  TmFix(
    TmAbs("plus", TyPi("X", TyNat, TyPi("Y", TyNat, TyNat)),
      TmAbs("x", TyNat, 
        TmAbs("y", TyNat,
          TmIf(
            TmIsZero(TmVar(1, ctxlen+3)),
            TmVar(0, ctxlen+3),
            TmApp(TmApp(TmVar(2, ctxlen+3), TmPred(TmVar(1, ctxlen+3))), TmSucc(TmVar(0, ctxlen+3)))
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

let nottrue = TmApp(notbool, TmTrue)
let notfalse = TmApp(notbool, TmFalse)

let plus_1_2 = TmApp(TmApp(plus, TmSucc(TmZero)), TmSucc(TmSucc(TmZero)))

let zero = TmZero
let one = TmSucc(TmZero)
let two = TmSucc(one)
let three = TmSucc(two)

let iseven_1 = TmApp(iseven, one)
let iseven_2 = TmApp(iseven, two)



let prty t = printType ctx (typeof ctx mctx t); pr"\n"
let prtm t = printTerm ctx (eval ctx t); pr"\n"