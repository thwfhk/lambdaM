open Format
open Syntax

let rec isnumericval ctx t = match t with
    TmZero -> true
  | TmSucc(t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmTrue -> true
  | TmFalse -> true
  | t when isnumericval ctx t -> true
  | TmNil -> true
  | TmCons(n, t1, t2) -> isnumericval ctx n && isval ctx t1 && isval ctx t2
  | TmAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 ctx t = match t with
    TmApp(TmAbs(x, tyT11, t12), v2) when isval ctx v2 ->
      termSubstTop v2 t12
  | TmApp(v1, t2) when isval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmApp(v1, t2')
  | TmApp(t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmApp(t1', t2)

  | TmIf(TmTrue, t2, t3) ->
      t2
  | TmIf(TmFalse, t2, t3) ->
      t3
  | TmIf(t1, t2, t3) ->
      let t1' = eval1 ctx t1 in
      TmIf(t1', t2, t3)

  | TmSucc(t1) ->
      let t1' = eval1 ctx t1 in
      TmSucc(t1')
  | TmPred(TmZero) ->
      TmZero
  | TmPred(TmSucc(nv1)) when isnumericval ctx nv1 ->
      nv1
  | TmPred(t1) ->
      let t1' = eval1 ctx t1 in
      TmPred(t1')
  | TmIsZero(TmZero) ->
      TmTrue
  | TmIsZero(TmSucc(nv1)) when isnumericval ctx nv1 ->
      TmFalse
  | TmIsZero(t1) ->
      let t1' = eval1 ctx t1 in
      TmIsZero(t1')

  | TmCons(n, v1, t2) when isnumericval ctx v1 ->
      let t2' = eval1 ctx t2 in
      TmCons(n, v1, t2')
  | TmCons(n, t1, t2) ->
      let t1' = eval1 ctx t1 in
      TmCons(n, t1', t2)
  | TmIsNil(n, TmNil) ->
      TmTrue
  | TmIsNil(n, TmCons(m, t1, t2)) ->
      TmFalse
  | TmIsNil(n, t1) ->
      let t1' = eval1 ctx t1 in
      TmIsNil(n, t1')
  | TmHead(n, TmCons(m, v1, t2)) when isnumericval ctx v1 ->
      v1
  | TmHead(n, t1) ->
      let t1' = eval1 ctx t1 in
      TmHead(n, t1')
  | TmTail(n, TmCons(m, t1, v2)) when isval ctx v2 ->
      v2
  | TmTail(n, t1) ->
      let t1' = eval1 ctx t1 in
      TmTail(n, t1')
  (* NOTE: 这里对于TmHead和TmTail只关心了他的返回值是value的时候就可以返回 *)

  | TmFix(v1) as t when isval ctx v1 ->
      (match v1 with
         TmAbs(_,_,t12) -> termSubstTop t t12
       | _ -> raise NoRuleApplies)
  | TmFix(t1) ->
      let t1' = eval1 ctx t1
      in TmFix(t1')

  | TmFun(s, tyMe, ty, t) ->
      TmFix(TmAbs(s, TyPi("n", TyNat, ty), TmAbs("n", TyNat, t)))
  | TmFunApp(s, t, me) ->
      TmApp(t, me)

  | _ ->
      raise NoRuleApplies (* include TmVar *)

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t


let rec checkkind ctx ki = match ki with
    KiStar -> ()
  | KiPi(x, tyT, ki') -> 
      let () = kindstar ctx tyT in
      let ctx' = addbinding ctx x (VarBind(tyT)) 
      in checkkind ctx' ki'

(* TODO: kindof好像也应该带着mctx叭，简单的例子没啥影响 *)
and kindof ctx tyT = match tyT with
    TyVar(x, _) -> getKindFromContext ctx x
  | TyPi(x, tyT1, tyT2) ->
      let () = kindstar ctx tyT1 in
      let ctx' = addbinding ctx x (VarBind(tyT1)) in 
      let () = kindstar ctx' tyT2 in
      KiStar
  | TyApp(tyS, t) ->
      let ki = kindof ctx tyS in
      let tyT2 = typeof ctx emptymctx t in
      (
        match ki with 
          KiPi(_, tyT1, kiK) ->
            if tyeqv ctx tyT1 tyT2 then kiK 
            (* should be [x->t2]kiK; maybe it is not needed in the current implementation *)
            else (printType ctx tyT1; printType ctx tyT2; 
                  error "kindof error: parameter type not equivalence")
        | _ -> error "kindof error: pi kind expected"
      )
  | TyBool -> KiStar
  | TyNat -> KiStar
  | TyVector(t) -> KiStar

and kindstar ctx tyT = 
  if kindof ctx tyT = KiStar then ()
  else error "kind not equal to KiStar"

and typeof ctx mctx t = 
  typeof' false ctx mctx t "dummy"(* dummy f *)

and typeofLess ctx mctx t f = 
  typeof' true ctx mctx t f

and typeof' isless ctx mctx t f = 
  let rec type_of isless ctx mctx t = match t with
    TmVar(x, _) -> getTypeFromContext ctx x
  | TmAbs(x, tyS, t) ->
      let () = kindstar ctx tyS in
      let ctx' = addbinding ctx x (VarBind(tyS)) in 
      let ctx' = shiftContext ctx' in  (* 应该先addbind后shift，shift的原因是addbind后TxVar变了 *)
      let mctx = shiftMetricContext mctx in
      let tyT = type_of isless ctx' mctx t in
      TyPi(x, tyS, tyT)
  | TmApp(t1, t2) ->
      let ty = type_of isless ctx mctx t1 in
      let tyS2 = type_of isless ctx mctx t2 in 
      (* let () = debugType ctx ty;pr"\n" in *)
      (match ty with
          TyPi(_, tyS1, tyT) ->
            if tyeqv ctx tyS1 tyS2 then tySubstTop t2 tyT (* [x->t2]tyT *)
            else 
            let () = printctx ctx;pr"\n";debugType ctx tyS1;pr"\n";debugType ctx tyS2;pr"\n" in 
            error "typeof error: parameter type mismatch"
        | _ -> error "typeof error: [TmApp] arrow type expected")

  | TmTrue -> 
      TyBool
  | TmFalse -> 
      TyBool
  | TmIf(t1, t2, t3) ->
      if (=) (type_of isless ctx mctx t1) TyBool then
        let tyT2 = type_of isless ctx mctx t2 in
        if (=) tyT2 (type_of isless ctx mctx t3) then tyT2
        else error "arms of conditional have different types"
      else error "guard of conditional not a boolean"

  | TmZero ->
      TyNat
  | TmSucc(t1) ->
      if tyeqv ctx (type_of isless ctx mctx t1) TyNat then TyNat
      else error "argument of succ is not a number"
  | TmPred(t1) ->
      if tyeqv ctx (type_of isless ctx mctx t1) TyNat then TyNat
      else error "argument of pred is not a number"
  | TmIsZero(t1) ->
      if tyeqv ctx (type_of isless ctx mctx t1) TyNat then TyBool
      else error "argument of iszero is not a number"

  | TmFix(t1) ->
      let tyT1 = type_of isless ctx mctx t1 in
      (match tyT1 with
        TyPi(_, tyT11, tyT12) ->
          if tyeqvFix ctx tyT11 tyT12 0 then tyT11
          else (debugType ctx tyT11; pr"\n"; debugType ctx tyT12; pr"\n";
                error "result of body not compatible with domain")
      | _ -> error "typeof error: [TmFix] arrow type expected")

  | TmFun(x, tyMe, ty, t) ->
      if not (tyeqv ctx tyMe TyNat) then error "[TmFun] metric not Nat"
      else 
      let () = kindstar ctx ty in
      let ctx' = addbinding ctx x (VarBind(TyPi("metric_"^x, TyNat, ty))) in 
      let ctx' = shiftContext ctx' in  (* 已经将f加入ctx里 *)
      let mctx = shiftMetricContext mctx in
      let ctx' = addbinding ctx' ("metric_"^x) (VarBind(TyNat)) in (* 加入n，也就是f的metric *)
      let ctx' = shiftContext ctx' in
      (* let ctxty = addbinding ctx ("metric_"^x) (VarBind(TyNat)) in *)
      (* let ctxty = shiftContext ctxty in *)
      let mctx = shiftMetricContext mctx in
      let me = TmVar(0, ctxlength ctx') in
      let mctx' = addmetric mctx x me in  (* 所以mctx里也要shift  *)
      let tyT = typeofLess ctx' mctx' t x in 
      if tyeqv ctx' tyT ty then TyPi("metric_"^x, TyNat, ty)
      else (debugType ctx' tyT; pr" "; debugType ctx' ty; pr"\n"; error "[TmFun] type not match")
      (* FIXME: 这里稍微有一点bug，见notes说明 *)

  | TmFunApp(x, t, me) ->
      let tyMe = type_of isless ctx mctx me in
      if not (tyeqv ctx tyMe TyNat) then error "[TmFunApp] metric not Nat"
      else 
      let ty = type_of isless ctx mctx t in 
      let res = (match ty with 
          TyPi(_, TyNat, tyT) -> tySubstTop me tyT
        | _ -> error "[TmFunApp] arrow type expected") in
      if not isless then res
      else if not (f = x) then res
      else let me0 = getmetric mctx f in 
      (match me0 with
        None -> error "typeof< error: [TmFunApp] metric not found"
      | Some(me0') ->
          if metricless ctx mctx me me0' then res
          else error "typeof< error: [TmFunApp] metric doesn't descent")

  | TmNil -> TyVector(TmZero)
  | TmCons(n, t1, t2) ->
      let tyN = type_of isless ctx mctx n in
      let tyT1 = type_of isless ctx mctx t1 in
      let tyT2 = type_of isless ctx mctx t2 in
      if not (tyeqv ctx tyN TyNat) 
      then error "typeof error: [TmCons] first argument not Nat"
      else if not (tyeqv ctx tyT1 TyNat)
      then error "typeof error: [TmCons] second argument not Nat"
      else if not (tyeqv ctx tyT2 (TyVector(n))) 
      then 
      let () = printType ctx tyT2; pr " "; printTerm ctx n in
      error "typeof error: [TmCons] Vector n mismatch"
      else TyVector(TmSucc(n))
  | TmIsNil(n, t1) ->
      let tyN = type_of isless ctx mctx n in
      let tyT1 = type_of isless ctx mctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "typeof error: [TmIsNil] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then error "typeof error: [TmIsNil] Vector n mismatch"
      else TyBool
  | TmHead(n, t1) ->
      let tyN = type_of isless ctx mctx n in
      let tyT1 = type_of isless ctx mctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "typeof error: [TmHead] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then error "typeof error: [TmHead] Vector n mismatch"
      else TyNat
  | TmTail(n, t1) ->
      let tyN = type_of isless ctx mctx n in
      let tyT1 = type_of isless ctx mctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "typeof error: [TmTail] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then error "typeof error: [TmTail] Vector n mismatch"
      else TyVector(TmPred(n))
  in type_of isless ctx mctx t

and kindeqv ctx ki1 ki2 = match (ki1, ki2) with
    (KiStar, KiStar) -> true
  | (KiPi(x, tyT1, kiK1), KiPi(_, tyT2, kiK2)) ->
      tyeqv ctx tyT1 tyT2 &&
      let ctx' = addbinding ctx x (VarBind(tyT1))
      in kindeqv ctx' kiK1 kiK2
  | _ -> false

and tyeqv ctx ty1 ty2 = 
  (* let () = (pr "tyeqv "; debugType ctx ty1; pr" "; debugType ctx ty2; pr"\n") in *)
  match (ty1, ty2) with
    (TyBool, TyBool) -> true
  | (TyNat, TyNat) -> true
  | (TyVar(x1,_), TyVar(x2,_)) -> x1 = x2
  | (TyPi(x, tyS1, tyS2), TyPi(_, tyT1, tyT2)) ->
      tyeqv ctx tyS1 tyT1 &&
      let ctx' = addbinding ctx x (VarBind(tyS1)) 
      in tyeqv ctx' tyS2 tyT2
  | (TyApp(tyS1, t1), TyApp(tyS2, t2)) -> 
      tyeqv ctx tyS1 tyS2 && 
      (* let () = pr"TyApp tmeqv: ";pr (string_of_bool (tmeqv ctx t1 t2));pr"\n" in *)
      tmeqv ctx t1 t2
  | (TyVector(n1), TyVector(n2)) ->
      tmeqv ctx n1 n2
  | _ -> false
  
and tmeqv ctx tm1 tm2 = 
    (* let () = (pr "tmeqv tm "; debugTerm ctx tm1; pr" "; debugTerm ctx tm2; pr"\n") in *)
    let v1 = eval ctx tm1 in
    let v2 = eval ctx tm2 in
    (* let () = (pr "tmeqv v "; debugTerm ctx v1; pr" "; debugTerm ctx v2; pr"\n"; pr (string_of_bool (v1 = v2)); pr"\n") in *)
    match (v1, v2) with
        (TmTrue, TmTrue) -> true
      | (TmFalse, TmFalse) -> true
      | (TmIf(t1, t2, t3), TmIf(s1, s2, s3)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2 && tmeqv ctx t3 s3
      | (TmZero, TmZero) -> true
      | (TmSucc(t1), TmSucc(s1)) -> tmeqv ctx t1 s1
      | (TmPred(t1), TmPred(s1)) -> tmeqv ctx t1 s1
      | (TmIsZero(t1), TmIsZero(s1)) -> tmeqv ctx t1 s1
      | (TmNil, TmNil) -> true
      | (TmCons(t1, t2, t3), TmCons(s1, s2, s3)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2 && tmeqv ctx t3 s3
      | (TmIsNil(t1, t2), TmIsNil(s1,s2)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2
      | (TmHead(t1, t2), TmHead(s1,s2)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2
      | (TmTail(t1, t2), TmTail(s1,s2)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2
      | (TmApp(t1, t2), TmApp(s1,s2)) -> 
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2
      | (TmAbs(_, tyT1, t2), TmAbs(_, tyS1, s2)) ->
          tyeqv ctx tyT1 tyS1 && tmeqv ctx t2 s2
      | (TmVar(x1, _), TmVar(x2, _)) -> x1 = x2
      | _ -> v1 = v2

and tmeqvFix ctx tm1 tm2 c=    
    (* let () = (pr "tmeqv tm "; debugTerm ctx tm1; pr" "; debugTerm ctx tm2; pr"\n") in *)
    let v1 = eval ctx tm1 in
    let v2 = eval ctx tm2 in
    (* let () = (pr "tmeqv v "; debugTerm ctx v1; pr" "; debugTerm ctx v2; pr"\n"; pr (string_of_bool (v1 = v2)); pr"\n") in *)
    match (v1, v2) with
        (TmTrue, TmTrue) -> true
      | (TmFalse, TmFalse) -> true
      | (TmIf(t1, t2, t3), TmIf(s1, s2, s3)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c && tmeqvFix ctx t3 s3 c
      | (TmZero, TmZero) -> true
      | (TmSucc(t1), TmSucc(s1)) -> tmeqvFix ctx t1 s1 c
      | (TmPred(t1), TmPred(s1)) -> tmeqvFix ctx t1 s1 c
      | (TmIsZero(t1), TmIsZero(s1)) -> tmeqvFix ctx t1 s1 c
      | (TmNil, TmNil) -> true
      | (TmCons(t1, t2, t3), TmCons(s1, s2, s3)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c && tmeqvFix ctx t3 s3 c
      | (TmIsNil(t1, t2), TmIsNil(s1,s2)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c
      | (TmHead(t1, t2), TmHead(s1,s2)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c
      | (TmTail(t1, t2), TmTail(s1,s2)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c
      | (TmApp(t1, t2), TmApp(s1,s2)) -> 
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c
      | (TmAbs(_, tyT1, t2), TmAbs(_, tyS1, s2)) ->
          tyeqvFix ctx tyT1 tyS1 c && tmeqvFix ctx t2 s2 (c+1)
      | (TmVar(x1, _), TmVar(x2, _)) -> if x1>=c then x1+1 = x2 else x1 = x2
      | _ -> v1 = v2

  
and tyeqvFix ctx ty1 ty2 c = 
    (* let () = printctx ctx;pr " "; debugType ctx ty1; pr" "; debugType ctx ty2; pr"\n" in *)
    match (ty1, ty2) with 
    (TyBool, TyBool) -> true
  | (TyNat, TyNat) -> true
  | (TyVar(x1,_), TyVar(x2,_)) -> if x1>=c then x1+1 = x2 else x1 = x2
  (* ty2比ty1的ctx多了一个变量绑定，但是用的ctx是ty1的 *)
  | (TyPi(x, tyS1, tyS2), TyPi(_, tyT1, tyT2)) ->
      tyeqvFix ctx tyS1 tyT1 c &&
      let ctx' = addbinding ctx x (VarBind(tyS1)) 
      in tyeqvFix ctx' tyS2 tyT2 (c+1)
  | (TyApp(tyS1, t1), TyApp(tyS2, t2)) -> 
      tyeqvFix ctx tyS1 tyS2 c && tmeqvFix ctx t1 t2 c
  | (TyVector(n1), TyVector(n2)) ->
      tmeqvFix ctx n1 n2 c
  | _ -> false

and metricless ctx mctx me me0 =
  let rec calc me cnt = match me with
      TmVar(x,_) -> (x, cnt)
    | TmSucc(t) -> calc t (cnt+1)
    | TmPred(t) -> calc t (cnt-1)
    | _ -> error "metricless error: metric not Nat"
  in 
  let (x1, c1) = calc me 0 in
  let (x2, c2) = calc me0 0 in
  if x1 != x2 then false
  else c1 < c2
