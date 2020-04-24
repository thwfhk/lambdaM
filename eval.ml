open Syntax
open Metric

let rec isnumericval ctx t = match t with
    TmZero -> true
  | TmSucc(t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmTrue -> true
  | TmFalse -> true
  | t when isnumericval ctx t -> true
  | TmNil -> true
  | TmCons(n, t1, t2) -> 
      isnumericval ctx n && isnumericval ctx t1 && isval ctx t2
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
      derivedformTmFun s tyMe ty t
  | TmFunApp(s, t, me) ->
      derivedformTmFunApp s t me

  | _ ->
      raise NoRuleApplies (* include TmVar *)

let rec eval ctx t =
  try let t' = eval1 ctx t
      in eval ctx t'
  with NoRuleApplies -> t