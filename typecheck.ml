open Format
open Syntax
open Metric
open Eval

let global_count = ref 0
  
let rec checkkind ctx ki = match ki with
    KiStar -> ()
  | KiPi(x, tyT, ki') -> 
      let () = kindstar ctx tyT in
      let ctx' = addbinding ctx x (VarBind(tyT)) 
      in checkkind ctx' ki'

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
            (* NOTE: should be [x->t2]kiK; not needed currently *)
            else (debugType ctx tyT1; debugType ctx tyT2; 
                  error "[kindof error] parameter type not equivalence")
        | _ -> error "[kindof error] pi kind expected"
      )
  | TySigma(x, tyT1, tyT2) ->
      let () = kindstar ctx tyT1 in
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let () = kindstar ctx' tyT2 in
      KiStar
  | TyBool -> KiStar
  | TyNat -> KiStar
  | TyVector(t) -> KiStar

and kindstar ctx tyT = 
  if kindof ctx tyT = KiStar then ()
  else error "[kindstar error] kind not equal to KiStar"

and typeof ctx mctx t = 
  typeof' false ctx mctx t "dummy"(* dummy f *)

and typeofLess ctx mctx t f = 
  typeof' true ctx mctx t f

and typeof' isless ctx mctx t f = 
let rec type_of isless ctx mctx t = 
  (* let _ = global_count := !global_count + 1 in 
  if !global_count >= 200 then error "TOO MANY!!!!"
  else 
  let () = pr"type_of "; debugTerm ctx t; pr"\n"; pr"ctx ["; printctx ctx; pr"]\n" in *)
  match t with
    TmVar(x, _) -> getTypeFromContext ctx x
  | TmAbs(x, tyS, t) ->
      let () = kindstar ctx tyS in
      let ctx' = addbinding ctx x (VarBind(tyS)) in 
      let ctx' = shiftContext ctx' 1 in  (* 应该先addbind后shift，shift的原因是addbind后TxVar变了 *)
      let mctx = shiftMetricContext mctx 1 in
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
          (let () = pr "ctx["; printctx ctx;pr"]\n";debugType ctx tyS1;pr"\n";debugType ctx tyS2;pr"\n" in 
          error "[typeof error: TmApp] parameter type mismatch")
      | _ -> error "[typeof error: TmApp] Pi type expected")

  | TmPair(t1, t2, ty) ->
      let () = kindstar ctx ty in
      (match ty with
        TySigma(_, tyT1, tyT2) ->
          let tyT1' = type_of isless ctx mctx t1 in
          if tyeqv ctx tyT1 tyT1' then
            let tyT2' = type_of isless ctx mctx t2 in
            let tyT2subst = tySubstTop t1 tyT2 in
            if tyeqv ctx tyT2subst tyT2' then ty
            else 
              (debugType ctx tyT2'; pr"\n"; debugType ctx tyT2subst; pr"\n";
              error "[typeof error: TmPair] the second element mismatch")
          else error "[typeof error: TmPair] the first element mismatch"
      | _ -> error "[typeof error: TmPair] Sigma type expected")
  | TmProj1(t) ->
      let tyT = type_of isless ctx mctx t in
      (match tyT with
        TySigma(_, tyT1, tyT2) -> tyT1
      | _ -> error "[typeof error: TmProj1] Sigma type expected")
  | TmProj2(t) ->
      let tyT = type_of isless ctx mctx t in
      (match tyT with
        TySigma(_, tyT1, tyT2) -> tySubstTop (TmProj1(t)) tyT2
      | _ -> error "[typeof error: TmProj2] Sigma type expected")

  | TmTrue -> 
      TyBool
  | TmFalse -> 
      TyBool
  | TmIf(t1, t2, t3) ->
      if (=) (type_of isless ctx mctx t1) TyBool then
        let tyT2 = type_of isless ctx mctx t2 in
        let tyT3 = type_of isless ctx mctx t3 in
        if tyeqv ctx tyT2 tyT3 then tyT2
        else (debugType ctx tyT2; pr" "; debugType ctx tyT3; pr"\n"; 
              error "[typeof error: TmIf] arms of conditional have different types")
      else error "[typeof error: TmIf] guard of conditional not a boolean"

  | TmZero ->
      TyNat
  | TmSucc(t1) ->
      if tyeqv ctx (type_of isless ctx mctx t1) TyNat then TyNat
      else error "[typeof error: TmSucc] argument of succ is not a number"
  | TmPred(t1) ->
      if tyeqv ctx (type_of isless ctx mctx t1) TyNat then TyNat
      else error "[typeof error: TmPred] argument of pred is not a number"
  | TmIsZero(t1) ->
      if tyeqv ctx (type_of isless ctx mctx t1) TyNat then TyBool
      else error "[typeof error: TmIsZero] argument of iszero is not a number"

  | TmFix(t1) ->
      let tyT1 = type_of isless ctx mctx t1 in
      (match tyT1 with
        TyPi(_, tyT11, tyT12) ->
          if tyeqvFix ctx tyT11 tyT12 0 then tyT11
          else (debugType ctx tyT11; pr"\n"; debugType ctx tyT12; pr"\n";
                error "[typeof error: TmFix] result of body not compatible with domain")
      | _ -> error "[typeof error: TmFix] arrow type expected")

  | TmFun(x, tyMe, ty, t) ->
      if not (List.fold_left (&&) true (List.map (tyeqv ctx TyNat) tyMe)) 
        then error "[typeof error: TmFun] metric not Nat"
      else 
      let () = kindstar ctx ty in
      let c = List.length tyMe in
      (* add f into ctx *)
      let tyF = generatePiType ty c x in
      let ctx' = addbinding ctx x (VarBind(tyF)) in 
      let ctx' = shiftContext ctx' 1 in  
      let mctx = shiftMetricContext mctx 1 in
      (* add metric of f into ctx *)
      let ctx' = addbindingOfMetric ctx' c x in
      let ctx' = shiftContext ctx' c in
      let mctx = shiftMetricContext mctx c in
      (* get metric *)
      let me = generateMetric (ctxlength ctx') c in
      let mctx' = addmetric mctx x me in  
      let tyT = typeofLess ctx' mctx' t x in 
      (* if tyeqv ctx' tyT ty then tyF *)
      if tyeqvFix ctx' tyT ty c then tyF
      else (debugType ctx' tyT; pr" "; debugType ctx' ty; pr"\n"; 
            error "[typeof error: TmFun] type not match")
      (* NOTE: 使用tyeqvFix的原因见下，一般不用也行 *)

  | TmFunApp(x, t, me) ->
      (* let () = pr "-----------TmFunApp "; debugTerm ctx t; pr"\n" in *)
      let tyMe = List.map (type_of isless ctx mctx) me in
      if not (List.fold_left (&&) true (List.map (tyeqv ctx TyNat) tyMe)) 
        then error "[typeof error: TmFunApp] metric not Nat"
      else 
      let ty = type_of isless ctx mctx t in 
      let res = substMetric me ty in
        (* (match ty with 
          TyPi(_, TyNat, tyT) -> tySubstTop me tyT
        | _ -> error "[TmFunApp] arrow type expected") in *)
      if not isless then res
      else if not (f = x) then res
      else let me0 = getmetric mctx f in 
      (match me0 with
        None -> error "[typeof< error: TmFunApp] metric not found"
      | Some(me0') ->
          if metricless ctx mctx me me0' then res
          else error "[typeof< error: TmFunApp] metric doesn't descent")

  | TmNil -> TyVector(TmZero)
  | TmCons(n, t1, t2) ->
      let tyN = type_of isless ctx mctx n in
      let tyT1 = type_of isless ctx mctx t1 in
      let tyT2 = type_of isless ctx mctx t2 in
      if not (tyeqv ctx tyN TyNat) 
      then error "[typeof error: TmCons] first argument not Nat"
      else if not (tyeqv ctx tyT1 TyNat)
      then error "[typeof error: TmCons] second argument not Nat"
      else if not (tyeqv ctx tyT2 (TyVector(n))) 
      then 
        let () = debugType ctx tyT2; pr " "; debugType ctx (TyVector(n)) in
        error "[typeof error: TmCons] Vector n mismatch"
      else TyVector(TmSucc(n))
  | TmIsNil(n, t1) ->
      let tyN = type_of isless ctx mctx n in
      let tyT1 = type_of isless ctx mctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "[typeof error: TmIsNil] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then 
      (printctx ctx; pr"\n";
      debugType ctx tyT1; pr"\n"; debugType ctx (TyVector(n));
      error "[typeof error: TmIsNil] Vector n mismatch")
      else TyBool
  | TmHead(n, t1) ->
      let tyN = type_of isless ctx mctx n in
      let tyT1 = type_of isless ctx mctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "[typeof error: TmHead] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then error "[typeof error: TmHead] Vector n mismatch"
      else TyNat
  | TmTail(n, t1) ->
      let tyN = type_of isless ctx mctx n in
      let tyT1 = type_of isless ctx mctx t1 in
      if not (tyeqv ctx tyN TyNat) 
      then error "[typeof error: TmTail] first argument not Nat"
      else if not (tyeqv ctx tyT1 (TyVector(n))) 
      then error "[typeof error: TmTail] Vector n mismatch"
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
  (* let () = (pr "tyeqv\nty1: "; debugType ctx ty1; pr"\nty2: "; debugType ctx ty2; pr"\n") in *)
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
  | (TySigma(x, tyS1, tyS2), TySigma(_, tyT1, tyT2)) ->
      (* let () = pr x; pr " "; pr y; pr "\n" in *)
      tyeqv ctx tyS1 tyT1 &&
      let ctx' = addbinding ctx x (VarBind(tyS1)) 
      in tyeqv ctx' tyS2 tyT2
  | (TyVector(n1), TyVector(n2)) ->
      tmeqv ctx n1 n2
  | _ -> false
  
and tmeqv ctx tm1 tm2 = 
    (* let () = (pr "tmeqv\ntm1: "; debugTerm ctx tm1; pr"\ntm2: "; debugTerm ctx tm2; pr"\n") in *)
    if tm1 = tm2 then true (* NOTE: This is a trick. For there are some bugs that the tmeqv will never halt. *)
    else 
    let v1 = eval ctx tm1 in
    let v2 = eval ctx tm2 in
    (* let () = (pr "tmeqv v "; debugTerm ctx v1; pr" "; debugTerm ctx v2; pr"\n"; pr (string_of_bool (v1 = v2)); pr"\n") in *)
    if natcheck ctx v1 && natcheck ctx v2 then
      nateqv ctx v1 v2
    else match (v1, v2) with
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
      | (TmPair(t1, t2, tyT), TmPair(s1, s2, tyS)) ->
          tmeqv ctx t1 s1 && tmeqv ctx t2 s2 && tyeqv ctx tyT tyS 
      | (TmProj1(t1), TmProj1(t2)) ->
          tmeqv ctx t1 t2
      | (TmProj2(t1), TmProj2(t2)) ->
          tmeqv ctx t1 t2
      | _ -> v1 = v2

  (* NOTE: Fix后缀的是为了处理fix时lambda f:ty1.ty2的ty1和ty2比较，ty2中会多绑定一个变量(递归函数f)的情况
    TxVar中>=c的都会调整一下（前一个+1）来比较
    其实一般来说f就是ctx中的第一个变量了，所以ty1和ty2中不会有>=c的TxVar存在，用不用这个无所谓
    手动在ctx里加了些全局绑定并使用了才会需要这个 *)

and natcheck ctx t = 
  match t with
    TmZero -> true
  | TmVar(x, _) -> typeof ctx [] t = TyNat
  | TmSucc(t1) -> natcheck ctx t1
  | TmPred(t1) -> natcheck ctx t1
  | _ -> false

and nateqv ctx t1 t2 = 
  (* let () = (pr "nateqv tm "; debugTerm ctx t1; pr" "; debugTerm ctx t2; pr"\n") in *)
  let rec calc me cnt = match me with
    TmVar(x,_) -> (x, cnt)
  | TmZero -> (-1, 0)
  | TmSucc(t) -> calc t (cnt+1)
  | TmPred(t) -> calc t (cnt-1)
  | _ -> (debugTerm ctx me; pr"\n"; error "[nateqv error] term not Nat")
  in
  let (x1, c1) = calc t1 0 in
  let (x2, c2) = calc t2 0 in
  if x1 != x2 then 
    (pr "[nateqv] nat not comparable\n"; false)
    (* (debugTerm ctx t1; pr" "; debugTerm ctx t2; pr"\n"; error "[nateqv error] nat not comparable") *)
  else c1 = c2

  (* NOTE: nateqv还么有加到Fix的里面。等着把这两个合并吧 *)

and tmeqvFix ctx tm1 tm2 c =    
    if tm1 = tm2 then true (* NOTE:This is a trick. For there are some bugs that the tmeqv will never halt. *)
    else 
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
      | (TmPair(t1, t2, tyT), TmPair(s1, s2, tyS)) ->
          tmeqvFix ctx t1 s1 c && tmeqvFix ctx t2 s2 c && tyeqvFix ctx tyT tyS c
      | (TmProj1(t1), TmProj1(t2)) ->
          tmeqvFix ctx t1 t2 c
      | (TmProj2(t1), TmProj2(t2)) ->
          tmeqvFix ctx t1 t2 c
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
  | (TySigma(x, tyS1, tyS2), TySigma(_, tyT1, tyT2)) ->
      tyeqvFix ctx tyS1 tyT1 c &&
      let ctx' = addbinding ctx x (VarBind(tyS1)) 
      in tyeqvFix ctx' tyS2 tyT2 c
  | (TyVector(n1), TyVector(n2)) ->
      tmeqvFix ctx n1 n2 c
  | _ -> false