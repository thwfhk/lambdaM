open Syntax

let rec printType ctx ty = match ty with
    TyBool -> 
      pr "Bool"
  | TyNat ->
      pr "Nat"
  | TyPi(x, ty1, ty2) ->
      let (ctx', x') = pickfreshname ctx x in
      pr"(Pi "; pr x'; pr ":"; printType ctx ty1; 
      pr "."; printType ctx' ty2; pr ")"
  | TySigma(x, ty1, ty2) ->
      let (ctx', x') = pickfreshname ctx x in
      pr"(Sigma "; pr x'; pr ":"; printType ctx ty1; 
      pr ".";
      printType ctx' ty2; pr ")"
  | TyVar(x, n) ->
      if ctxlength ctx = n then
        pr (index2name ctx x)
      else
        (print"\n ctx:["; printctx ctx; pr"]";
        pr ("n:" ^ string_of_int n);pr" ";pr ("ctxlen:" ^ string_of_int (ctxlength ctx)); pr" "; 
        print (string_of_bool (ctxlength ctx = n)); pr"\n";
        error ("[printType error] Unconsistency found! "))
  | TyApp(tyT1, t2) ->
      printType ctx tyT1;
      pr " ";
      printTerm ctx t2;
  | TyVector(n) ->
      pr "Vector("; printTerm ctx n; pr ")"

and printTerm ctx t = match t with
    TmVar(x, n) ->
      if ctxlength ctx = n then
        pr (index2name ctx x)
      else
        (print"\n ctx:["; printctx ctx; pr"]";
        pr ("n:" ^ string_of_int n);pr" ";pr ("ctxlen:" ^ string_of_int (ctxlength ctx)); pr" "; 
        print (string_of_bool (ctxlength ctx = n)); pr"\n";
        error ("[printTerm error] Unconsistency found! "))
  | TmApp(t1, t2) ->
      printTerm ctx t1;
      pr " ";
      printTerm ctx t2
  | TmAbs(x, tyT1, t2) -> 
      let (ctx', x') = pickfreshname ctx x in  (* 这里有将x加到ctx中！ *)
      pr "(lambda "; pr x'; pr ":"; printType ctx tyT1;
      pr "."; printTerm ctx' t2; pr ")"
  | TmTrue -> 
      pr "true"
  | TmFalse ->
      pr "false"
  | TmIf(t1, t2, t3) ->
      pr "if "; printTerm ctx t1; pr " then "; printTerm ctx t2; pr " else "; printTerm ctx t3
  | TmZero ->
      pr "0"
  | TmSucc(t1) ->
      let rec check t = match t with
          TmZero -> true
        | TmSucc(s) -> check s
        | _ -> false
      in
      if check t then 
        let rec f n t = match t with
            TmZero -> print (string_of_int n)
          | TmSucc(s) -> f (n+1) s
          | _ -> error "[printTerm error] succ stuck"
        in f 0 t
      else (pr "succ("; printTerm ctx t1; pr ")")
  | TmPred(t1) ->
      pr "pred("; printTerm ctx t1; pr ")"
  | TmNil -> 
      pr "nil"
  | TmCons(n, t1, t2) ->
      pr"cons("; printTerm ctx t1; pr","; printTerm ctx t2; pr")"
  | TmPair(t1, t2, _) ->
      pr"("; printTerm ctx t1; pr","; printTerm ctx t2; pr")"
  | _ -> error "[printTerm error] Cases not include."

and debugType ctx ty = 
  match ty with
    TyBool -> 
      pr "Bool"
  | TyNat ->
      pr "Nat"
  | TyPi(x, ty1, ty2) ->
      let (ctx', x') = pickfreshname ctx x in
      pr"(Pi "; pr x'; pr ":"; debugType ctx ty1; 
      pr "."; debugType ctx' ty2; pr ")"
  | TySigma(x, ty1, ty2) ->
      let (ctx', x') = pickfreshname ctx x in
      pr"(Sigma "; pr x'; pr ":"; debugType ctx ty1; 
      pr "."; debugType ctx' ty2; pr ")"
  | TyVar(x, n) ->
      (pr "TyVar("; pr (string_of_int x); pr")")
  | TyApp(tyT1, t2) ->
      debugType ctx tyT1;
      pr " ";
      debugTerm ctx t2;
  | TyVector(n) ->
      pr "Vector("; debugTerm ctx n; pr ")"

and debugTerm ctx t = match t with
    TmVar(x, n) ->
      (pr "TmVar("; pr (string_of_int x); pr")")
  | TmApp(t1, t2) ->
    debugTerm ctx t1;
    pr " ";
    debugTerm ctx t2
  | TmFunApp(s, t1, me) ->
    debugTerm ctx t1;
    pr " ";
    pr"["; prlist me (debugTerm ctx); pr"]"
  | TmAbs(x, tyT1, t2) -> 
    let (ctx', x') = pickfreshname ctx x in  (* 这里有将x加到ctx中！ *)
    pr "(lambda "; pr x'; pr ":"; debugType ctx tyT1;
    pr "."; debugTerm ctx' t2; pr ")"
  | TmTrue -> 
    pr "true"
  | TmFalse ->
    pr "false"
  | TmIf(t1, t2, t3) ->
    pr "if "; debugTerm ctx t1; pr " then "; debugTerm ctx t2; pr " else "; debugTerm ctx t3
  | TmZero ->
    pr "0"
  | TmIsZero(t1) ->
    pr "iszero("; debugTerm ctx t1; pr")"
  | TmIsNil(n, t1) ->
    pr "isnil("; debugTerm ctx t1; pr")"
  | TmSucc(t1) ->
    pr "succ("; debugTerm ctx t1; pr ")"
  | TmPred(t1) ->
    pr "pred("; debugTerm ctx t1; pr ")"
  | TmFun(s, me, ty, t) -> 
    pr ("fun "^s^" "); 
    List.fold_left (fun x -> debugType ctx) () me; 
    debugType ctx ty; debugTerm ctx t 
  | TmNil -> pr "nil"
  | TmHead(n, t) -> pr "head("; debugTerm ctx t; pr")"
  | TmTail(n, t) -> pr "tail("; debugTerm ctx t; pr")"
  | TmCons(n, t1, t2) ->
      pr"cons("; debugTerm ctx t1; pr","; debugTerm ctx t2; pr")"
  | TmPair(t1, t2, ty) ->
      pr"pair("; debugTerm ctx t1; pr","; debugTerm ctx t2; pr":"; debugType ctx ty; pr")"
  | TmProj1(t) -> pr "Proj1("; debugTerm ctx t; pr")"
  | TmProj2(t) -> pr "Proj2("; debugTerm ctx t; pr")"
  | TmFix(t) -> pr "Fix("; debugTerm ctx t; pr")"