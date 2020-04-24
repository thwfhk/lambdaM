type ty = 
    TyVar of int * int
  | TyPi of string * ty * ty  
  | TyApp of ty * term
  | TyBool
  | TyNat
  | TyVector of term
  
and term =
    TmVar of int * int            (* De Bruijn index, current contex length *)
  | TmAbs of string * ty * term   
  | TmApp of term * term
  | TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term 
  | TmIsZero of term
  | TmFix of term
  | TmNil
  | TmCons of term * term * term (* n,x,v *)
  | TmIsNil of term * term
  | TmHead of term * term
  | TmTail of term * term
  | TmFun of  string * ty list * ty * term
  | TmFunApp of string * term * metric

and metric = term list

and kind = 
    KiStar
  | KiPi of string * ty * kind

type binding =
    NameBind               (* 只是占位 *)
  | VarBind of ty
  | TyVarBind of kind

type context = (string * binding) list  (* name * binding *)

type metricContext = (string * metric) list

type command =
  | Eval of term
  | Bind of string * binding

(* ---------------------------------------------------------------------- *)
(* Utilities *)

exception Exit

let pr = output_string stdout

let print x = output_string stdout x; flush stdout

let error x = pr x; pr " "; raise Exit

let rec prctx ctx = match ctx with
    [] -> ()
  | (x::xs) -> pr (fst x); pr" "; prctx xs



(* ---------------------------------------------------------------------- *)
(* Context management *)

let emptycontext = []

let ctxlength ctx = List.length ctx

let addbinding ctx x bind = (x,bind)::ctx (* 每次加入开头，index是0 *)

let addname ctx x = addbinding ctx x NameBind

let rec printctx ctx = 
  match ctx with
      [] -> ()
    | (x,_)::rest ->
        print x; print " "; printctx rest

let rec isnamebound ctx x =
  match ctx with
      [] -> false
    | (y,_)::rest ->
        if y=x then true
        else isnamebound rest x

let rec pickfreshname ctx x =
  if isnamebound ctx x then pickfreshname ctx (x^"'")
  else ((x,NameBind)::ctx), x

let index2name ctx x =
  try
    let (xn,_) = List.nth ctx x in xn
  with Failure _ -> error "[index2name] Variable lookup failure! "

let rec name2index ctx x =
  match ctx with
      [] -> error ("[name2index] Identifier " ^ x ^ " is unbound! ")
    | (y,_)::rest ->
        if y=x then 0
        else 1 + (name2index rest x)

(* ---------------------------------------------------------------------- *)
(* Shifting *)

(* c记录abstraction的层数 *)
let rec tmmap ontmvar ontyvar c t = 
  let rec walk c t = match t with
      TmVar(x, n) -> ontmvar c x n
    | TmAbs(s, ty, t) -> TmAbs(s, tymap ontmvar ontyvar c ty, walk (c+1) t)
    | TmApp(t1, t2) -> TmApp(walk c t1, walk c t2)
    | TmTrue -> TmTrue
    | TmFalse -> TmFalse
    | TmIf(t1, t2, t3) -> TmIf(walk c t1, walk c t2, walk c t3)
    | TmZero -> TmZero
    | TmSucc(t1) -> TmSucc(walk c t1)
    | TmPred(t1) -> TmPred(walk c t1)
    | TmIsZero(t1) -> TmIsZero(walk c t1)
    | TmFix(t1) -> TmFix(walk c t1)
    | TmNil -> TmNil
    | TmCons(n, t1, t2) -> TmCons(walk c n, walk c t1, walk c t2)
    | TmIsNil(n, t1) -> TmIsNil(walk c n, walk c t1)
    | TmHead(n, t1) -> TmHead(walk c n, walk c t1)
    | TmTail(n, t1) -> TmTail(walk c n, walk c t1)
    | TmFun(s, me, ty, t) -> 
        TmFun(s, List.map (tymap ontmvar ontyvar c) me, tymap ontmvar ontyvar (c+1) ty, walk (c+1) t)
    | TmFunApp(s, t, me) -> 
        TmFunApp(s, walk c t, List.map (walk c) me)
  in walk c t

and tymap ontmvar ontyvar c ty = 
  let rec walk c t = match t with
      TyVar(x, n) -> ontyvar c x n
    | TyPi(s, ty1, ty2) -> TyPi(s, walk c ty1, walk (c+1) ty2)
    | TyApp(ty, t) -> TyApp(walk c ty, tmmap ontmvar ontyvar c t)
    | TyBool -> TyBool
    | TyNat -> TyNat
    | TyVector(n) -> TyVector(tmmap ontmvar ontyvar c n)
  in walk c ty

(* \uparrow^d_c (t) *)
let termShiftAbove d c t =
  tmmap 
    (fun c x n -> if x >= c then TmVar(x+d, n+d) else TmVar(x, n+d))
    (fun c x n -> TyVar(x, n))  (* eval的时候TyVar不用管 *)
    c t

let termShift d t = termShiftAbove d 0 t

(* [j->s]t 其实只要用到j=0 *)
let termSubst j s t =
  tmmap
    (fun c x n -> if x=j+c then termShift c s else TmVar(x,n))
    (fun c x n -> TyVar(x,n)) (* eval的时候TyVar不用管 *) 
    0 t

(* [0->s]t加上外面去掉一层lambda *)
let termSubstTop s t = 
  termShift (-1) (termSubst 0 (termShift 1 s) t)

(* tyShift的时候TmVar和TyVar都要管， *)
let tyShiftAbove d c t =
  tymap 
    (fun c x n -> if x >= c then TmVar(x+d, n+d) else TmVar(x, n+d))
    (fun c x n -> if x >= c then TyVar(x+d, n+d) else TyVar(x, n+d))
    c t
let tyShift d t = tyShiftAbove d 0 t

(* tySubst的时候只会替换TmVar，TyVar不用管 *)
(* [j->s]t 其实只要用到j=0 *)
let tySubst j s t =
  tymap 
    (fun c x n -> if x=j+c then termShift c s else TmVar(x, n))
    (fun c x n -> TyVar(x, n))
    0 t
(* [0->s]t加上外面去掉一层lambda *)
let tySubstTop s t = 
  tyShift (-1) (tySubst 0 (termShift 1 s) t)

let rec shiftContext ctx c = match ctx with
    [] -> []
  | (x::xs) -> let (name, bind) = x in 
      let newbind = ( match bind with
          NameBind -> NameBind
        | VarBind(ty) -> VarBind(tyShift c ty)
        | TyVarBind(ki) -> TyVarBind(ki)   
        (* 按理说kind中也可能有type，也是需要shift的，但是先不管了吧 *)
      ) in (name, newbind) :: shiftContext xs c




(* ---------------------------------------------------------------------- *)
(* Context management (continued) *)

(* return the i-th bind in ctx *)
let rec getbinding ctx i =
  try
    let (_,bind) = List.nth ctx i in
    bind 
  with Failure _ -> error "[getbinding error] Variable lookup failure! "

let rec getTypeFromContext ctx i =
  match getbinding ctx i with
    VarBind(ty) -> ty
  | _ -> error "[getTypeFromContext error] Wrong kind of binding for variable "

let rec getKindFromContext ctx i =
  match  getbinding ctx i with
    TyVarBind(ki) -> ki
  | _ -> printctx ctx; error "[getKindFromContext error] Wrong kind of binding for variable "

(* ---------------------------------------------------------------------- *)

  

let rec printType ctx ty = match ty with
    TyBool -> 
      pr "Bool"
  | TyNat ->
      pr "Nat"
  | TyPi(x, ty1, ty2) ->
      let (ctx', x') = pickfreshname ctx x in
      pr"(Pi "; pr x'; pr ":"; printType ctx ty1; 
      pr "."; printType ctx' ty2; pr ")"
  | TyVar(x, n) ->
      if ctxlength ctx = n then
        pr (index2name ctx x)
      else
        (print"\n ctx:["; prctx ctx; pr"]";
        pr ("n:" ^ string_of_int n);pr" ";pr ("ctxlen:" ^ string_of_int (ctxlength ctx)); pr" "; 
        print (string_of_bool (ctxlength ctx = n)); pr" ";
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
        (print"\n ctx:["; prctx ctx; pr"]";
        pr ("n:" ^ string_of_int n);pr" ";pr ("ctxlen:" ^ string_of_int (ctxlength ctx)); pr" "; 
        print (string_of_bool (ctxlength ctx = n)); pr" ";
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
      pr "zero"
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
      pr"cons("; printTerm ctx n; pr","; printTerm ctx t1; pr","; printTerm ctx t2; pr")"
  | _ -> error "[printTerm error] Cases not include."


let rec debugType ctx ty = 
  match ty with
    TyBool -> 
      pr "Bool"
  | TyNat ->
      pr "Nat"
  | TyPi(x, ty1, ty2) ->
      let (ctx', x') = pickfreshname ctx x in
      pr"(Pi "; pr x'; pr ":"; debugType ctx ty1; 
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
    printTerm ctx t1;
    pr " ";
    printTerm ctx t2
  | TmAbs(x, tyT1, t2) -> 
    let (ctx', x') = pickfreshname ctx x in  (* 这里有将x加到ctx中！ *)
    pr "(lambda "; pr x'; pr ":"; printType ctx tyT1;
    pr "."; debugTerm ctx' t2; pr ")"
  | TmTrue -> 
    pr "true"
  | TmFalse ->
    pr "false"
  | TmIf(t1, t2, t3) ->
    pr "if "; debugTerm ctx t1; pr " then "; debugTerm ctx t2; pr " else "; debugTerm ctx t3
  | TmZero ->
    pr "zero"
  | TmSucc(t1) ->
    let rec check n t = match t with
        TmZero -> true
      | TmSucc(s) -> check (n+1) s
      | _ -> false
    in
    if check 0 t then 
      let rec f n t = match t with
          TmZero -> print (string_of_int n)
        | TmSucc(s) -> f (n+1) s
        | _ -> error "succ stuck encountered when printing"
      in f 0 t
    else (pr "succ("; debugTerm ctx t1; pr ")")
  | TmPred(t1) ->
    pr "pred("; debugTerm ctx t1; pr ")"
  | TmFun(s, me, ty, t) -> 
    pr ("fun "^s); 
    List.fold_left (fun x -> debugType ctx) () me; 
    debugType ctx ty; debugTerm ctx t 
  | _ -> error "Non-value encountered when printing."

(* TODO: 这个print和debug还应该完善一下 *)