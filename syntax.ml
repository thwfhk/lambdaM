type ty = 
    TyVar of int * int
  | TyPi of string * ty * ty  
  | TyApp of ty * term
  | TySigma of string * ty * ty
  | TyBool
  | TyNat
  | TyVector of term
  
and term =
    TmVar of int * int            (* De Bruijn index, current contex length *)
  | TmAbs of string * ty * term   
  | TmApp of term * term
  | TmPair of term * term * ty 
  | TmProj1 of term 
  | TmProj2 of term
  | TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term 
  | TmIsZero of term
  | TmFix of term
  | TmNil
  | TmCons of term * term * term 
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
    NameBind               
  | VarBind of ty
  | TyVarBind of kind

type context = (string * binding) list  (* name * binding *)

type metricContext = (string * metric) list

type command =
  | Eval of term
  | Bind of string * binding

(* ---------------------------------------------------------------------- *)
(* print *)

exception Exit

let pr = output_string stdout

let print x = output_string stdout x; flush stdout

let error x = pr x; pr " "; raise Exit

let rec prlist li f = match li with
    [] -> ()
  | (x::xs) -> f x; pr" "; prlist xs f

let rec printctx ctx = 
  match ctx with
      [] -> ()
    | (x,_)::rest ->
        print x; print " "; printctx rest


(* ---------------------------------------------------------------------- *)
(* Context management *)

let emptycontext = []

let ctxlength ctx = List.length ctx

let addbinding ctx x bind = (x,bind)::ctx (* 每次加入开头，index是0 *)

let addname ctx x = addbinding ctx x NameBind

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
(* Shifting *)

(* c记录abstraction的层数 *)
let rec tmmap ontmvar ontyvar c t = 
  let rec walk c t = match t with
      TmVar(x, n) -> ontmvar c x n
    | TmAbs(s, ty, t) -> TmAbs(s, tymap ontmvar ontyvar c ty, walk (c+1) t)
    | TmApp(t1, t2) -> TmApp(walk c t1, walk c t2)
    | TmPair(t1, t2, ty) -> TmPair(walk c t1, walk c t2, tymap ontmvar ontyvar c ty)
    | TmProj1(t1) -> TmProj1(walk c t1)
    | TmProj2(t1) -> TmProj2(walk c t1)
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
        let len = List.length me in
        TmFun(s, List.map (tymap ontmvar ontyvar c) me, 
              tymap ontmvar ontyvar (c+len) ty, walk (c+len+1) t)
    | TmFunApp(s, t, me) -> 
        TmFunApp(s, walk c t, List.map (walk c) me)
  in walk c t

and tymap ontmvar ontyvar c ty = 
  let rec walk c t = match t with
      TyVar(x, n) -> ontyvar c x n
    | TyPi(s, ty1, ty2) -> TyPi(s, walk c ty1, walk (c+1) ty2)
    | TySigma(s, ty1, ty2) -> TySigma(s, walk c ty1, walk (c+1) ty2)
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

(* tyShift的时候TmVar和TyVar都要管 *)
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

