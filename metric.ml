open Syntax
open Print

(* Metric Context Management *)

let emptymctx = []

let rec getmetric mctx str = 
  match mctx with
    [] -> None
  | (s,t)::xs ->
      if s=str then Some(t)
      else getmetric xs str

let addmetric mctx x me = (x,me)::mctx

let rec shiftMetricContext mctx c = match mctx with
    [] -> []
  | (me::xs) -> let (name, li) = me in
      (name, List.map (fun t -> termShift c t) li) :: shiftMetricContext xs c

(* utilities for typeof of TmFun and TmFunApp *)

let generatePiType ty c f = 
  let rec go ty d = match d with
    0 -> ty
  | _ -> TyPi("metric_" ^ f ^ "_" ^ string_of_int (c-d+1), TyNat, go ty (d-1))
  in go ty c

let generateLambdaTerm t c f = 
  let rec go t d = match d with
    0 -> t
  | _ -> TmAbs("metric_" ^ f ^ "_" ^ string_of_int (c-d+1), TyNat, go t (d-1))
  in go t c

let addbindingOfMetric ctx c f = 
  let rec go ctx d = match d with
    0 -> ctx
  | _ -> addbinding (go ctx (d-1)) ("metric_"^f^"_"^string_of_int d) (VarBind(TyNat))
  in go ctx c

let generateMetric ctxlen c =
  let rec go d = match d with
    0 -> []
  | _ -> TmVar(d-1, ctxlen) :: go (d-1)
  in go c

let substMetric me ty = 
  let rec go li curty = match li with
    [] -> curty
  | x::xs -> 
    let curty' = (match curty with 
        TyPi(_, TyNat, tyT) -> tySubstTop x tyT
      | _ -> error "[typeof error: TmFunApp] substMetric error") 
    in go xs curty'
  in go me ty

(* translate TmFun and TmFunApp into derived forms for eval *)

let derivedformTmFun s tyMe ty t =
  let c = List.length tyMe in
  let tyF = generatePiType ty c s in
  let tF = generateLambdaTerm t c s in
  TmFix(TmAbs(s, tyF, tF))

let derivedformTmFunApp s t me = 
  let rec go li = match li with
    [] -> t
  | x::xs -> TmApp(go xs, x)
  in go (List.rev me)

(* comparison of metrics  *)

let metricless_normal ctx mctx me me0 =
  if List.length me != List.length me0 
    then error "[metricless error] metric length not equal"
  else 
  let single_metricless (m1, m2) = 
    let rec calc me cnt = match me with
        TmVar(x,_) -> (x, cnt)
      | TmSucc(t) -> calc t (cnt+1)
      | TmPred(t) -> calc t (cnt-1)
      | _ -> error "[metricless error] metric not Nat"
    in 
    let (x1, c1) = calc m1 0 in
    let (x2, c2) = calc m2 0 in
    if x1 != x2 then -1
    else if c1 > c2 then -1
    else if c1 == c2 then 0
    else 1
  in let res = List.map single_metricless (List.combine me me0) in
  (* in let () = pr (string_of_bool (List.hd res)); pr" ";pr (string_of_bool (List.hd (List.tl res))); pr"\n"  *)
  let qwq x y = 
    if (x == -1 || y == -1) then -1 
    else if(x == 1 || y == 1) then 1
    else 0
  in let ans = List.fold_left qwq 0 res in
  if ans == 1 then true else false

let metricless_sum ctx mctx me me0 =
  if List.length me != List.length me0 
    then error "[metricless error] metric length not equal"
  else 
  let single_metricless (m1, m2) = 
    let rec calc me cnt = match me with
        TmVar(x,_) -> (x, cnt)
      | TmSucc(t) -> calc t (cnt+1)
      | TmPred(t) -> calc t (cnt-1)
      | _ -> (debugTerm ctx me; pr"\n"; error "[metricless error] metric not Nat")
    in 
    let (x1, c1) = calc m1 0 in
    let (x2, c2) = calc m2 0 in
    if x1 != x2 then error "[metricless error] metric not comparable"
    else c1 - c2
  in let res = List.map single_metricless (List.combine me me0) 
  (* in let () = pr (string_of_bool (List.hd res)); pr" ";pr (string_of_bool (List.hd (List.tl res))); pr"\n"  *)
  in List.fold_left (+) 0 res < 0

let metricless = metricless_sum