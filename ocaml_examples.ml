let rec le_vec x li = match li with
  [] -> []
| (h::xs) -> if h <= x then h :: le_vec x (xs)
  else le_vec x (xs)

let rec g_vec x li = match li with
  [] -> []
| (h::xs) -> if h > x then h :: g_vec x (xs)
  else g_vec x (xs)

let rec qs li = match li with
  [] -> []
| (x::xs) -> qs (le_vec x xs) @ [x] @ qs (g_vec x xs)