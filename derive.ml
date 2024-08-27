type 't reg_exp =
| EmptySet
| EmptyStr
| Char of 't
| App of 't reg_exp * 't reg_exp
| Union of 't reg_exp * 't reg_exp
| Star of 't reg_exp

(** val match_eps : ascii reg_exp -> bool **)

let rec match_eps = function
| EmptySet -> false
| Char _ -> false
| App (re1, re2) -> match_eps re1 && match_eps re2
| Union (re1, re2) -> match_eps re1 || match_eps re2
| _ -> true

(** val derive : ascii -> ascii reg_exp -> ascii reg_exp **)

let rec derive (a : char) = function
| Char b -> if a = b then EmptyStr else EmptySet
| App (re1, re2) ->
  print_endline "hello";
  (match re1 with
   | EmptySet -> EmptySet
   | EmptyStr -> derive a re2
   | Char _ -> 
      if match_eps (derive a re1)
        then re2
        else EmptySet
   | Star _ ->
      print_endline "in star";
      let d1 = derive a re1 in
      print_endline "derived re1, let's see #####";
      (match d1 with
      | EmptySet -> print_endline "nope, shouldn't have gone star"; derive a re2
      | _ -> App (d1, re2))
   | _ ->
      let d1 = derive a re1 in App (d1, re2))
| Union (re, EmptySet) | Union (EmptySet, re) -> derive a re
| Union (re1, re2) ->
  let d1 = derive a re1 in
  let d2 = derive a re2 in
  Union (d1, d2)
| Star re' ->
  let d = derive a re' in
  (match d with
  | EmptySet -> EmptySet
  | _ -> if match_eps d
          then Star re'
          else App (d, (Star re')))
| _ -> EmptySet

(** val regex_match : char list -> ascii reg_exp -> bool **)

let rec regex_match (s : char list) re =
  match s with
  | [] -> match_eps re
  | a :: s' -> 
    (match derive a re with 
    | EmptySet -> false
    | d -> regex_match s' d);;

let match_string s = regex_match (s |> String.to_seq |> List.of_seq);;

#trace derive;;
#trace regex_match;;

let a, b, c, d = 'a', 'b', 'c', 'd';;
let m1 s = match_string s (App (Star (Char c), Char d));;
let m2 s = match_string s (Star (Union (Char c, App (Char a, Char d))))