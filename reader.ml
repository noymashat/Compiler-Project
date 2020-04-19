#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2) 
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;

let _newline = char '\n';;
let _hash = char '#';;
let _backslash = char '\\';;
let _double_quote = char '\"';;
let digit = range '0' '9';;
let _atoz = range 'a' 'z';;
let _AtoZ = pack (range 'A' 'Z') (fun (e) -> lowercase_ascii e);;
let _sym_list = "!$^*-_=+<>?/:";;
let _symbol = plus (disj digit (disj _atoz (disj _AtoZ (one_of _sym_list))));;
let _symbol_charsOnly = plus (disj _atoz (disj _AtoZ (one_of _sym_list)));;

let frac_part nat =
  let num = float_of_string (list_to_string nat) in
  if num = 0.0 then (0.0)
  else let exp = 10.0 ** (float_of_int ((-1) * String.length (list_to_string nat))) in
  (num  *. exp);;

let rad_char ch = 
  if (ch >= '0' &&  ch <= '9')
    then ((int_of_char ch) - 48)
  else (if (ch >= 'A' &&  ch <= 'Z')
    then ((int_of_char ch) - 55)
  else ((int_of_char ch) - 87));;

let radix_float n num charList = 
  let dot_len = (-1.0) *. float_of_int (List.length charList) in
  let un_dot = (List.map (fun i -> rad_char i) (num @ charList)) in
  let rfloat_calc = List.fold_left (fun a b -> n * a + b) 0 un_dot in
  (float_of_int rfloat_calc) *. ((float_of_int n) ** dot_len);;

let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let nt_line_comment = 
  let nt_semicolon = char ';' in
  let nt = diff nt_any _newline in
  let nt1 = pack (caten nt_semicolon (caten (star nt) _newline)) (fun _ -> ()) in
  let nt2 = pack (caten nt_semicolon (caten (star nt) nt_end_of_input)) (fun _ -> ()) in
  disj nt1 nt2;;

let rec nt_comment s = 
  disj nt_line_comment nt_sexpr_comment s

and nt_sexpr_comment s =
  pack (caten (word "#;") nt_sexpr) (fun _ -> ()) s

and nt_skippable s =
  (star (disj (pack nt_whitespace (fun _ -> ())) nt_comment)) s

and make_skipped nt = 
  make_paired nt_skippable nt_skippable nt

and nt_sexpr s = 
  let nts = disj_list [nt_boolean; nt_char; nt_string; nt_number; nt_symbol; nt_list; nt_quoted; nt_qq; nt_unquoted; nt_unquoted_spliced; nt_tagged_sexpr] in
  make_skipped nts s

and nt_boolean s =
  let _true = char_ci 'T' in
  let _false = char_ci 'F' in
  let nt = pack (caten _hash (disj _true _false)) (fun ((e1, e2)) -> Bool(e2 = 't' || e2 = 'T')) in
  nt s

and nt_char s = 
  let nt_char_prefix = pack (caten _hash _backslash) (fun ((e1, e2)) -> (e1, e2)) in
  let nt_visible_char = pack (range (Char.chr 33) (Char.chr 127)) (fun (e) -> Char(e)) in
  let nt_named_char = disj_list [(word_ci "newline"); (word_ci "nul"); (word_ci "page"); (word_ci "return"); (word_ci "tab");
                                  (word_ci "space")] in
  let nt_named_char = pack 
                        nt_named_char 
                        (fun ((e)) ->
                          let e = (list_to_string (List.map lowercase_ascii e)) in
                          match e with
                          | "newline" -> Char(char_of_int 10)
                          | "nul" -> Char(char_of_int 0)
                          | "page" -> Char(char_of_int 12)
                          | "return" -> Char(char_of_int 13)
                          | "tab" -> Char(char_of_int 9)
                          | "space" -> Char(char_of_int 32)
                          | _ -> raise X_no_match) in

  let nt = caten nt_char_prefix (disj nt_named_char nt_visible_char) in
  let nt = pack nt (fun (a, b) -> b) in
  nt s

and nt_string s =
  let nt_meta_char = caten _backslash (disj_list [(char 'n'); _backslash; (char 'r'); (char 't'); (char 'f'); _double_quote]) in
  let nt_meta_char = pack 
                      nt_meta_char
                      (fun (a,b) ->
                        match b with
                        | 'n' -> char_of_int 10
                        | '\\' -> char_of_int 92
                        | 'r' -> char_of_int 13
                        | 't' -> char_of_int 9
                        | 'f'-> char_of_int 12
                        | '\"' -> char_of_int 34
                        | _ -> raise X_no_match) in
  let nt_literal_char = diff nt_any (one_of "\\\"") in
  let nt = star (disj nt_literal_char nt_meta_char) in
  let nt = make_paired _double_quote _double_quote nt in
  let nt = pack nt (fun (e) -> String(list_to_string e)) in
  nt s

and nt_number s = 
  let plus_minus = maybe (disj (char '+') (char '-')) in
  let _integer = caten plus_minus (plus digit) in
  let nt_integer = pack 
                    _integer
                    (fun ((sign, num)) ->
                      match sign with
                      | Some('-') -> Number(Int((-1) * int_of_string (list_to_string num)))
                      | _ -> Number(Int(int_of_string (list_to_string num)))) in

  let _float = caten (caten _integer (char '.')) (plus digit) in
  let nt_float = pack 
                  _float 
                  (fun (((sign, num), dot), charList) -> 
                    let frac = frac_part charList in
                    let num = float_of_string (list_to_string num) in
                    match sign with
                    | Some('-') -> Number (Float ((-1.0) *. num -. frac))
                    | _ -> Number (Float(num +. frac))) in

  let nt_scientific = caten (disj nt_float nt_integer) (caten (char_ci 'e') nt_integer) in
  let nt_scientific = pack
                        nt_scientific
                        (fun (sexp, (_, exp)) -> 
                          (match exp with
                          | Number(Int(exp)) -> (match sexp with
                                                  | Number(Float(sexp)) -> Number (Float (sexp *. (10.0 ** (float_of_int exp))))
                                                  | Number(Int(sexp)) -> Number (Float ((float_of_int sexp) *. (10.0 ** (float_of_int exp))))
                                                  | _ -> sexp)
                          | _ -> exp)) in

  let _rad_digit = caten plus_minus (plus (disj_list [digit; _atoz; _AtoZ])) in
  let nt_int_radix = caten _hash (caten (nt_integer) (caten (char_ci 'r') _rad_digit)) in
  let nt_int_radix = pack
                      nt_int_radix 
                      (fun (_, (n, (_, (sign, num)))) -> 
                        (match n with
                        | Number(Int(n)) -> (match sign with
                                              | Some('-') ->  Number(Int((-1) * (List.fold_left 
                                                                                    (fun a b -> n * a + b) 0 (List.map (fun i -> rad_char i) num))))
                                              | _ -> Number(Int (List.fold_left       
                                                                    (fun a b -> n * a + b) 0 (List.map (fun i -> rad_char i) num))))
                        | _ -> n)) in

  let _frad_digit = caten _rad_digit (caten (char '.') (plus (disj_list [digit; _atoz; _AtoZ]))) in
  let _float_radix = caten _hash (caten (nt_integer) (caten (char_ci 'r') _frad_digit)) in
  let nt_float_radix = pack
                        _float_radix   
                        (fun (_, (n, (_, ((sign, num), (_, charList))))) -> 
                          (match n with
                          | Number(Int(n)) -> (match sign with
                                                | Some('-') ->  Number(Float((-1.0) *. (radix_float n num charList)))
                                                | _ -> Number(Float(radix_float n num charList)))
                          | _ -> n)) in

  let nt = not_followed_by (disj_list [nt_scientific; nt_float_radix; nt_int_radix; nt_float; nt_integer]) _symbol_charsOnly in                     
  nt s

and nt_symbol s =
  let nt_symbol_char = plus (disj digit (disj _atoz (disj _AtoZ (one_of _sym_list)))) in
  let nt_symbol_char = pack nt_symbol_char (fun (e)-> Symbol(list_to_string e)) in
  nt_symbol_char s

and nt_list s = 
  let nt_lpar = (char '(') in
  let nt_rpar = pack (char ')') (fun _ -> Nil) in 
  let _elist = caten nt_lpar (caten (nt_skippable) (char ')')) in
  let _elist = pack _elist (fun _ -> Nil) in
  let nt2 = make_paired (char '.') nt_rpar nt_sexpr in 
  let nt3 = plus nt_sexpr in
  let _list = caten nt_lpar (caten nt3 nt_rpar) in
  let _list = pack _list (fun (_, e) -> e) in
  let _dlist = caten nt_lpar (caten nt3 nt2) in
  let _dlist = pack _dlist (fun (_, e) -> e) in
  let nt = disj _list _dlist in
  let nt = pack 
            nt 
            (fun (sexprs, sexpr) -> 
                let list_expr = List.fold_right (fun a b -> Pair(a, b)) sexprs sexpr in
                if ((check_tag (acc_list list_expr))) then (list_expr)
                else (raise X_this_should_not_happen)) in        
  let nt = disj nt _elist in
  nt s

and nt_quoted s =
  let nt = caten (char '\'') nt_sexpr in
  let nt = pack nt (fun (_, b) -> Pair(Symbol "quote", Pair(b, Nil))) in
  nt s

and nt_qq s =
  let nt = caten (char '`') nt_sexpr in
  let nt = pack nt (fun (_, b) -> Pair(Symbol "quasiquote", Pair(b, Nil))) in
  nt s

and nt_unquoted s =
  let nt = caten (char ',') nt_sexpr in
  let nt = pack nt (fun (_, b) -> Pair(Symbol "unquote", Pair(b, Nil))) in
  nt s

and nt_unquoted_spliced s =
  let nt = caten (word ",@") nt_sexpr in
  let nt = pack nt (fun (_, b) -> Pair(Symbol "unquote-splicing", Pair(b, Nil))) in
  nt s

and nt_tagged_sexpr s = 
  let _symbol_char = plus (disj digit (disj _atoz (disj _AtoZ (one_of _sym_list)))) in
  let nt_tag = caten _hash (caten (char '{') (caten _symbol_char (char '}'))) in  
  let nt = caten nt_tag (maybe (caten (char '=') nt_sexpr)) in
  let nt = pack
            nt
            (fun ((_, (_, (tag, _))), opt) ->
                match opt with
                | Some(opt) ->  
                      let tagged_expr = TaggedSexpr(list_to_string tag, (snd opt)) in
                      if ((check_tag (acc_list tagged_expr))) then (tagged_expr)
                      else (raise X_this_should_not_happen)
                | _ -> TagRef(list_to_string tag)) in
  nt s

and check_tag lst =
  if ((List.length lst) <= 1) then (true)
  else (let tag = List.hd lst in
        let rest = List.tl lst in
        if (List.mem tag rest)
        then (false)
        else (check_tag rest))

and acc_list sexprs =
  match sexprs with
  | Pair (first, second) -> (acc_list first) @ (acc_list second)
  | TaggedSexpr(tag, rest) -> [tag] @ (acc_list rest)
  | _ -> [];;


module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct 

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr string = 
  let p = nt_sexpr (string_to_list string) in
  match (snd p) with
  | [] -> (fst p)
  | _ -> raise X_no_match;;

let read_sexprs string = 
  let p = (star nt_sexpr) (string_to_list string) in 
  (fst p);

 end;; (*struct Reader *)

