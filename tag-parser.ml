#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  (* | Var(v1), Var(v2) -> String.equal v1 v2 *)
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  (* | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2) *)
  (* | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2) *)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

let rec tag_parser sexpr =
  match sexpr with
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | Number(x) -> Const(Sexpr(Number(x)))
  | String(x) -> Const(Sexpr(String(x)))
  | Symbol(x) -> if (List.mem x reserved_word_list) then (raise X_syntax_error) else (Var(x))
  | TaggedSexpr(tag, value) -> Const(Sexpr(TaggedSexpr(tag, (check_taggedSexpr value))))
  | Pair(Symbol("quote"), Pair(x, Nil)) -> Const(Sexpr(x))
  | Pair(Symbol("quasiquote"), Pair(x, Nil)) -> (tag_parser (macro_qq x))
  | Pair(Symbol("if"), Pair(test, Pair(dit, Pair(dif, Nil)))) -> If((tag_parser test), (tag_parser dit), (tag_parser dif)) 
  | Pair(Symbol("if"), Pair(test, Pair(dit, Nil))) -> If((tag_parser test), (tag_parser dit), Const(Void))
  | Pair(Symbol("cond"), conds) -> (tag_parser (macro_cond conds))
  | Pair(Symbol("lambda"), Pair(args, body)) -> (check_lambda args body)
  | Pair(Symbol("let"), Pair(Nil, body)) -> (tag_parser (macro_empty_let body))
  | Pair(Symbol("let"), Pair(ribs, body)) -> (tag_parser (macro_let_makeApplic (macro_let_vars ribs) (macro_let_values ribs) body))
  | Pair(Symbol("let*"), Pair(Nil, body)) -> (tag_parser (macro_empty_let body))
  | Pair(Symbol("let*"), Pair(ribs, body)) -> (tag_parser (macro_let_star ribs body))
  | Pair(Symbol("letrec"), Pair(Nil, body)) -> (tag_parser (macro_empty_let body))
  | Pair(Symbol("letrec"), Pair(ribs, body)) -> (tag_parser (macro_letrec ribs body))
  | Pair(Symbol("or"), x) -> (check_or x)
  | Pair(Symbol("and"), x) -> (tag_parser (macro_and x))
  | Pair(Symbol("define"), Pair(Pair(name, args), expr)) -> (tag_parser (macro_defineMIT name args expr))
  | Pair(Symbol("define"), Pair(name, Pair(value, Nil))) -> (let _name = tag_parser name in
                                                            (match _name with
                                                            | Var(n) -> Def(_name, tag_parser value)
                                                            | _ -> raise X_syntax_error))

  | Pair(Symbol("set!"), Pair(name, Pair(value, Nil))) -> (let _name = tag_parser name in
                                                          (match _name with
                                                          | Var(n) -> Set(_name, tag_parser value)
                                                          | _ -> raise X_syntax_error))
  | Pair(Symbol("begin"), seq) -> (check_ex_seq seq)
  | Pair(op, rands) -> Applic(tag_parser op, (sexprs_to_exprs rands))
  | Nil -> Const(Void)
  | _ -> raise X_not_yet_implemented

and check_taggedSexpr value =
  match value with
  | Pair(Symbol("quote"), Pair(x, Nil)) -> x
  | _ -> value

and check_lambda args body =
  let argList = args_to_list args in
    if (not (check_dups argList))
      then (raise X_syntax_error)
    else (if (check_if_proper args)
            then (LambdaSimple(argList, (check_im_seq body)))
          else (let opt = (List.hd (List.rev argList)) in
                if ((List.length argList) < 2)
                  then (LambdaOpt([], opt, check_im_seq body))
                else (let mandatory = (List.rev (List.tl (List.rev argList))) in
                      LambdaOpt(mandatory, opt, check_im_seq body))))

and args_to_list args =
  match args with
  | Nil -> []
  | Pair(Symbol(x), rest) -> [x] @ (args_to_list rest);
  | Symbol(x) -> [x]
  | _ -> raise X_syntax_error

and check_dups arglist =
  if ((List.length arglist) <= 1) then (true)
  else (let curr = List.hd arglist in
        let rest = List.tl arglist in
        if (List.mem curr rest)
        then (false)
        else (check_dups rest))

and check_if_proper arglist =
  match arglist with
    | Nil -> true
    | Pair(a, b) -> check_if_proper b
    | _ -> false

and sexprs_to_exprs rands =
  match rands with
  | Nil -> []
  | Pair(Symbol("quote"), Pair(x, Nil)) -> [tag_parser rands]
  | Pair(first, rest) -> [tag_parser first] @ (sexprs_to_exprs rest)
  | _ -> raise X_syntax_error

and check_or rands =
  match rands with
  | Nil -> Const(Sexpr(Bool(false)))
  | Pair(Symbol("quote"), Pair(x, Nil)) -> tag_parser rands
  | Pair(first, Nil) -> tag_parser first
  | Pair(first, second) -> Or(sexprs_to_exprs rands)
  | _ -> raise X_this_should_not_happen

and check_ex_seq seq = 
  if (check_if_proper seq)
    then (match seq with
          | Nil -> Const(Void)
          | Pair(a, Nil)-> tag_parser a
          | _ -> Seq(sexprs_to_exprs seq))
  else (raise X_syntax_error)

and check_im_seq seq = 
  if (check_if_proper seq)
    then (match seq with
          | Nil -> raise X_syntax_error
          | Pair(a, Nil)-> tag_parser a
          | Pair(Symbol("if"), b) ->  Seq([tag_parser seq])
          | _ -> Seq(sexprs_to_exprs seq))
  else (raise X_syntax_error)

and macro_and sexpr = 
  match sexpr with
  | Nil -> (Bool true)
  | Pair(x, rest) -> (match rest with
                      | Nil -> x
                      | _ -> Pair(Symbol("if"), Pair(x, Pair(Pair(Symbol("and"), rest), Pair(Bool(false), Nil)))))
  | _ -> raise X_syntax_error

and macro_empty_let body =
  Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)

and macro_let_vars ribs = 
  match ribs with
  | Pair(Pair(var, Pair(value, Nil)), cont) -> 
        (match cont with
        | Nil -> Pair(var, Nil)
        | Pair(Pair(first, second), rest) -> Pair(var, (macro_let_vars cont))
        | _ -> cont)
                                              
  | _ -> raise X_syntax_error

and macro_let_values ribs = 
  match ribs with
  | Pair(Pair(var, Pair(value, Nil)), cont) -> 
        (match cont with
        | Nil -> Pair(value, Nil)
        | Pair(Pair(first, second), _) -> Pair(value, (macro_let_values cont))
        | _ -> cont)
  | _ -> raise X_syntax_error

and macro_let_makeApplic vars values body = 
  Pair(Pair(Symbol("lambda"), Pair(vars, body)), values)
  
and macro_let_star ribs body = 
  match ribs with
  | Pair(Pair(var, Pair(value, Nil)), cont) -> 
        (let rib = Pair(var, Pair(value, Nil)) in
        match cont with
        | Nil -> Pair(Symbol("let"), Pair(Pair(rib, Nil), body))
        | Pair(first, rest) -> Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Pair(Symbol("let*"), Pair(Pair(first, rest), body)), Nil)))
        | _ -> cont)
  | _ -> raise X_syntax_error

and macro_letrec_initbody ribs =
  match ribs with
  | Nil -> Nil
  | Pair(Pair(var, Pair(value, Nil)), rest) ->
    (match rest with
      | Nil -> Pair(Symbol("set!"), Pair(var, Pair(value, Nil)))
      | Pair(Pair(a, Pair(b, Nil)), _) -> Pair(Pair(Symbol("set!"), Pair(var, Pair(value, Nil))), (macro_letrec_initbody rest))
      | _ -> rest)
  | _ -> raise X_syntax_error

and macro_letrec_initval ribs = 
  match ribs with
  | Nil -> Nil
  | Pair(Pair(var, Pair(value, Nil)), rest) ->
      (match rest with
      | Nil -> Pair(Pair(var, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), Nil)
      | Pair(Pair(a, Pair(b, Nil)), _) -> Pair(Pair(var, Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), (macro_letrec_initval rest))
      | _ -> rest)
  | _ -> raise X_syntax_error

and macro_letrec ribs body = 
  let new_body = Pair(Pair(Symbol("begin"), Pair((macro_letrec_initbody ribs), body)), Nil) in
  Pair(Symbol("let"), Pair((macro_letrec_initval ribs), new_body))

and macro_qq x =
  match x with
  | Pair(Symbol("unquote"), Pair(sexpr, Nil)) -> sexpr
  | Pair(Symbol("unquote-splicing"), Pair(sexpr, Nil)) -> raise X_syntax_error
  | Symbol(y) -> Pair(Symbol("quote"), Pair(Symbol(y), Nil))
  | Nil -> Pair(Symbol("quote"), Pair(Nil, Nil))
  | Pair(Pair(Symbol("unquote-splicing"), Pair(a, Nil)), b) -> Pair(Symbol("append"), Pair(a, Pair (macro_qq b, Nil)))                
  | Pair(a, Pair(Symbol("unquote-splicing"), Pair(b, Nil))) -> Pair(Symbol("cons"), Pair(macro_qq a, Pair (b, Nil))) 
  | Pair(a, b) -> Pair(Symbol("cons"), Pair(macro_qq a, Pair (macro_qq b, Nil)))
  | _ -> x

and macro_cond conds =
  match conds with  
  | Pair(Pair(test, Pair(Symbol("=>"), dit)), ribs) ->  
      (match ribs with
      | Nil -> (Pair(Symbol("let"), 
                Pair(Pair(Pair(Symbol("value"), Pair(test, Nil)), 
                          Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, dit)), Nil)), Nil)), 
                Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), Nil))), Nil))))

      | _ -> (Pair(Symbol("let"), 
                Pair(Pair(Pair(Symbol("value"), Pair(test, Nil)), 
                          Pair(Pair(Symbol("f"), Pair(Pair(Symbol("lambda"), Pair(Nil, dit)), Nil)), 
                                Pair(Pair(Symbol("rest"), Pair(Pair(Symbol("lambda"), Pair(Nil, Pair((macro_cond ribs), Nil))), Nil)), Nil))), 
                Pair(Pair(Symbol("if"), Pair(Symbol("value"), Pair(Pair(Pair(Symbol("f"), Nil), Pair(Symbol("value"), Nil)), 
                      Pair(Pair(Symbol("rest"), Nil), Nil)))), Nil)))))

  | Pair(Pair(Symbol("else"), dif), rest) -> Pair(Symbol("begin"), dif)
                                                
  | Pair(Pair(test, dit), ribs)-> 
      (match ribs with
      | Nil -> Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"), dit), Nil)))
      | _ -> Pair(Symbol("if"), Pair(test, Pair(Pair(Symbol("begin"), dit), Pair((macro_cond ribs), Nil)))))
  | _ -> raise X_this_should_not_happen

and macro_defineMIT name args expr =
  Pair(Symbol("define"), Pair(name, Pair(Pair(Symbol("lambda"), Pair(args, expr)), Nil)));;


let tag_parse_expression sexpr = tag_parser sexpr;;

let tag_parse_expressions sexpr = List.map tag_parser sexpr;;    

end;; 
(* struct Tag_Parser *) 