#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  (* | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2 *)
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  (* | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2) *)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct


let rec search_box expr =
  match expr with
  | Const'(x) -> Const'(x)
  | Var'(x) -> Var'(x)
  | If'(test, dit, dif) -> If'((search_box test), (search_box dit), (search_box dif))
  | Seq'(x) -> Seq'(List.map search_box x)
  | Set'(name, value) -> Set'((search_box name), (search_box value))
  | Def'(name, value) -> Def'((search_box name), (search_box value))
  | Or'(x) -> Or'(List.map search_box x)
  | LambdaSimple'(params, body) -> let var_lst = (vars_to_box params body) in
                                   LambdaSimple'(params, (search_box (add_set_box (List.fold_left make_box body var_lst) params var_lst)))
  | LambdaOpt'(mand, opt, body) -> let params = (mand @ [opt]) in
                                   let var_lst = (vars_to_box params body) in 
                                   LambdaOpt'(mand, opt, (search_box (add_set_box (List.fold_left make_box body var_lst) params var_lst)))
  | Applic'(op, rands) -> Applic'((search_box op), (List.map search_box rands))
  | ApplicTP'(op, rands) -> ApplicTP'((search_box op), (List.map search_box rands))
  | BoxGet'(x) -> BoxGet'(x)
  | BoxSet'(name, value) -> BoxSet'(name, (search_box value))
  | Box'(x) -> Box'(x)
  
and vars_to_box params body =
  match params with
  | [] -> []
  | hd :: [] -> if(check_box hd body) then([hd])
                else([]) 
  | hd :: tl -> if(check_box hd body) then([hd] @ (vars_to_box tl body))
                else(vars_to_box tl body)
                
and check_box var body =
  let read_ref_count = {contents = -1} in
  let write_ref_count = {contents = -1} in
  let read_lst = check_box_read var read_ref_count (-1) body in
  let write_lst = check_box_write var write_ref_count (-1) body in 
  let cart_lst = cartesian_product read_lst write_lst in
  let bool_cart_lst = List.map (fun p -> if(fst p != snd p) then(true) else(false)) cart_lst in
  let res = List.fold_left (fun a b -> a || b) false bool_cart_lst in
  res

and make_box expr var =
  make_box_rec var (-1) expr

and make_box_rec var nest_count expr =
  match expr with
  | Const'(x) -> Const'(x)
  | Var'(x) -> 
    (match x with
    | VarBound (name, major, _) when(major = nest_count && name = var) -> BoxGet'(x)
    | VarParam (name, _) when(nest_count < 0 && name = var) -> BoxGet'(x)
    | _ -> Var'(x))
  | If'(test, dit, dif) -> If'((make_box_rec var nest_count test), 
                                (make_box_rec var nest_count dit),
                                (make_box_rec var nest_count dif))
  | Seq'(x) -> Seq'(List.map (make_box_rec var nest_count) x)
  | Set'(n, value) -> 
    (match n with
      | Var'(VarBound (name, major, minor)) when (major = nest_count && name = var) ->
          (BoxSet'(VarBound (name, major, minor), (make_box_rec var nest_count value)))
      | Var'(VarParam (name, minor)) when (nest_count < 0 && name = var) ->
          (BoxSet'(VarParam (name, minor), (make_box_rec var nest_count value)))
      | _ -> (Set'(n, (make_box_rec var nest_count value))))

  | Def'(name, value) -> Def'((name), (make_box_rec var nest_count value))
  | Or'(x) -> Or'(List.map (make_box_rec var nest_count) x)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (make_box_rec var (nest_count+1) body))
  | LambdaOpt'(mand, opt, body) -> LambdaOpt'(mand, opt, (make_box_rec var (nest_count+1) body))
  | Applic'(op, rands) -> Applic'((make_box_rec var nest_count op), (List.map (make_box_rec var nest_count) rands))
  | ApplicTP'(op, rands) -> ApplicTP'((make_box_rec var nest_count op), (List.map (make_box_rec var nest_count) rands))
  | BoxGet'(x) -> BoxGet'(x)
  | BoxSet'(name, value) -> BoxSet'(name, (make_box_rec var nest_count value))
  | Box'(x) -> Box'(x)

and add_set_box expr params var_lst = 
  match var_lst with
  | [] -> expr
  | _ -> let set_lst = List.map 
                        (fun v -> Set' (Var' (VarParam (v, (find_index 0 params v))), Box' (VarParam (v, (find_index 0 params v))))) 
                        var_lst in
          Seq'(List.append set_lst [expr])

and find_index index params var =
  match params with
  | [] -> raise X_this_should_not_happen
  | hd :: tl when (hd = var) -> index
  | hd :: tl -> find_index (index+1) tl var
                  
and check_box_read var ref_count nest_count expr =  
  match expr with
  | Const'(x) -> []
  | BoxGet'(x) -> []
  | Box'(x) -> []
  | Var'(x) -> 
    (match x with
    | VarBound (name, major, _) when(major = nest_count && name = var) -> [!ref_count]
    | VarParam (name, _) when(nest_count < 0 && name = var) -> [0]
    | _ -> [])
  | If'(test, dit, dif) -> (check_box_read var ref_count nest_count test) 
                            @ (check_box_read var ref_count nest_count dit)
                            @ (check_box_read var ref_count nest_count dif)
  | Seq'(x) -> List.fold_left List.append [] (List.map (check_box_read var ref_count nest_count) x)
  | Set'(name, value) -> check_box_read var ref_count nest_count value
  | Def'(name, value) -> check_box_read var ref_count nest_count value
  | Or'(x) -> List.fold_left List.append [] (List.map (check_box_read var ref_count nest_count) x)
  | LambdaSimple'(params, body) -> nested_lambda_read var ref_count nest_count body
  | LambdaOpt'(mand, opt, body) -> nested_lambda_read var ref_count nest_count body
  | Applic'(op, rands) -> (check_box_read var ref_count nest_count op)
                          @ List.fold_left List.append [] (List.map (check_box_read var ref_count nest_count) rands)
  | ApplicTP'(op, rands) -> (check_box_read var ref_count nest_count op)
                            @ List.fold_left List.append [] (List.map (check_box_read var ref_count nest_count) rands)
  | BoxSet'(name, value) -> (check_box_read var ref_count nest_count value)

and nested_lambda_read var ref_count nest_count body =
  let inc_count = inc_ref_count ref_count in
  if ((check_box_read var (inc_ref_count inc_count) (nest_count + 1) body) = [])
    then ([])
  else ([!ref_count])

and check_box_write var ref_count nest_count expr =  
  match expr with
  | Const'(x) -> []
  | BoxGet'(x) -> []
  | Box'(x) -> []
  | Var'(x) -> []
  | If'(test, dit, dif) -> (check_box_write var ref_count nest_count test) 
                            @ (check_box_write var ref_count nest_count dit)
                            @ (check_box_write var ref_count nest_count dif)
  | Seq'(x) -> List.fold_left List.append [] (List.map (check_box_write var ref_count nest_count) x)
  | Set'(n, value) -> 
    (match n with
    | Var'(VarBound (name, major, minor)) when (major = nest_count && name = var) ->[!ref_count]
    | Var'(VarParam (name, minor)) when (nest_count < 0 && name = var) -> [0]
    | _ -> [])
    @ check_box_write var ref_count nest_count value
  | Def'(name, value) -> check_box_write var ref_count nest_count value
  | Or'(x) -> List.fold_left List.append [] (List.map (check_box_write var ref_count nest_count) x)
  | LambdaSimple'(params, body) -> nested_lambda_write var ref_count nest_count body
  | LambdaOpt'(mand, opt, body) -> nested_lambda_write var ref_count nest_count body
  | Applic'(op, rands) -> (check_box_write var ref_count nest_count op)
                          @ List.fold_left List.append [] (List.map (check_box_write var ref_count nest_count) rands)
  | ApplicTP'(op, rands) -> (check_box_write var ref_count nest_count op)
                            @ List.fold_left List.append [] (List.map (check_box_write var ref_count nest_count) rands)
  
  | BoxSet'(name, value) -> check_box_write var ref_count nest_count value

and nested_lambda_write var ref_count nest_count body =
  let inc_count = inc_ref_count ref_count in
  if ((check_box_write var (inc_ref_count inc_count) (nest_count + 1) body) = [])
    then ([])
  else ([!ref_count])

and inc_ref_count ref_count =
  let count = { contents = 0 } in
  if((ref_count := !ref_count + 1) = (count := !count + 1))
    then(ref_count)
  else(ref_count)


and cartesian_product r_lst w_lst = 
  List.concat (List.map (fun r -> List.map (fun w -> (r,w)) w_lst) r_lst)
  
and traverse_ast e =
  match e with
  | Const'(x) -> Const'(x)
  | Var'(x) -> Var'(x)
  | If'(test, dit, dif) -> If'((traverse_ast test), (traverse_ast dit), (traverse_ast dif))
  | Seq'(x) -> Seq'(List.map traverse_ast x)
  | Set'(name, value) -> Set'((traverse_ast name), (traverse_ast value))
  | Def'(name, value) -> Def'((traverse_ast name), (traverse_ast value))
  | Or'(x) -> Or'(List.map traverse_ast x)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (fix_lambda false body))
  | LambdaOpt'(mand, opt, body) -> LambdaOpt'(mand, opt, (fix_lambda false body))
  | Applic'(op, rands) -> Applic'((traverse_ast op), (List.map traverse_ast rands))
  | _ -> e

and fix_lambda in_tp e =
  match e with
  | Seq'(x) -> Seq'(List.append (List.map (tail_annotate false) (rmv_last x)) [tail_annotate true (ret_last x)])
  | _ -> tail_annotate true e

and tail_annotate in_tp e =
  match e with
  | Const'(x) -> Const'(x)
  | Var'(x) -> Var'(x)
  | If'(test, dit, dif) -> If'(test, (tail_annotate in_tp dit), (tail_annotate in_tp dif))
  | Seq'(x) -> Seq'(List.append (List.map (tail_annotate false) (rmv_last x)) [tail_annotate in_tp (ret_last x)])
  | Or'(x) -> Or'(List.append (List.map (tail_annotate false) (rmv_last x)) [tail_annotate in_tp (ret_last x)])                    
  | Set'(name, value) -> Set'(name, (tail_annotate false value))
  | Def'(name, value) -> Def'(name, (tail_annotate in_tp value))
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (fix_lambda false body))
  | LambdaOpt'(mand, opt, body) -> LambdaOpt'(mand, opt, (fix_lambda false body))
  | Applic'(op, rands) -> if(in_tp) then(ApplicTP'((tail_annotate false op), (List.map (tail_annotate false) rands))) 
                          else(Applic'((tail_annotate false op), (List.map (tail_annotate false) rands)))
  | _ -> e

and ret_last lst =
  let last = List.rev lst in
  let last = List.hd last in 
  last

and rmv_last lst =
  let rest = List.rev lst in
  let rest = List.rev (List.tl rest) in
  rest

and to_expr' e =
  match e with
  | Const(x) -> Const'(x)
  | Var(x) -> Var'(VarFree(x))
  | If(test, dit, dif) -> If'((to_expr' test), (to_expr' dit), (to_expr' dif))
  | Seq(x) -> Seq'(List.map to_expr' x)
  | Set(name, value) -> Set'((to_expr' name), (to_expr' value))
  | Def(name, value) -> Def'((to_expr' name), (to_expr' value))
  | Or(x) -> Or'(List.map to_expr' x)
  | LambdaSimple(params, body) -> LambdaSimple'(params, (lambda_lex_env params [] body))
  | LambdaOpt(mand, opt, body) -> LambdaOpt'(mand, opt, (lambda_lex_env (mand @ [opt]) [] body))
  | Applic(op, rands) -> Applic'((to_expr' op), (List.map to_expr' rands))

and lambda_lex_env params env body =
  match body with
  | Const(x) -> Const'(x)
  | Var(x) -> Var'(check_vars params env x 0)
  | If(test, dit, dif) -> If'((lambda_lex_env params env test), (lambda_lex_env params env dit), (lambda_lex_env params env dif))
  | Seq(x) -> Seq'(List.map (lambda_lex_env params env) x)
  | Set(name, value) -> Set'((lambda_lex_env params env name), (lambda_lex_env params env value))                      
  | Def(name, value) -> Def'((lambda_lex_env params env name), (lambda_lex_env params env value)) 
  | Or(x) -> Or'(List.map (lambda_lex_env params env) x)
  | LambdaSimple(args, body) -> LambdaSimple'(args, (lambda_lex_env args (params :: env) body))
  | LambdaOpt(mand, opt, body) -> LambdaOpt'(mand, opt, (lambda_lex_env (mand @ [opt]) (params :: env) body))
  | Applic(op, rands) -> Applic'((lambda_lex_env params env op), (List.map (lambda_lex_env params env) rands))


and check_vars params env var minor =
  match params with
  | [] -> check_bound_or_free params env var 0 0
  | hd :: tl -> if(var = hd) then(VarParam(var, minor))
                else(check_vars tl env var (minor+1))

and check_bound_or_free params env var major minor =
  match env with
  | [] -> VarFree(var)
  | hd :: tl -> if(List.mem var hd) then(find_minor hd var major 0)
                else(check_bound_or_free params tl var (major+1) minor) 

and find_minor env var major minor =
  match env with
  | hd :: [] -> VarBound(var, major, minor) 
  | hd :: tl -> if(var = hd) then(VarBound(var, major, minor))
                else(find_minor tl var major (minor+1))
  | _ -> raise X_this_should_not_happen;;

let annotate_lexical_addresses e = to_expr' e;;

let annotate_tail_calls e = traverse_ast e;;

let box_set e = search_box e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr)
       )
       ;;

end;; 
(* struct Semantics *)
