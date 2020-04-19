#use "semantic-analyser.ml";;

(* CONST_TBL START REGION*)

let rec change_tag_name offset expr =
  match expr with
  (* | Var'(x) -> Var'(x) *)
  | If'(test, dit, dif) -> If'((change_tag_name offset test), (change_tag_name offset dit), (change_tag_name offset dif))
  | Seq'(x) -> Seq'(List.map (change_tag_name offset) x)
  | Set'(name, value) -> Set'(name, (change_tag_name offset value))
  | Def'(name, value) -> Def'(name, (change_tag_name offset value))
  | Or'(x) -> Or'(List.map (change_tag_name offset) x)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (change_tag_name offset body))
  | LambdaOpt'(mand, opt, body) -> LambdaOpt'(mand, opt, (change_tag_name offset body))
  | Applic'(op, rands) -> Applic'((change_tag_name offset op), (List.map (change_tag_name offset ) rands))
  | ApplicTP'(op, rands) -> ApplicTP'((change_tag_name offset op), (List.map (change_tag_name offset) rands))
  | BoxSet'(name, value) -> BoxSet'(name, (change_tag_name offset value))
  | Const'(x) -> 
    (match x with
    | Sexpr(TaggedSexpr(name, value)) -> 
        let r = inc_ref_count offset in
        Const'(Sexpr(TaggedSexpr((string_of_int !r), value)))
    | Sexpr(TagRef(name)) -> Const'(Sexpr(TagRef(string_of_int !offset)))
    | Sexpr(Pair(f, s)) -> 
        let ref_offset = { contents = (-1) } in
        Const'(Sexpr(change_tag_name_pair false ref_offset offset f s))
    | _ -> Const'(x))
  | _ -> expr

(* if ref_flag = true: the current TagRef is already bound to TagDef *)
and change_tag_name_pair ref_flag ref_offset offset f s =
  match f with
  | TaggedSexpr(name, value) -> 
      let r = inc_ref_count offset in
      Pair(TaggedSexpr(string_of_int !offset, value), (search_tag_ref_pair name ref_offset r s))
  | TagRef(name) when(ref_flag=true) -> 
      Pair(TagRef(string_of_int !offset), (search_tag_ref_pair name ref_offset offset s))
  | TagRef(name) -> 
      let has_def = (check_if_has_def_pair name s) in
      (match has_def with
       | true -> 
          let new_name = (calc_tag_def_offset_pair name ref_offset s) in
          Pair(TagRef(string_of_int !new_name), (search_tag_def_pair ref_flag name ref_offset offset s))
       | _ -> raise X_this_should_not_happen)
  | Pair(fst, scnd) -> Pair((change_tag_name_pair ref_flag ref_offset offset fst scnd), 
                            (change_tag_name_pair_helper ref_flag ref_offset offset s))
  | _ -> Pair(f, (change_tag_name_pair_helper ref_flag ref_offset offset s))

(* continue searching tagdef/ref in this nested pair (proper list) Sexpr 
   if ref_flag = true: the current TagRef is already bound to TagDef *)
and change_tag_name_pair_helper ref_flag ref_offset offset sec = 
  match sec with
  | Pair(f, s) -> (change_tag_name_pair ref_flag ref_offset offset f s)
  | _ -> sec

(* change all(!) occurrences of TagRef(n) in this nested pair (proper list) Sexpr. 
   always continue searching other tagdef/ref in this Sexpr. 
   got here only when had TagDef and so (ref_flag = true) *)
and search_tag_ref_pair n ref_offset offset sec =
  match sec with
  | Pair(f, s) -> 
      (match f with
        | TagRef(name) when(name = n) -> Pair(TagRef(string_of_int !offset), (change_tag_name_pair_helper true ref_offset offset s))
        | _ -> (change_tag_name_pair true ref_offset offset f s))
  | _ -> sec

(* when we got TagRef with (ref_flag = false) - first step: check it has a TagDef in this nested pair Sexpr 
   if not found - raise X_this_should_not_happen *)  
and check_if_has_def_pair name sec =
  match sec with
  | Pair(f, s) ->
      (match f with
       | TaggedSexpr(n, _) when(n = name) -> true
       | _ -> (check_if_has_def_pair name s))
  | _ -> false

(* when we got TagRef with (ref_flag = false) - second step: calc it's TagDef's offset before continuing *)  
and calc_tag_def_offset_pair n ref_offset sec =
  match sec with
  | Pair(f, s) ->
      (match f with
       | TaggedSexpr(name, value) when(name = n) -> 
          let r = inc_ref_count ref_offset in
          r
       | TaggedSexpr(name, value) -> (calc_tag_def_offset_pair n ref_offset s)
       | _ -> (calc_tag_def_offset_pair n ref_offset s))
  | _ -> raise X_this_should_not_happen

(* search an occurrence of TaggedSexpr(n, _) in this nested pair Sexpr.
   if exist - continue searching other tagdef/ref in this Sexpr with (ref_flag=true) for this TagRef 
              and only after changing all TagRef(n) to TagRef(offset) *)
and search_tag_def_pair ref_flag n ref_offset offset sec =
  match sec with
  | Pair(f, s) ->
      (match f with
      | TaggedSexpr(name, value) when(name = n) -> 
          let r = inc_ref_count offset in
          Pair(TaggedSexpr(string_of_int !r, value), (change_tag_name_pair_helper true ref_offset offset (fix_tag_ref_pair n offset s)))
      | _ -> (change_tag_name_pair false ref_offset offset f s))
  | _ -> sec


(* change all(!) occurrences of TagRef(n) to TagRef(offset).
   got here only after changing TagDef(n, _) to TagDef(offset, _) *)  
and fix_tag_ref_pair name offset sec =
  match sec with
  | Pair(f, s) -> 
        (match f with
         | TagRef(n) when(n = name) -> Pair(TagRef(string_of_int !offset), (fix_tag_ref_pair name offset s))
         | _ -> Pair(f, (fix_tag_ref_pair name offset s)))
  | _ -> sec


and make_tag_lst expr =
  match expr with
  | Const'(x) -> 
    (match x with
    | Sexpr(TaggedSexpr(name, value)) -> [(name, value)] @ (make_tag_lst_helper value)
    | Sexpr(Pair(f, s)) -> (make_tag_lst_helper f) @ (make_tag_lst_helper s)
    | _ -> [])
  | If'(test, dit, dif) -> (make_tag_lst test) 
                            @ (make_tag_lst dit)
                            @ (make_tag_lst dif)
  | Seq'(x) -> List.fold_left List.append [] (List.map (make_tag_lst) x)
  | Set'(name, value) -> make_tag_lst value
  | Def'(name, value) -> make_tag_lst value
  | Or'(x) -> List.fold_left List.append [] (List.map (make_tag_lst) x)
  | LambdaSimple'(params, body) -> make_tag_lst body
  | LambdaOpt'(mand, opt, body) -> make_tag_lst body
  | Applic'(op, rands) -> (make_tag_lst op)
                          @ (List.fold_left List.append [] (List.map (make_tag_lst) rands))
  | ApplicTP'(op, rands) -> (make_tag_lst op)
                          @ (List.fold_left List.append [] (List.map (make_tag_lst) rands))
  | BoxSet'(name, value) -> make_tag_lst value
  | expr -> []

and make_tag_lst_helper sexpr =
  match sexpr with
  | TaggedSexpr(name, value) -> [(name, value)] @ (make_tag_lst_helper value)
  | Pair(f, s) -> (make_tag_lst_helper f) @ (make_tag_lst_helper s)
  | _ -> []
 
and inc_ref_count ref_count =
  let count = { contents = 0 } in
  if((ref_count := !ref_count + 1) = (count := !count + 1))
    then(ref_count)
  else(ref_count)

and replace_tag_ast tag_lst expr =
  match expr with
  | Var'(x) -> Var'(x)
  | If'(test, dit, dif) -> If'((replace_tag_ast tag_lst test), (replace_tag_ast tag_lst dit), (replace_tag_ast tag_lst dif))
  | Seq'(x) -> Seq'(List.map (replace_tag_ast tag_lst) x)
  | Set'(name, value) -> Set'(name, (replace_tag_ast tag_lst value))
  | Def'(name, value) -> Def'(name, (replace_tag_ast tag_lst value))
  | Or'(x) -> Or'(List.map (replace_tag_ast tag_lst) x)
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (replace_tag_ast tag_lst body))
  | LambdaOpt'(mand, opt, body) -> LambdaOpt'(mand, opt, (replace_tag_ast tag_lst body))
  | Applic'(op, rands) -> Applic'((replace_tag_ast tag_lst op), (List.map (replace_tag_ast tag_lst) rands))
  | ApplicTP'(op, rands) -> ApplicTP'((replace_tag_ast tag_lst op), (List.map (replace_tag_ast tag_lst) rands))
  | BoxSet'(name, value) -> BoxSet'(name, (replace_tag_ast tag_lst value))
  | Const'(x) -> 
    (match x with
    | Sexpr(TaggedSexpr(name, value)) -> Const'(Sexpr(value))
    | Sexpr(TagRef(name)) -> Const'(Sexpr(search_ref_in_lst tag_lst name))
    | Sexpr(Pair(f, s)) -> Const'(Sexpr(Pair((fix_sexpr tag_lst f), (fix_sexpr tag_lst s))))
    | _ -> Const'(x))
  | _ -> expr

and fix_sexpr tag_lst sexpr =
  match sexpr with
  | TaggedSexpr(name, value) -> value
  | TagRef(name) -> search_ref_in_lst tag_lst name
  | Pair(f, s) -> Pair((fix_sexpr tag_lst f), (fix_sexpr tag_lst s))
  | _ -> sexpr

and search_ref_in_lst tag_lst name =
  match tag_lst with
  | [] -> raise X_this_should_not_happen
  | hd :: tl ->
    (match hd with
     | (n, v) when (n = name) -> v
     | _ -> search_ref_in_lst tl name)
  

and scan_ast expr =
  match expr with
  | Const'(x) -> [x]
  | If'(test, dit, dif) -> (scan_ast test) 
                            @ (scan_ast dit)
                            @ (scan_ast dif)
  | Seq'(x) -> List.fold_left List.append [] (List.map scan_ast x)
  | Set'(name, value) -> scan_ast value
  | Def'(name, value) -> scan_ast value
  | Or'(x) -> List.fold_left List.append [] (List.map scan_ast x)
  | LambdaSimple'(params, body) -> scan_ast body
  | LambdaOpt'(mand, opt, body) -> scan_ast body
  | Applic'(op, rands) -> (scan_ast op)
                          @ (List.fold_left List.append [] (List.map scan_ast rands))
  | ApplicTP'(op, rands) -> (scan_ast op)
                          @ (List.fold_left List.append [] (List.map scan_ast rands))
  | BoxSet'(name, value) -> scan_ast value
  | expr -> []

and remove_dups lst = 
  match (List.rev lst) with
  | [] -> []
  | hd :: tl -> if(List.mem hd tl) then(remove_dups (List.rev tl)) else(remove_dups (List.rev tl) @ [hd])

and power_set sexp_list =
  match sexp_list with
  | [] -> []
  | hd :: tl -> (expand_lst hd) @ (power_set tl)

and expand_lst sexp =
  match sexp with
  | Sexpr(Pair(f, s)) -> (expand_lst (Sexpr(f))) @ ((expand_lst (Sexpr(s))) @ [sexp])
  | Sexpr(Symbol(str)) -> (expand_lst (Sexpr(String(str)))) @ [sexp]
  | _ -> [sexp]

and build_tbl off lst =
  match lst with
  | [] -> []
  | hd :: tl -> 
    let new_off = (calc_offset off hd) in
    (make_const_record off hd) @ (build_tbl new_off tl)

and make_const_record off const = 
  match const with
  | Void -> [(Void, (off, "MAKE_VOID"))]
  | Sexpr(Nil) -> [(Sexpr(Nil), (off, "MAKE_NIL"))]
  | Sexpr(Bool(false)) -> [(Sexpr(Bool false), (off, "MAKE_BOOL(0)"))]
  | Sexpr(Bool(true)) -> [(Sexpr(Bool true), (off, "MAKE_BOOL(1)"))]
  | Sexpr(Number(Int(x))) -> [(Sexpr(Number(Int(x))), (off, "MAKE_LITERAL_INT(" ^ (string_of_int x) ^ ")"))]
  | Sexpr(Number(Float(x))) -> [(Sexpr(Number(Float(x))), (off, "MAKE_LITERAL_FLOAT(" ^ (string_of_float x) ^ ")"))]
  | Sexpr(Char(x)) -> [(Sexpr(Char(x)), (off, "MAKE_LITERAL_CHAR(" ^ (string_of_int (Char.code x)) ^ ")"))]
  | Sexpr(Symbol(x)) -> [(Sexpr(Symbol(x)), (off, "MAKE_LITERAL_SYMBOL("))]
  | Sexpr(String(x)) -> let str = String.concat " , " (List.map (fun ch -> string_of_int (Char.code ch)) (string_to_list x)) in
                         [(Sexpr(String(x)), (off, "MAKE_LITERAL_STRING {" ^(* String.escaped *) str ^ "}"))]
  | Sexpr(Pair(f, s)) -> [(Sexpr(Pair(f, s)), (off, "MAKE_LITERAL_PAIR("))] 
  | _ -> []

and calc_offset curr const = 
match const with
  | Void -> curr + 1
  | Sexpr(Nil) -> curr + 1
  | Sexpr(Bool(false)) -> curr + 2
  | Sexpr(Bool(true)) -> curr + 2
  | Sexpr(Number(Int(x))) -> curr + 9
  | Sexpr(Number(Float(x))) -> curr + 9
  | Sexpr(Char(x)) -> curr + 2
  | Sexpr(String(x)) -> curr + 9 + (String.length x)
  | Sexpr(Symbol(x))-> curr + 9
  | Sexpr(Pair(f, s)) -> curr + 17
  | _ -> curr

and record_pair_symbol_helper tbl record = 
  match record with 
  | (Sexpr(Pair(f, s)), (off, "MAKE_LITERAL_PAIR(")) -> 
      (Sexpr(Pair(f, s)), (off, "MAKE_LITERAL_PAIR(" ^ (make_pair_record f off tbl) ^ ", " ^ (make_pair_record s off tbl) ^ ")"))
  | (Sexpr(Symbol(x)), (off, "MAKE_LITERAL_SYMBOL(")) -> 
      (Sexpr(Symbol(x)), (off, "MAKE_LITERAL_SYMBOL(" ^ (make_symbol_record x tbl) ^ ")"))
  | _ -> record

and make_pair_record constant off tbl =
  match tbl with
  | [] -> "const_tbl+" ^ (string_of_int off)
  | (sexpr, (offset, _)) :: tl when(sexpr = Sexpr(constant)) -> "const_tbl+" ^ (string_of_int offset)
  | (sexpr, (offset, _)) :: tl -> make_pair_record constant off tl

and make_symbol_record sym tbl =
  match tbl with
  | [] -> raise X_this_should_not_happen
  | (sexpr, (off, _)) :: tl when(sexpr = Sexpr(String(sym))) -> "const_tbl+" ^ (string_of_int off)
  | (sexpr, (off, _)) :: tl -> make_symbol_record sym tl
    
;;
  (* CONSTANTS TABLE END REGION *)
  
  (* FVARS TABLE START REGION *)
  let primitive_names_to_labels = 
    ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
     "null?", "is_null"; "char?", "is_char"; "string?", "is_string";
     "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
     "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
     "symbol->string", "symbol_to_string"; 
     "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
     "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
    "car", "car"; "cdr", "cdr"; "cons", "cons"; "set-car!", "setcar"; "set-cdr!", "setcdr"; "apply", "apply"];;

let rec make_lst_fvar expr =
  match expr with
  | Var'(VarFree(x)) -> [x]
  | If'(test, dit, dif) -> (make_lst_fvar test) 
                            @ (make_lst_fvar dit)
                            @ (make_lst_fvar dif)
  | Seq'(x) -> List.fold_left List.append [] (List.map make_lst_fvar x)
  | Set'(name, value) -> make_lst_fvar value
  | Def'(Var' (VarFree(x)), value) -> [x] @ (make_lst_fvar value)
  | Or'(x) -> List.fold_left List.append [] (List.map make_lst_fvar x)
  | LambdaSimple'(params, body) -> make_lst_fvar body
  | LambdaOpt'(mand, opt, body) -> make_lst_fvar body
  | Applic'(op, rands) -> (make_lst_fvar op)
                          @ (List.fold_left List.append [] (List.map make_lst_fvar rands))
  | ApplicTP'(op, rands) -> (make_lst_fvar op)
                          @ (List.fold_left List.append [] (List.map make_lst_fvar rands))
  | BoxSet'(name, value) -> make_lst_fvar value
  | expr -> [] 

and fvars_offset lst offset =
  match lst with
  | [] -> []
  | name :: tl -> [(name, offset)] @ (fvars_offset tl (offset+1)) ;;
  (* FVARS TABLE END REGION *)

  (* GENERATE START REGION *)


  (* GENERATE END REGION *)

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys arconst_tbe the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables. 
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;


 module Code_Gen : CODE_GEN = struct
  (* let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;; 
  let generate consts fvars e = raise X_not_yet_implemented;; *)

    let label_counter = ref 0;;
      
    let count () =
      ( label_counter := 1 + !label_counter ;
        !label_counter );;
      
    let make_label base =
      Printf.sprintf "%s_%d" base (count());;
      
    let make_labels bases =
      let n = count() in
      List.map (fun base -> Printf.sprintf "%s_%d" base n)
         bases;;

    
  
let make_consts_tbl expr =
  let offset = {contents = (-1)} in
  let expr = List.map(change_tag_name offset) expr in
  let lst = List.fold_left List.append [] (List.map make_tag_lst expr) in
  let ast = List.map (replace_tag_ast lst) expr in
  let init_lst = [Void; Sexpr(Nil); Sexpr(Bool false); Sexpr(Bool true)] in
  let const_lst = remove_dups (power_set (remove_dups (List.fold_left List.append init_lst (List.map scan_ast ast)))) in
  let tmp_tbl = build_tbl 0 const_lst in
  let tbl = List.map (record_pair_symbol_helper tmp_tbl) tmp_tbl in
  tbl;;  

let make_fvars_tbl expr =
  let prim_names = List.map (fun (name, label) -> name) primitive_names_to_labels in
  let lst = remove_dups (List.fold_left List.append prim_names (List.map make_lst_fvar expr)) in
  fvars_offset lst 0 ;; 

let rec generate consts fvars e =
  (* let expr = (generate_helper_p consts fvars e) in
  generate_helper consts fvars 0 expr *)

  let offset = {contents = (-1)} in
  let ast = change_tag_name offset e in
  let lst = make_tag_lst ast in
  let expr = replace_tag_ast lst ast in
  match expr with
  | Const'(x) -> 
    (match x with
    | Sexpr(TaggedSexpr(name, value)) -> generate_helper consts fvars 0 (Const'(Sexpr(value)))
    | Sexpr(TagRef(name)) -> generate_helper consts fvars 0 (Const'(Sexpr(search_ref_in_lst lst name)))
    | Sexpr(Pair(f, s)) -> generate_helper consts fvars 0 (Const'(Sexpr(Pair((fix_sexpr lst f), (fix_sexpr lst s)))))
    | _ -> generate_helper consts fvars 0 expr)
  | _ -> generate_helper consts fvars 0 expr 

(* and generate_helper_p consts fvars e =
  let offset = {contents = (-1)} in
  let expr = change_tag_name offset e in
  let lst = make_tag_lst expr in
  match expr with
  | Const'(x) -> 
    (match x with
    | Sexpr(TaggedSexpr(name, value)) -> Const'(Sexpr(value))
    | Sexpr(TagRef(name)) -> Const'(Sexpr(search_ref_in_lst lst name))
    | Sexpr(Pair(f, s)) -> Const'(Sexpr(Pair((fix_sexpr lst f), (fix_sexpr lst s))))
    | _ -> expr)
  | _ -> expr  *)

and generate_helper consts fvars nest_count e =
  match e with
  | Const'(x) ->
      let address = get_const_address x consts in
      Printf.sprintf "mov rax, " ^ address ^ "\n"
  | Var'(VarParam(_, minor)) -> Printf.sprintf "mov rax, qword [rbp+8*(4+" ^ (string_of_int minor) ^ ")]\n"
  | Var'(VarBound(_, major, minor)) -> 
      Printf.sprintf "
                      mov rax, qword [rbp+8*2]
                      mov rax, qword [rax+8*" ^ (string_of_int major) ^ "]
                      mov rax, qword [rax+8*" ^ (string_of_int minor) ^ "]
                      "
  | Var'(VarFree(x)) -> 
      let address = get_fvar_address x fvars in
      Printf.sprintf "mov rax, qword [" ^ address ^ "]\n"
      
  | Set'(x, value) ->
      let gen_val = generate_helper consts fvars nest_count value in
      (match x with
      | Var'(VarParam(_, minor)) -> 
          let second_gen = "mov qword [rbp+8*(4+" ^ (string_of_int minor) ^ ")], rax\n
                            mov rax, SOB_VOID_ADDRESS" in
          gen_val ^ Printf.sprintf "%s\n" second_gen
      | Var'(VarBound(_, major, minor)) -> 
          let second_gen = "mov rbx, qword [rbp+8*2]\n
                            mov rbx, qword [rbx+8*" ^ (string_of_int major) ^ "]\n
                            mov qword [rbx+8*" ^ (string_of_int minor) ^ "], rax\n
                            mov rax, SOB_VOID_ADDRESS" in
          gen_val ^ Printf.sprintf "%s\n" second_gen
      | Var'(VarFree(x)) -> 
          let address = get_fvar_address x fvars in 
          let second_gen = "mov qword [" ^ address ^ "], rax\n
                            mov rax, SOB_VOID_ADDRESS" in
          gen_val ^ Printf.sprintf "%s\n" second_gen
      | _ -> "")
  | Def'(x, value) ->
      let gen_val = generate_helper consts fvars nest_count value in
      (match x with
      | Var'(VarParam(_, minor)) -> 
          let second_gen = "mov qword [rbp+8*(4+" ^ (string_of_int minor) ^ ")], rax\n
                            mov rax, SOB_VOID_ADDRESS" in
          gen_val ^ Printf.sprintf "%s\n" second_gen
      | Var'(VarBound(_, major, minor)) -> 
          let second_gen = "mov rbx, qword [rbp+8*2]\n
                            mov rbx, qword [rbx+8*" ^ (string_of_int major) ^ "]\n
                            mov qword [rbx+8*" ^ (string_of_int minor) ^ "], rax\n
                            mov rax, SOB_VOID_ADDRESS" in
          gen_val ^ Printf.sprintf "%s\n" second_gen
      | Var'(VarFree(x)) -> 
          let address = get_fvar_address x fvars in 
          let second_gen = "mov qword [" ^ address ^ "], rax\n
                            mov rax, SOB_VOID_ADDRESS" in
          gen_val ^ Printf.sprintf "%s\n" second_gen
      | _ -> "")
  | Seq'(x) -> String.concat "" (List.map (generate_helper consts fvars nest_count) x)
  | Or'(x) ->
      let exit_label = make_label "Lexit" in
      let last = List.hd (List.rev x) in
      let rest = List.rev (List.tl (List.rev x)) in
      let gen_seq_no_last = List.map (generate_helper consts fvars nest_count) rest in
      let str_seq_no_last = String.concat "" (List.map (fun x -> (x  ^ "cmp rax, SOB_FALSE_ADDRESS\njne " ^ exit_label ^ "\n")) gen_seq_no_last) in
      let gen_last = generate_helper consts fvars nest_count last ^ exit_label ^ ":\n" in
      str_seq_no_last ^ gen_last

  | If'(test, dit, dif) -> 
      let labels = ["Lelse"; "Lexit"] in
      let labels = make_labels labels in
      let gen_test = generate_helper consts fvars nest_count test in
      let test_str = "cmp rax, SOB_FALSE_ADDRESS\nje " ^ (List.nth labels 0) ^ "\n"  in
      let gen_dit = generate_helper consts fvars nest_count dit in
      let dit_str = "jmp " ^ (List.nth labels 1) ^ "\n" ^ (List.nth labels 0) ^ ":\n" in
      let gen_dif = generate_helper consts fvars nest_count dif in
      gen_test ^ Printf.sprintf "%s\n" test_str ^ gen_dit ^ dit_str ^ gen_dif ^ (List.nth labels 1) ^ ":\n"

  | Box'(VarParam(x, minor)) ->
      let get_param = "mov rbx, qword [rbp+8*(4+" ^ (string_of_int minor) ^ ")]" in
      let alloc = "MALLOC rax, WORD_SIZE\nmov qword [rax], rbx\n" in
      Printf.sprintf "%s\n" get_param ^ alloc
  | BoxGet'(x) ->
      let gen_var = generate_helper consts fvars nest_count (Var'(x)) in
      let str = "mov rax, qword [rax]" in
      gen_var ^ Printf.sprintf "%s\n" str
  | BoxSet'(x, value) -> 
      let gen_val = generate_helper consts fvars nest_count value in
      let first_str = "push rax\n" in
      let gen_var = generate_helper consts fvars nest_count (Var'(x)) in
      let second_str = "pop qword [rax]\nmov rax, SOB_VOID_ADDRESS" in
      gen_val ^ Printf.sprintf "%s\n" first_str ^ gen_var ^ Printf.sprintf "%s\n" second_str
  | LambdaSimple'(params, body) -> Printf.sprintf "%s\n" (gen_lambda_simple consts fvars (nest_count+1) params body)
  | Applic'(op, rands) -> Printf.sprintf "%s\n" (gen_applic consts fvars nest_count op rands)
  | ApplicTP'(op, rands) -> Printf.sprintf "%s\n" (gen_applicTP consts fvars nest_count op rands)
  | LambdaOpt'(mand, opt, body) -> Printf.sprintf "%s\n" (gen_lambda_opt consts fvars (nest_count+1) mand [opt] body)
  | _ -> Printf.sprintf ""

  and gen_applic consts fvars nest_count op rands =
    let exit_label = make_label "Lexit" in
    let magic_str = "push SOB_NIL_ADDRESS\t\t; magic\n" in
    let gen_rands = List.map (generate_helper consts fvars nest_count) (List.rev rands) in
    let rands_len = List.length rands in
    let str_rands = 
      (* if(rands_len = 0) then("\n") *)
        (* else *)
        (String.concat "" (List.map (fun x -> (x  ^ "push rax\n")) gen_rands)) in
    let rands_count = "push " ^ (string_of_int rands_len) ^ "\n" in
    let gen_op = generate_helper consts fvars nest_count op in
    let apply_closure =

    "
      mov rsi, rax
      mov bl, byte [rsi]
      cmp bl, T_CLOSURE
      jne " ^ exit_label ^ "\n
 
      CLOSURE_ENV r10, rax
      push r10
      CLOSURE_CODE r10, rax
      call r10

      add rsp, 8*1                          ; pop env
      pop rbx                               ; pop arg count
      inc rbx
      shl rbx, 3                            ; rbx = rbx * 8
      add rsp, rbx                          ; pop args + magic
    " ^ exit_label ^":\n" in
    make_label "APPLIC" ^ ":\n" ^ magic_str ^ str_rands ^ rands_count ^ gen_op ^ apply_closure


  and gen_lambda_simple consts fvars nest_count params body  =
    let labels = ["cp_params"; "cont"; "cp_prev_env"; "end_lambda_body"; "empty_env"; "lambda_body"; "lambda_error"; "skip_cp_prev_env"; "pre_cp_params"; "no_params_to_cp"] in
    let labels = make_labels labels in
    let len = string_of_int (List.length params) in
    let str_nest = string_of_int nest_count in
    let gen_body = (generate_helper consts fvars nest_count body) in
    let str_part1 = 
        "
        mov rcx, " ^ str_nest ^ "             ; size of ext env
        cmp rcx, 1                            ; check if Env_0
        je " ^ (List.nth labels 4) ^ "        ; Env_0

        MALLOC rbx, WORD_SIZE*(" ^ str_nest ^ ")             ; allocate new env, store in rbx
        mov r10, qword [rbp+2*WORD_SIZE]               ; r10 points to prev env
        cmp r10, SOB_NIL_ADDRESS
        je " ^ (List.nth labels 7) ^ "\n
        dec rcx                                       ; dec extEnv size for loop
        "
(*copy prev env to ext env:*)
         ^ (List.nth labels 2) ^ ":                  ; iterate through the arrays from end to start
        mov r12, qword [r10+rcx*WORD_SIZE-WORD_SIZE]         ; copies prevEnv[i-1] to extEnv[i]
        mov [rbx+rcx*WORD_SIZE], r12            ; extEnv[n .. 1]
        loop " ^ (List.nth labels 2) ^ "
        jmp " ^ (List.nth labels 8) ^ "\n\n"

        ^ (List.nth labels 7) ^ ":
        mov qword [rbx+WORD_SIZE], SOB_NIL_ADDRESS
        "
        
        ^ (List.nth labels 8) ^ ":
        mov r9, PARAM_COUNT                         ; r9 = prev arg count
        cmp r9, 0                                  ; check if prevEnv has params
        je " ^ (List.nth labels 9) ^ " 

        inc r9                              ; take magic
        shl r9, 3                                   ; mul prev arg count by WORD_SIZE
        MALLOC rdx, r9                              ; allocate prev_param_array for extEnv

        mov [rbx], qword rdx                              ; extEnv[0] points to prev_param_array

        mov r9, PARAM_COUNT                                 ; prev arg count for .cp_params loop
        mov rcx, PARAM_COUNT                                 ; prev arg count for .cp_params loop
        inc rcx
        "
(*copy params:*)
        ^ (List.nth labels 0) ^ ":                   ; iterate through the arrays from end to start
        mov r12, PVAR(r9)                             ; copies prev params to extEnv[0]
        mov qword [rdx+r9*WORD_SIZE], r12            ; rdx = param_array of extEnv
        dec r9
        loop " ^ (List.nth labels 0) ^ "
        jmp " ^ (List.nth labels 1) ^ "
        
        " ^ (List.nth labels 9) ^ ":
        mov qword [rbx], SOB_NIL_ADDRESS 

        " ^ (List.nth labels 1) ^ ":                  ; prepare for cp_prev_env loop

        MAKE_CLOSURE(rax, rbx, " ^ (List.nth labels 5) ^ ")\n
        jmp " ^ (List.nth labels 3) ^ "\n

        " ^ (List.nth labels 4) ^ ":
        MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ (List.nth labels 5) ^ ")\n
        jmp " ^ (List.nth labels 3) ^ "\n

        " ^ (List.nth labels 5) ^ ":\n
        push rbp
        mov rbp, rsp

        mov rax, " ^ len ^ "\n
        cmp rax, PARAM_COUNT
        jne " ^ (List.nth labels 6) ^ "\n" in
  let str_part2 = 
        "
        leave
        ret\n\n
        jmp " ^ (List.nth labels 3) ^ "\n

        " ^ (List.nth labels 6) ^ ":\n
        mov r8, r8                                  ; to check what this is for
        " ^ (List.nth labels 3) ^ ":\n" in
  str_part1 ^ gen_body ^ str_part2

and gen_applicTP consts fvars nest_count op rands =
  let exit_label = make_label "Lexit" in
  let magic_str = "push SOB_NIL_ADDRESS\t\t; magic\n" in
  let gen_rands = List.map (generate_helper consts fvars nest_count) (List.rev rands) in
  let str_rands = String.concat "" (List.map (fun x -> (x  ^ "push rax\n")) gen_rands) in
  let rands_count = "push " ^ (string_of_int (List.length rands)) ^ "\n" in
  let gen_op = generate_helper consts fvars nest_count op in
  let apply_closure =

  "
    mov rsi, rax
    mov bl, byte [rsi]
    cmp bl, T_CLOSURE
    jne " ^ exit_label ^ "\n

    CLOSURE_ENV r10, rax
    push r10
    
    push qword [rbp + 8*1]        ; old return address
    
    mov r12, " ^ (string_of_int (4 + List.length rands)) ^"    
    mov r14, qword [rbp]
    SHIFT_FRAME r12
    mov rbp, r14
    CLOSURE_CODE r10, rax
    jmp r10

  " ^ exit_label ^":\n" in
  make_label "APPLIC_TP" ^ ":\n" ^ magic_str ^ str_rands ^ rands_count ^ gen_op ^ apply_closure
    

  and gen_lambda_opt consts fvars nest_count mand opt body  =
    let mand_len = string_of_int (List.length mand) in
    (* let opt_len = string_of_int (List.length opt) in *)
    (* let last_arg = string_of_int (List.length mand+List.length opt-1) in *)
    
    let labels = ["cp_params"; "cont"; "cp_prev_env"; "end_lambda_body"; "empty_env"; "lambda_body";
                   "lambda_error"; "skip_cp_prev_env"; "pre_cp_params"; "no_params_to_cp"; "check_opt"; "end_adj_stack"] in
    let labels = make_labels labels in
    let str_nest = string_of_int nest_count in
    let gen_body = (generate_helper consts fvars nest_count body) in
    let str_part1 = 
        "
        mov rcx, " ^ str_nest ^ "             ; size of ext env
        cmp rcx, 1                            ; check if Env_0
        je " ^ (List.nth labels 4) ^ "        ; Env_0

        MALLOC rbx, WORD_SIZE*(" ^ str_nest ^ ")             ; allocate new env, store in rbx
        mov r10, qword [rbp+2*WORD_SIZE]               ; r10 points to prev env
        cmp r10, SOB_NIL_ADDRESS
        je " ^ (List.nth labels 7) ^ "\n
        dec rcx                                       ; dec extEnv size for loop
        "
(*copy prev env to ext env:*)
         ^ (List.nth labels 2) ^ ":                  ; iterate through the arrays from end to start
        mov r12, qword [r10+rcx*WORD_SIZE-WORD_SIZE]         ; copies prevEnv[i-1] to extEnv[i]
        mov [rbx+rcx*WORD_SIZE], r12            ; extEnv[n .. 1]
        loop " ^ (List.nth labels 2) ^ "
        jmp " ^ (List.nth labels 8) ^ "\n\n"

        ^ (List.nth labels 7) ^ ":
        mov qword [rbx+WORD_SIZE], SOB_NIL_ADDRESS
        "
        
        ^ (List.nth labels 8) ^ ":
        mov r9, PARAM_COUNT                         ; r9 = prev arg count
        cmp r9, 0                                  ; check if prevEnv has params
        je " ^ (List.nth labels 9) ^ " 
        
        inc r9                            ; take magic
        shl r9, 3                                   ; mul prev arg count by WORD_SIZE
        MALLOC rdx, r9                              ; allocate prev_param_array for extEnv

        mov [rbx], qword rdx                              ; extEnv[0] points to prev_param_array

        mov r9, PARAM_COUNT                                 ; prev arg count for .cp_params loop
        mov rcx, PARAM_COUNT                                 ; prev arg count for .cp_params loop
        inc rcx
        "
(*copy params:*)
        ^ (List.nth labels 0) ^ ":                   ; iterate through the arrays from end to start
        mov r12, PVAR(r9)                             ; copies prev params to extEnv[0]
        mov qword [rdx+r9*WORD_SIZE], r12            ; rdx = param_array of extEnv
        dec r9
        loop " ^ (List.nth labels 0) ^ "
        jmp " ^ (List.nth labels 1) ^ "
        
        " ^ (List.nth labels 9) ^ ":
        mov qword [rbx], SOB_NIL_ADDRESS 

        " ^ (List.nth labels 1) ^ ":                  ; prepare for cp_prev_env loop

        MAKE_CLOSURE(rax, rbx, " ^ (List.nth labels 5) ^ ")\n
        jmp " ^ (List.nth labels 3) ^ "\n

        " ^ (List.nth labels 4) ^ ":
        MAKE_CLOSURE(rax, SOB_NIL_ADDRESS, " ^ (List.nth labels 5) ^ ")\n
        jmp " ^ (List.nth labels 3) ^ "\n

        " ^ (List.nth labels 5) ^ ":\n
        mov r12, qword [rsp+2*WORD_SIZE]          ; r12 = opt_len
        sub r12, qword " ^ mand_len ^" ; r12 = opt_len

        mov r11, qword [rsp+2*WORD_SIZE]          ; r11 = last_arg
        dec r11                       ; r11 = last_arg

        mov r9, qword 0
        cmp r9, qword " ^ mand_len ^"
        jne " ^ (List.nth labels 10) ^ "
        
        cmp r12, qword 0
        je " ^ (List.nth labels 11) ^ "

        ;only_opt:
        mov qword [rsp+2*WORD_SIZE], 1
        mov r10, qword " ^ mand_len ^"
        MAKE_OPT_LIST r12, r10
        add r10, qword 3
        SHRINK_FRAME r10, r12, r11
        sub r10, qword 3
        jmp " ^ (List.nth labels 11) ^ "

        " ^ (List.nth labels 10) ^ ":
        cmp r12, qword 0
        je " ^ (List.nth labels 11) ^ "

        ;mand_opt:
        mov qword [rsp+2*WORD_SIZE], (" ^ mand_len ^" + 1)
        mov r10, qword " ^ mand_len ^"
        MAKE_OPT_LIST r12, r10
        add r10, qword 3
        SHRINK_FRAME r10, r12, r11
        sub r10, qword 3
        
        " ^ (List.nth labels 11) ^ ":
        push rbp
        mov rbp, rsp
        " in
  let str_part2 = 
        "
        leave
        ret\n\n
        jmp " ^ (List.nth labels 3) ^ "\n

        " ^ (List.nth labels 6) ^ ":\n
        mov r8, r8                                  ; to check what this is for
        " ^ (List.nth labels 3) ^ ":\n" in
  str_part1 ^ gen_body ^ str_part2


and get_const_address expr consts = 
  let ret_val = List.assoc expr consts in
  let offset = (fst ret_val) in
  "const_tbl+" ^ (string_of_int offset)

and get_fvar_address expr fvars =
  let offset = List.assoc expr fvars in
  "fvar_tbl+8*" ^ (string_of_int offset)



(* 
let test s = 
  let expr = (List.map Semantics.run_semantics (Tag_Parser.tag_parse_expressions (Reader.read_sexprs s))) in
  let consts_tbl = Code_Gen.make_consts_tbl expr in
  let fvars_tbl = Code_Gen.make_fvars_tbl expr in
  List.map (Code_Gen.generate consts_tbl fvars_tbl) expr;; *)


end;;