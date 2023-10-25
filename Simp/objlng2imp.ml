let tr_op: Objlng.binop -> Imp.binop = function
  | Add -> Add
  | Mul -> Mul
  | Lt  -> Lt


(* types for various environments *)
module Env = Map.Make(String)
type tenv = Objlng.typ Env.t
type fenv = Objlng.function_def Env.t
type cenv = Objlng.class_def Env.t

let add2env l env =
  List.fold_left (fun env (x, t) -> Env.add x t env) env l


let check_type x t =
  if x <> t then failwith ("type mismatch: expected " ^ (Objlng.string_of_typ x) ^ " but got " ^ (Objlng.string_of_typ t))
  

let get_type_var x env =
  try Env.find x env with Not_found -> failwith ("unknown variable " ^ x)

let get_function f fenv =
  try Env.find f fenv with Not_found -> failwith ("unknown function " ^ f)

let get_class_name (c: Objlng.typ)  =
  match c with 
  | TClass s -> s
  | _ -> failwith "not a class"

let get_class c cenv =
  let cdef = get_class_name c in
  try Env.find cdef cenv with Not_found -> failwith ("unknown class " ^ cdef)

let get_class_from_name c cenv =
  try Env.find c cenv with Not_found -> failwith ("unknown class " ^ c)

let debug_env tenv = 
    Env.bindings tenv |> List.iter (fun (k, v) -> Printf.printf "%s -> %s\n" k (Objlng.string_of_typ v))
let print_env env =
  Env.bindings env |> List.iter (fun (k, v) -> Printf.printf "%s -> %s\n" k (Objlng.string_of_typ v))

let get_method_from_list (m : string ) (methods :  Objlng.function_def list) :Objlng.function_def = 
  let rec aux m methods = 
    match methods with
    | [] -> failwith ("unknown method " ^ m)
    | (x:Objlng.function_def)::methods -> if x.name = m then x else aux m methods
  in aux m methods


let rec get_method cenv c m =
  let cdef : Objlng.class_def = get_class c cenv in
  let methods = cdef.methods in
  try get_method_from_list m methods with Not_found -> failwith ("unknown method " ^ m)



let translate_program (p: Objlng.program) =

  (* initialize global environments *)
  let tenv = add2env p.globals Env.empty in
  let fenv = add2env (List.map (fun (f: Objlng.function_def) -> f.name, f) p.functions) Env.empty in
  let cenv = add2env (List.map (fun s -> s.Objlng.name, s) p.classes) Env.empty in


  (* type checking *)

  (* typing a variable declaration *)
  

 (* typing an expression *)
let rec type_expr tenv cenv fenv (fdef:Objlng.function_def) (e: Objlng.expression) : Objlng.typ =
  match e with
      | Cst n -> TInt
      | Bool b -> TBool
      | Var x -> get_type_var x tenv
      | Binop((Add | Mul)  , e1, e2 ) ->
        let t1  =  type_expr  tenv cenv fenv fdef e1 in 
        let t2 =  type_expr  tenv cenv fenv fdef e2 in
        check_type t1 TInt;
        check_type t2 TInt;
        TInt
      | Binop(Lt, e1, e2 ) ->
        let t1  =  type_expr  tenv cenv fenv fdef  e1 in
        let t2 =  type_expr  tenv cenv fenv fdef e2 in
        check_type t1 TInt;
        check_type t2 TInt;
        TBool
      | Call(f,args) -> type_function  tenv cenv fenv fdef f args
      | MCall(c,m,args) -> type_method  tenv cenv fenv fdef c m args
      | New(c,args) -> type_constructor  tenv cenv fenv fdef c args
      | NewTab (t,e) -> 
        let te = type_expr  tenv cenv fenv fdef e in
        check_type te TInt;
        TArray t
      | Read(mem) -> 
        type_mem  tenv cenv fenv fdef mem
      | This -> 
        debug_env tenv;
        print_env tenv;
        get_type_var "this" tenv
      
    
    and type_mem  tenv cenv fenv fdef (m: Objlng.mem) :Objlng.typ=
       match m with 
       | Arr(ma,e) -> 
        let te = type_expr tenv cenv fenv fdef e in
        check_type te TInt;
        let tm = type_expr  tenv cenv fenv fdef  ma in
        (match tm with 
        | TArray t -> t
        | _ -> failwith "not an array")
       | Atr(c,a) -> 
        let tc = type_expr  tenv cenv fenv fdef c in
        (match tc with 
        | TClass s -> 
          let cdef :Objlng.class_def = get_class tc cenv in
          let t = List.assoc a cdef.fields in
          t
        | _ -> failwith "not a class instance")


    and type_method  tenv cenv fenv fdef c (m : string) args = 
    let tc = type_expr  tenv cenv fenv fdef c in
    let tenv_with_this = add2env [("this", tc)] tenv in
    let method_def = get_method cenv tc m in
    let params = method_def.params in

    let rec aux args params = match args, params with
      | [], [] -> method_def.return
      | e::args, (x,t)::params -> 
        let t' = type_expr  tenv_with_this cenv fenv fdef e in
        check_type t t';
        aux args params
      | _ -> failwith "wrong number of arguments"
    in aux args params



    and type_constructor  tenv cenv fenv fdef c args =
      let cdef = get_class_from_name c cenv in
      let tc = Objlng.TClass cdef.name in
      let constructor = get_method cenv tc "constructor" in
      let params = constructor.params in 
      let rec aux args params = match args, params with
        | [], [] -> tc
        | e::args, (x,t)::params -> 
          let t' = type_expr  tenv cenv fenv fdef e in
          check_type t t';
          aux args params
        | _ -> failwith "wrong number of arguments"
      in aux args params


    and type_function  tenv cenv fenv fdef f args = 
    let tenv_with_dummy_this = add2env [("this", Objlng.TDummy)] tenv in
    let (fdef:Objlng.function_def) = get_function f fenv in
    let params = fdef.params in
    let rec aux args params = match args, params with
      | [], [] -> fdef.return
      | e::args, (x,t)::params -> 
        let t' = type_expr tenv_with_dummy_this cenv fenv fdef e in
        check_type t t';
        aux args params
      | _ -> failwith "wrong number of arguments"
    in aux args params

    in

    (* typing a sequence of instructions *)

 let rec type_seq  tenv cenv fenv fdef (s: Objlng.instruction list) =
      List.iter (type_instr  tenv cenv fenv fdef) s

    and type_instr   tenv cenv fenv fdef (i:Objlng.instruction) : unit = 
      match i with 
      | Putchar e -> 
        let t = type_expr  tenv cenv fenv fdef e in
        check_type t TInt
      | Set(x,e) -> 
        let t = type_expr tenv cenv fenv fdef e in
        let tx = get_type_var x tenv in
        check_type tx t
      | If (e, s1, s2) -> 
        let t = type_expr  tenv cenv fenv fdef e in
        check_type t TBool;
        type_seq  tenv cenv fenv fdef s1;
        type_seq  tenv cenv fenv fdef s2
      | While (e, s) -> 
        let t = type_expr  tenv cenv fenv fdef e in
        check_type t TBool;
        type_seq  tenv cenv fenv fdef s
      | Return e -> 
        let t = type_expr  tenv cenv fenv fdef e in
        check_type t fdef.return
      | Expr e -> 
        let t = type_expr  tenv cenv fenv fdef e in
        check_type t TVoid
      | Write (mem,e) -> 
        let t = type_expr  tenv cenv fenv fdef e in
        let tm = type_mem  tenv cenv fenv fdef mem in
        check_type tm t
      in 


  
  let type_fdef (f: Objlng.function_def) : unit =
    let tenv = add2env f.params Env.empty in
    let tenv = add2env f.locals tenv in
    let tenv = add2env p.globals tenv in
    type_seq tenv cenv fenv f f.code;
    check_type f.return f.return
    in 

  let type_class (c: Objlng.class_def) : unit =
    let tenv = add2env c.fields Env.empty in
    let tenv = add2env p.globals tenv in
    let tenv = add2env [("this", Objlng.TClass c.name)] tenv in
    List.iter type_fdef c.methods;
    List.iter (fun (x,t) -> check_type t (get_type_var x tenv)) c.fields
  
  in

  let type_prog (p: Objlng.program) : unit =
    List.iter type_class p.classes;
    List.iter type_fdef p.functions;
    List.iter (fun (c: Objlng.class_def) -> List.iter type_fdef c.methods) p.classes
  in



 (* translation of an expression *)
    let rec tr_expr  tenv cenv fenv fdef (e: Objlng.expression) : Imp.expression =
      match e with
      | Cst n  -> Cst n
      | Bool b -> Bool b
      | Var x  -> Var x
      | Binop(op, e1, e2) -> Binop(tr_op op, tr_expr  tenv cenv fenv fdef e1, tr_expr  tenv cenv fenv fdef e2)
      | Call(f,args) -> Call(f, List.map (tr_expr tenv cenv fenv fdef) args)
      | MCall(c,m,args) -> tr_mcall  tenv cenv fenv fdef c m args    
      | New(c,args) -> 
         Call(c^"_constructor", List.map (tr_expr  tenv cenv fenv fdef) args)
      | NewTab (t,e) -> Alloc(Binop(Mul, Cst 4, tr_expr  tenv cenv fenv fdef e))
      | Read(mem) -> Deref(tr_mem  tenv cenv fenv fdef mem)
      | This -> Var "this"
      
    and tr_mem  tenv cenv fenv fdef m = 
      match m with
      | Arr(e1,e2) -> Binop(Add, tr_expr  tenv cenv fenv fdef e1, Binop(Mul, tr_expr   tenv cenv fenv fdef e2, Cst 4))
      | Atr(c,a) -> 
        let tc :Objlng.typ = type_expr tenv cenv fenv fdef c in
        let cdef = get_class tc cenv in
        (*we want to get  the offset, ie the number of fields before the one we want to access *)
        let offset = List.length (List.filter (fun (x,t) -> x <> a) cdef.fields) in
        Binop(Add, tr_expr  tenv cenv fenv fdef c, Cst (offset * 4))

    and tr_mcall  tenv cenv fenv fdef c m args = 
      
      match c with
        | This -> 
          let cdef = get_class_name (type_expr  tenv cenv fenv fdef c) in
         Call(cdef^"_"^m, List.map (tr_expr   tenv cenv fenv fdef)  (c::args))
        | _ ->
          let tr_c = tr_expr  tenv cenv fenv fdef c in
          let args = tr_c :: (List.map (tr_expr tenv  cenv fenv fdef) args) in
          let f = Imp.Binop(Add, Imp.Deref tr_c, Cst 4)  in 
          Imp.DCall(Deref f, args)
        in 

let rec tr_seq   tenv cenv fenv fdef  s = 
    List.map (tr_instr fdef) s
    and tr_instr fdef (i: Objlng.instruction) : Imp.instruction =
      match i with
      | Putchar e     -> Putchar(tr_expr  tenv cenv fenv fdef  e)
      | Set(x,e)      -> Set(x, tr_expr tenv  cenv fenv fdef  e)
      | If(e,s1,s2)   -> If(tr_expr  tenv cenv fenv fdef  e, tr_seq  tenv cenv fenv fdef  s1, tr_seq  tenv cenv fenv fdef  s2)
      | While(e,s)    -> While(tr_expr  tenv cenv fenv fdef  e, tr_seq  tenv cenv fenv fdef  s)
      | Return e      -> Return(tr_expr tenv  cenv fenv fdef  e)
      | Expr e        -> Expr(tr_expr  tenv cenv fenv fdef  e)
      | Write(mem,e)  -> Write(tr_mem  tenv cenv fenv fdef  mem, tr_expr   tenv cenv fenv fdef  e)
    in 

let tr_class tenv (c: Objlng.class_def) f :  Imp.function_def list  = 
    
      let tr_method (f:Objlng.function_def) : Imp.function_def  = 
        if f.name = "constructor" then
          let size_field = List.length c.fields in
          let size = (size_field + 1) * 4 in
          let code = Imp.Set("this", Alloc (Cst size))
          :: Write(Var "this", Addr(c.name ^ "_" ^ "descr"))
          :: tr_seq tenv cenv fenv  f f.code @ [Return (Var "this")] in 
          {
            name = f.name ^ "_" ^ c.name;
            params = List.map fst f.params;
            locals = "this" :: List.map fst f.locals;
            code = code;
          }
        else
          {
            name = f.name ^ "_" ^ c.name;
            params = List.map fst f.params;
            locals = "this" :: List.map fst f.locals;
            code = tr_seq tenv cenv fenv f  f.code;
          } 
      in
     List.fold_left (fun acc f -> acc @ [tr_method f]) f c.methods
          
    in


  (* function definition translation *)
let tr_fdef  (f: Objlng.function_def) : Imp.function_def =
  let tenv = add2env f.locals tenv in
  let tenv = add2env f.params tenv in
  let tenv = add2env p.globals tenv in

  (*check if and add this to env*)
  let tenv  = 
    if f.name = "constructor" then
      let cdef = get_class_name f.return in
      add2env [("this", Objlng.TClass cdef)] tenv
    else tenv
  in
  

  type_prog p;
  {
    name = f.name;
    params = List.map fst f.params;
    locals = List.map fst f.locals;
    code = tr_seq tenv cenv fenv  f f.code;
  }
  in 

(* program translation *)

  {
    Imp.globals = List.map fst p.globals;
    functions = List.fold_left (fun f c -> tr_class tenv c f)
      (List.map tr_fdef p.functions) p.classes;
  }



 

