
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | WHILE
    | VAR
    | TYP_VOID
    | TYP_INT
    | TYP_BOOL
    | THIS
    | STAR
    | SET
    | SEMI
    | RPAR
    | RETURN
    | RBRACKET
    | PUTCHAR
    | PLUS
    | NEW
    | METHOD
    | LT
    | LPAR
    | LBRACKET
    | IF
    | IDENT of (
# 17 "objlngparser.mly"
       (string)
# 35 "objlngparser.ml"
  )
    | FUNCTION
    | EXTENDS
    | EOF
    | END
    | ELSE
    | DOT
    | CST of (
# 15 "objlngparser.mly"
       (int)
# 46 "objlngparser.ml"
  )
    | COMMA
    | CLASS
    | BOOL of (
# 16 "objlngparser.mly"
       (bool)
# 53 "objlngparser.ml"
  )
    | BEGIN
    | ATTRIBUTE
  
end

include MenhirBasics

# 1 "objlngparser.mly"
  

  open Lexing
  open Objlng

  let classes = ref []
  let globals = ref []
  let functions = ref []


# 73 "objlngparser.ml"

type ('s, 'r) _menhir_state = 
  | MenhirState000 : ('s, _menhir_box_program) _menhir_state
    (** State 000.
        Stack shape : .
        Start symbol: program. *)

  | MenhirState002 : (('s, _menhir_box_program) _menhir_cell1_VAR, _menhir_box_program) _menhir_state
    (** State 002.
        Stack shape : VAR.
        Start symbol: program. *)

  | MenhirState006 : (('s, _menhir_box_program) _menhir_cell1_LBRACKET, _menhir_box_program) _menhir_state
    (** State 006.
        Stack shape : LBRACKET.
        Start symbol: program. *)

  | MenhirState014 : (('s, _menhir_box_program) _menhir_cell1_FUNCTION, _menhir_box_program) _menhir_state
    (** State 014.
        Stack shape : FUNCTION.
        Start symbol: program. *)

  | MenhirState017 : (('s, _menhir_box_program) _menhir_cell1_typ _menhir_cell0_IDENT, _menhir_box_program) _menhir_state
    (** State 017.
        Stack shape : typ IDENT.
        Start symbol: program. *)

  | MenhirState019 : (('s, _menhir_box_program) _menhir_cell1_typed_ident, _menhir_box_program) _menhir_state
    (** State 019.
        Stack shape : typed_ident.
        Start symbol: program. *)

  | MenhirState024 : ((('s, _menhir_box_program) _menhir_cell1_typ _menhir_cell0_IDENT, _menhir_box_program) _menhir_cell1_loption_separated_nonempty_list_COMMA_typed_ident__, _menhir_box_program) _menhir_state
    (** State 024.
        Stack shape : typ IDENT loption(separated_nonempty_list(COMMA,typed_ident)).
        Start symbol: program. *)

  | MenhirState025 : (('s, _menhir_box_program) _menhir_cell1_variable_decl, _menhir_box_program) _menhir_state
    (** State 025.
        Stack shape : variable_decl.
        Start symbol: program. *)

  | MenhirState027 : (((('s, _menhir_box_program) _menhir_cell1_typ _menhir_cell0_IDENT, _menhir_box_program) _menhir_cell1_loption_separated_nonempty_list_COMMA_typed_ident__, _menhir_box_program) _menhir_cell1_list_variable_decl_, _menhir_box_program) _menhir_state
    (** State 027.
        Stack shape : typ IDENT loption(separated_nonempty_list(COMMA,typed_ident)) list(variable_decl).
        Start symbol: program. *)

  | MenhirState029 : (('s, _menhir_box_program) _menhir_cell1_WHILE, _menhir_box_program) _menhir_state
    (** State 029.
        Stack shape : WHILE.
        Start symbol: program. *)

  | MenhirState032 : (('s, _menhir_box_program) _menhir_cell1_NEW, _menhir_box_program) _menhir_state
    (** State 032.
        Stack shape : NEW.
        Start symbol: program. *)

  | MenhirState034 : ((('s, _menhir_box_program) _menhir_cell1_NEW, _menhir_box_program) _menhir_cell1_typ, _menhir_box_program) _menhir_state
    (** State 034.
        Stack shape : NEW typ.
        Start symbol: program. *)

  | MenhirState035 : (('s, _menhir_box_program) _menhir_cell1_LPAR, _menhir_box_program) _menhir_state
    (** State 035.
        Stack shape : LPAR.
        Start symbol: program. *)

  | MenhirState037 : (('s, _menhir_box_program) _menhir_cell1_IDENT, _menhir_box_program) _menhir_state
    (** State 037.
        Stack shape : IDENT.
        Start symbol: program. *)

  | MenhirState045 : (('s, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_state
    (** State 045.
        Stack shape : expression.
        Start symbol: program. *)

  | MenhirState047 : (('s, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_state
    (** State 047.
        Stack shape : expression.
        Start symbol: program. *)

  | MenhirState050 : (('s, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_state
    (** State 050.
        Stack shape : expression.
        Start symbol: program. *)

  | MenhirState054 : (('s, _menhir_box_program) _menhir_cell1_expression _menhir_cell0_IDENT, _menhir_box_program) _menhir_state
    (** State 054.
        Stack shape : expression IDENT.
        Start symbol: program. *)

  | MenhirState057 : (('s, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_state
    (** State 057.
        Stack shape : expression.
        Start symbol: program. *)

  | MenhirState059 : (('s, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_state
    (** State 059.
        Stack shape : expression.
        Start symbol: program. *)

  | MenhirState066 : (('s, _menhir_box_program) _menhir_cell1_NEW _menhir_cell0_IDENT, _menhir_box_program) _menhir_state
    (** State 066.
        Stack shape : NEW IDENT.
        Start symbol: program. *)

  | MenhirState071 : ((('s, _menhir_box_program) _menhir_cell1_WHILE, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_state
    (** State 071.
        Stack shape : WHILE expression.
        Start symbol: program. *)

  | MenhirState072 : (('s, _menhir_box_program) _menhir_cell1_RETURN, _menhir_box_program) _menhir_state
    (** State 072.
        Stack shape : RETURN.
        Start symbol: program. *)

  | MenhirState076 : (('s, _menhir_box_program) _menhir_cell1_PUTCHAR, _menhir_box_program) _menhir_state
    (** State 076.
        Stack shape : PUTCHAR.
        Start symbol: program. *)

  | MenhirState081 : (('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_state
    (** State 081.
        Stack shape : IF.
        Start symbol: program. *)

  | MenhirState084 : ((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_state
    (** State 084.
        Stack shape : IF expression.
        Start symbol: program. *)

  | MenhirState086 : (('s, _menhir_box_program) _menhir_cell1_IDENT, _menhir_box_program) _menhir_state
    (** State 086.
        Stack shape : IDENT.
        Start symbol: program. *)

  | MenhirState090 : (('s, _menhir_box_program) _menhir_cell1_mem_access, _menhir_box_program) _menhir_state
    (** State 090.
        Stack shape : mem_access.
        Start symbol: program. *)

  | MenhirState096 : (((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_cell1_list_instruction_, _menhir_box_program) _menhir_state
    (** State 096.
        Stack shape : IF expression list(instruction).
        Start symbol: program. *)

  | MenhirState099 : (('s, _menhir_box_program) _menhir_cell1_instruction, _menhir_box_program) _menhir_state
    (** State 099.
        Stack shape : instruction.
        Start symbol: program. *)

  | MenhirState113 : (('s, _menhir_box_program) _menhir_cell1_CLASS _menhir_cell0_IDENT _menhir_cell0_option___anonymous_0_, _menhir_box_program) _menhir_state
    (** State 113.
        Stack shape : CLASS IDENT option(__anonymous_0).
        Start symbol: program. *)

  | MenhirState114 : (('s, _menhir_box_program) _menhir_cell1_ATTRIBUTE, _menhir_box_program) _menhir_state
    (** State 114.
        Stack shape : ATTRIBUTE.
        Start symbol: program. *)

  | MenhirState117 : ((('s, _menhir_box_program) _menhir_cell1_CLASS _menhir_cell0_IDENT _menhir_cell0_option___anonymous_0_, _menhir_box_program) _menhir_cell1_list_attribute_decl_, _menhir_box_program) _menhir_state
    (** State 117.
        Stack shape : CLASS IDENT option(__anonymous_0) list(attribute_decl).
        Start symbol: program. *)

  | MenhirState118 : (('s, _menhir_box_program) _menhir_cell1_METHOD, _menhir_box_program) _menhir_state
    (** State 118.
        Stack shape : METHOD.
        Start symbol: program. *)

  | MenhirState120 : (('s, _menhir_box_program) _menhir_cell1_method_def, _menhir_box_program) _menhir_state
    (** State 120.
        Stack shape : method_def.
        Start symbol: program. *)

  | MenhirState124 : (('s, _menhir_box_program) _menhir_cell1_attribute_decl, _menhir_box_program) _menhir_state
    (** State 124.
        Stack shape : attribute_decl.
        Start symbol: program. *)

  | MenhirState131 : (('s, _menhir_box_program) _menhir_cell1_decl, _menhir_box_program) _menhir_state
    (** State 131.
        Stack shape : decl.
        Start symbol: program. *)


and ('s, 'r) _menhir_cell1_attribute_decl = 
  | MenhirCell1_attribute_decl of 's * ('s, 'r) _menhir_state * (string * Objlng.typ)

and ('s, 'r) _menhir_cell1_decl = 
  | MenhirCell1_decl of 's * ('s, 'r) _menhir_state * (unit)

and ('s, 'r) _menhir_cell1_expression = 
  | MenhirCell1_expression of 's * ('s, 'r) _menhir_state * (Objlng.expression)

and ('s, 'r) _menhir_cell1_instruction = 
  | MenhirCell1_instruction of 's * ('s, 'r) _menhir_state * (Objlng.instruction)

and ('s, 'r) _menhir_cell1_list_attribute_decl_ = 
  | MenhirCell1_list_attribute_decl_ of 's * ('s, 'r) _menhir_state * ((string * Objlng.typ) list)

and ('s, 'r) _menhir_cell1_list_instruction_ = 
  | MenhirCell1_list_instruction_ of 's * ('s, 'r) _menhir_state * (Objlng.sequence)

and ('s, 'r) _menhir_cell1_list_variable_decl_ = 
  | MenhirCell1_list_variable_decl_ of 's * ('s, 'r) _menhir_state * ((string * Objlng.typ) list)

and ('s, 'r) _menhir_cell1_loption_separated_nonempty_list_COMMA_typed_ident__ = 
  | MenhirCell1_loption_separated_nonempty_list_COMMA_typed_ident__ of 's * ('s, 'r) _menhir_state * ((string * Objlng.typ) list)

and ('s, 'r) _menhir_cell1_mem_access = 
  | MenhirCell1_mem_access of 's * ('s, 'r) _menhir_state * (Objlng.mem)

and ('s, 'r) _menhir_cell1_method_def = 
  | MenhirCell1_method_def of 's * ('s, 'r) _menhir_state * (Objlng.function_def)

and 's _menhir_cell0_option___anonymous_0_ = 
  | MenhirCell0_option___anonymous_0_ of 's * (string option)

and ('s, 'r) _menhir_cell1_typ = 
  | MenhirCell1_typ of 's * ('s, 'r) _menhir_state * (Objlng.typ)

and ('s, 'r) _menhir_cell1_typed_ident = 
  | MenhirCell1_typed_ident of 's * ('s, 'r) _menhir_state * (string * Objlng.typ)

and ('s, 'r) _menhir_cell1_variable_decl = 
  | MenhirCell1_variable_decl of 's * ('s, 'r) _menhir_state * (string * Objlng.typ)

and ('s, 'r) _menhir_cell1_ATTRIBUTE = 
  | MenhirCell1_ATTRIBUTE of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_CLASS = 
  | MenhirCell1_CLASS of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_FUNCTION = 
  | MenhirCell1_FUNCTION of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_IDENT = 
  | MenhirCell1_IDENT of 's * ('s, 'r) _menhir_state * (
# 17 "objlngparser.mly"
       (string)
# 317 "objlngparser.ml"
)

and 's _menhir_cell0_IDENT = 
  | MenhirCell0_IDENT of 's * (
# 17 "objlngparser.mly"
       (string)
# 324 "objlngparser.ml"
)

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LBRACKET = 
  | MenhirCell1_LBRACKET of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_LPAR = 
  | MenhirCell1_LPAR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_METHOD = 
  | MenhirCell1_METHOD of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_NEW = 
  | MenhirCell1_NEW of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_PUTCHAR = 
  | MenhirCell1_PUTCHAR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_RETURN = 
  | MenhirCell1_RETURN of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_VAR = 
  | MenhirCell1_VAR of 's * ('s, 'r) _menhir_state

and ('s, 'r) _menhir_cell1_WHILE = 
  | MenhirCell1_WHILE of 's * ('s, 'r) _menhir_state

and _menhir_box_program = 
  | MenhirBox_program of (Objlng.program) [@@unboxed]

let _menhir_action_01 =
  fun tid ->
    (
# 68 "objlngparser.mly"
                                 ( tid )
# 362 "objlngparser.ml"
     : (string * Objlng.typ))

let _menhir_action_02 =
  fun fields methods name parent ->
    (
# 60 "objlngparser.mly"
   ( { name; fields; methods; parent; } )
# 370 "objlngparser.ml"
     : (Objlng.class_def))

let _menhir_action_03 =
  fun c ->
    (
# 51 "objlngparser.mly"
              ( classes := c :: !classes )
# 378 "objlngparser.ml"
     : (unit))

let _menhir_action_04 =
  fun v ->
    (
# 52 "objlngparser.mly"
                  ( let id, ty = v in globals := (id, ty) :: !globals )
# 386 "objlngparser.ml"
     : (unit))

let _menhir_action_05 =
  fun f ->
    (
# 53 "objlngparser.mly"
                 ( functions := f :: !functions )
# 394 "objlngparser.ml"
     : (unit))

let _menhir_action_06 =
  fun n ->
    (
# 116 "objlngparser.mly"
        ( Cst n )
# 402 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_07 =
  fun b ->
    (
# 117 "objlngparser.mly"
         ( Bool b )
# 410 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_08 =
  fun id ->
    (
# 118 "objlngparser.mly"
           ( Var id )
# 418 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_09 =
  fun e ->
    (
# 119 "objlngparser.mly"
                         ( e )
# 426 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_10 =
  fun e1 e2 ->
    let op = 
# 130 "objlngparser.mly"
       ( Add )
# 434 "objlngparser.ml"
     in
    (
# 120 "objlngparser.mly"
                                       ( Binop(op, e1, e2) )
# 439 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_11 =
  fun e1 e2 ->
    let op = 
# 131 "objlngparser.mly"
       ( Mul )
# 447 "objlngparser.ml"
     in
    (
# 120 "objlngparser.mly"
                                       ( Binop(op, e1, e2) )
# 452 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_12 =
  fun e1 e2 ->
    let op = 
# 132 "objlngparser.mly"
     ( Lt )
# 460 "objlngparser.ml"
     in
    (
# 120 "objlngparser.mly"
                                       ( Binop(op, e1, e2) )
# 465 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_13 =
  fun f xs ->
    let params = 
# 229 "<standard.mly>"
    ( xs )
# 473 "objlngparser.ml"
     in
    (
# 121 "objlngparser.mly"
                                                             ( Call(f, params) )
# 478 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_14 =
  fun e f xs ->
    let params = 
# 229 "<standard.mly>"
    ( xs )
# 486 "objlngparser.ml"
     in
    (
# 122 "objlngparser.mly"
                                                                              ( MCall(e, f, params) )
# 491 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_15 =
  fun id xs ->
    let params = 
# 229 "<standard.mly>"
    ( xs )
# 499 "objlngparser.ml"
     in
    (
# 123 "objlngparser.mly"
                                                                  ( New(id, params) )
# 504 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_16 =
  fun e ty ->
    (
# 124 "objlngparser.mly"
                                                  ( NewTab(ty, e) )
# 512 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_17 =
  fun m ->
    (
# 125 "objlngparser.mly"
               ( Read m )
# 520 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_18 =
  fun () ->
    (
# 126 "objlngparser.mly"
       ( This )
# 528 "objlngparser.ml"
     : (Objlng.expression))

let _menhir_action_19 =
  fun code locals name return xs ->
    let params = 
# 229 "<standard.mly>"
    ( xs )
# 536 "objlngparser.ml"
     in
    (
# 94 "objlngparser.mly"
    ( {name; code; params; return; locals} )
# 541 "objlngparser.ml"
     : (Objlng.function_def))

let _menhir_action_20 =
  fun fdef ->
    (
# 84 "objlngparser.mly"
                        ( fdef )
# 549 "objlngparser.ml"
     : (Objlng.function_def))

let _menhir_action_21 =
  fun e ->
    (
# 98 "objlngparser.mly"
                                      ( Putchar(e) )
# 557 "objlngparser.ml"
     : (Objlng.instruction))

let _menhir_action_22 =
  fun e id ->
    (
# 99 "objlngparser.mly"
                                 ( Set(id, e) )
# 565 "objlngparser.ml"
     : (Objlng.instruction))

let _menhir_action_23 =
  fun c s1 s2 ->
    (
# 102 "objlngparser.mly"
                                        ( If(c, s1, s2) )
# 573 "objlngparser.ml"
     : (Objlng.instruction))

let _menhir_action_24 =
  fun c s ->
    (
# 104 "objlngparser.mly"
                                  ( While(c, s) )
# 581 "objlngparser.ml"
     : (Objlng.instruction))

let _menhir_action_25 =
  fun e ->
    (
# 105 "objlngparser.mly"
                           ( Return(e) )
# 589 "objlngparser.ml"
     : (Objlng.instruction))

let _menhir_action_26 =
  fun e ->
    (
# 106 "objlngparser.mly"
                    ( Expr(e) )
# 597 "objlngparser.ml"
     : (Objlng.instruction))

let _menhir_action_27 =
  fun e m ->
    (
# 107 "objlngparser.mly"
                                     ( Write(m, e) )
# 605 "objlngparser.ml"
     : (Objlng.instruction))

let _menhir_action_28 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 613 "objlngparser.ml"
     : ((string * Objlng.typ) list))

let _menhir_action_29 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 621 "objlngparser.ml"
     : ((string * Objlng.typ) list))

let _menhir_action_30 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 629 "objlngparser.ml"
     : (unit list))

let _menhir_action_31 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 637 "objlngparser.ml"
     : (unit list))

let _menhir_action_32 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 645 "objlngparser.ml"
     : (Objlng.sequence))

let _menhir_action_33 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 653 "objlngparser.ml"
     : (Objlng.sequence))

let _menhir_action_34 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 661 "objlngparser.ml"
     : (Objlng.function_def list))

let _menhir_action_35 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 669 "objlngparser.ml"
     : (Objlng.function_def list))

let _menhir_action_36 =
  fun () ->
    (
# 208 "<standard.mly>"
    ( [] )
# 677 "objlngparser.ml"
     : ((string * Objlng.typ) list))

let _menhir_action_37 =
  fun x xs ->
    (
# 210 "<standard.mly>"
    ( x :: xs )
# 685 "objlngparser.ml"
     : ((string * Objlng.typ) list))

let _menhir_action_38 =
  fun () ->
    (
# 139 "<standard.mly>"
    ( [] )
# 693 "objlngparser.ml"
     : (Objlng.expression list))

let _menhir_action_39 =
  fun x ->
    (
# 141 "<standard.mly>"
    ( x )
# 701 "objlngparser.ml"
     : (Objlng.expression list))

let _menhir_action_40 =
  fun () ->
    (
# 139 "<standard.mly>"
    ( [] )
# 709 "objlngparser.ml"
     : ((string * Objlng.typ) list))

let _menhir_action_41 =
  fun x ->
    (
# 141 "<standard.mly>"
    ( x )
# 717 "objlngparser.ml"
     : ((string * Objlng.typ) list))

let _menhir_action_42 =
  fun e1 e2 ->
    (
# 111 "objlngparser.mly"
                                                ( Arr(e1, e2) )
# 725 "objlngparser.ml"
     : (Objlng.mem))

let _menhir_action_43 =
  fun e id ->
    (
# 112 "objlngparser.mly"
                            ( Atr(e, id) )
# 733 "objlngparser.ml"
     : (Objlng.mem))

let _menhir_action_44 =
  fun mdef ->
    (
# 88 "objlngparser.mly"
                      ( mdef )
# 741 "objlngparser.ml"
     : (Objlng.function_def))

let _menhir_action_45 =
  fun () ->
    (
# 111 "<standard.mly>"
    ( None )
# 749 "objlngparser.ml"
     : (string option))

let _menhir_action_46 =
  fun p ->
    let x = 
# 58 "objlngparser.mly"
                                                 ( p )
# 757 "objlngparser.ml"
     in
    (
# 113 "<standard.mly>"
    ( Some x )
# 762 "objlngparser.ml"
     : (string option))

let _menhir_action_47 =
  fun () ->
    (
# 38 "objlngparser.mly"
    ( {classes = List.rev !classes;
       functions = List.rev !functions;
       globals = List.rev !globals} )
# 772 "objlngparser.ml"
     : (Objlng.program))

let _menhir_action_48 =
  fun _startpos__1_ ->
    let _ = let _startpos = _startpos__1_ in
    (
# 41 "objlngparser.mly"
        ( let pos = _startpos in
          let message =
            Printf.sprintf
              "Syntax error at %d, %d"
              pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
          in
          failwith message )
# 787 "objlngparser.ml"
     : (Objlng.program)) in
    prerr_string "Menhir: misuse: the semantic action associated with the production\nprogram -> error\nis expected to abort the parser, but does not do so.\n";
    assert false

let _menhir_action_49 =
  fun x ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 797 "objlngparser.ml"
     : (Objlng.expression list))

let _menhir_action_50 =
  fun x xs ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 805 "objlngparser.ml"
     : (Objlng.expression list))

let _menhir_action_51 =
  fun x ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 813 "objlngparser.ml"
     : ((string * Objlng.typ) list))

let _menhir_action_52 =
  fun x xs ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 821 "objlngparser.ml"
     : ((string * Objlng.typ) list))

let _menhir_action_53 =
  fun () ->
    (
# 76 "objlngparser.mly"
          ( TInt )
# 829 "objlngparser.ml"
     : (Objlng.typ))

let _menhir_action_54 =
  fun () ->
    (
# 77 "objlngparser.mly"
           ( TBool )
# 837 "objlngparser.ml"
     : (Objlng.typ))

let _menhir_action_55 =
  fun () ->
    (
# 78 "objlngparser.mly"
           ( TVoid )
# 845 "objlngparser.ml"
     : (Objlng.typ))

let _menhir_action_56 =
  fun ty ->
    (
# 79 "objlngparser.mly"
                           ( TArray ty )
# 853 "objlngparser.ml"
     : (Objlng.typ))

let _menhir_action_57 =
  fun id ->
    (
# 80 "objlngparser.mly"
           ( TClass id )
# 861 "objlngparser.ml"
     : (Objlng.typ))

let _menhir_action_58 =
  fun id ty ->
    (
# 72 "objlngparser.mly"
                  ( id, ty )
# 869 "objlngparser.ml"
     : (string * Objlng.typ))

let _menhir_action_59 =
  fun tid ->
    (
# 64 "objlngparser.mly"
                           ( tid )
# 877 "objlngparser.ml"
     : (string * Objlng.typ))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | ATTRIBUTE ->
        "ATTRIBUTE"
    | BEGIN ->
        "BEGIN"
    | BOOL _ ->
        "BOOL"
    | CLASS ->
        "CLASS"
    | COMMA ->
        "COMMA"
    | CST _ ->
        "CST"
    | DOT ->
        "DOT"
    | ELSE ->
        "ELSE"
    | END ->
        "END"
    | EOF ->
        "EOF"
    | EXTENDS ->
        "EXTENDS"
    | FUNCTION ->
        "FUNCTION"
    | IDENT _ ->
        "IDENT"
    | IF ->
        "IF"
    | LBRACKET ->
        "LBRACKET"
    | LPAR ->
        "LPAR"
    | LT ->
        "LT"
    | METHOD ->
        "METHOD"
    | NEW ->
        "NEW"
    | PLUS ->
        "PLUS"
    | PUTCHAR ->
        "PUTCHAR"
    | RBRACKET ->
        "RBRACKET"
    | RETURN ->
        "RETURN"
    | RPAR ->
        "RPAR"
    | SEMI ->
        "SEMI"
    | SET ->
        "SET"
    | STAR ->
        "STAR"
    | THIS ->
        "THIS"
    | TYP_BOOL ->
        "TYP_BOOL"
    | TYP_INT ->
        "TYP_INT"
    | TYP_VOID ->
        "TYP_VOID"
    | VAR ->
        "VAR"
    | WHILE ->
        "WHILE"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37"]
  
  let _menhir_run_128 : type  ttv_stack. ttv_stack -> _menhir_box_program =
    fun _menhir_stack ->
      let _v = _menhir_action_47 () in
      MenhirBox_program _v
  
  let rec _menhir_run_132 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_decl -> _ -> _menhir_box_program =
    fun _menhir_stack _v ->
      let MenhirCell1_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_31 x xs in
      _menhir_goto_list_decl_ _menhir_stack _v _menhir_s
  
  and _menhir_goto_list_decl_ : type  ttv_stack. ttv_stack -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _v _menhir_s ->
      match _menhir_s with
      | MenhirState131 ->
          _menhir_run_132 _menhir_stack _v
      | MenhirState000 ->
          _menhir_run_128 _menhir_stack
      | _ ->
          _menhir_fail ()
  
  let rec _menhir_run_002 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_VAR (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState002 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYP_VOID ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_INT ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_BOOL ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_003 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_55 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_typ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState032 ->
          _menhir_run_033 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState118 ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState014 ->
          _menhir_run_015 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState114 ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState019 ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState002 ->
          _menhir_run_012 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState006 ->
          _menhir_run_008 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_033 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_NEW as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_s = MenhirState034 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | THIS ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NEW ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAR ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BOOL _v ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_030 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_18 () in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_expression : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState027 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState071 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState084 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_101 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_091 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState086 ->
          _menhir_run_087 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState081 ->
          _menhir_run_082 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_077 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_073 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState029 ->
          _menhir_run_069 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_063 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState035 ->
          _menhir_run_061 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_058 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState050 ->
          _menhir_run_051 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState047 ->
          _menhir_run_048 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState045 ->
          _menhir_run_046 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState037 ->
          _menhir_run_044 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_101 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let e = _v in
          let _v = _menhir_action_26 e in
          _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_045 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expression -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState045 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_031 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_NEW (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LBRACKET ->
          let _menhir_s = MenhirState032 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TYP_VOID ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TYP_INT ->
              _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TYP_BOOL ->
              _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACKET ->
              _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAR ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | THIS ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
              | NEW ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
              | LPAR ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState066
              | IDENT _v_0 ->
                  _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState066
              | CST _v_1 ->
                  _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState066
              | BOOL _v_2 ->
                  _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState066
              | RPAR ->
                  let _v_3 = _menhir_action_38 () in
                  _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_004 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_53 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_005 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let _v = _menhir_action_54 () in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_006 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LBRACKET (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState006 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYP_VOID ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_INT ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_BOOL ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_007 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let id = _v in
      let _v = _menhir_action_57 id in
      _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_035 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_LPAR (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState035 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_036 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAR ->
          let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | DOT | LBRACKET | LT | PLUS | RBRACKET | RPAR | SEMI | STAR ->
          let id = _v in
          let _v = _menhir_action_08 id in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_037 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_IDENT -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState037
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState037
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState037
      | IDENT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState037
      | CST _v ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState037
      | BOOL _v ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState037
      | RPAR ->
          let _v = _menhir_action_38 () in
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _eRR ()
  
  and _menhir_run_038 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let n = _v in
      let _v = _menhir_action_06 n in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_039 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let b = _v in
      let _v = _menhir_action_07 b in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_042 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_IDENT -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_IDENT (_menhir_stack, _menhir_s, f) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_13 f xs in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_067 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_NEW _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, id) = _menhir_stack in
      let MenhirCell1_NEW (_menhir_stack, _menhir_s) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_15 id xs in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_instruction : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_instruction (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | RETURN ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | PUTCHAR ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | IF ->
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState099
      | IDENT _v_0 ->
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState099
      | CST _v_1 ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState099
      | BOOL _v_2 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState099
      | END ->
          let _v_3 = _menhir_action_32 () in
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3
      | _ ->
          _eRR ()
  
  and _menhir_run_028 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_WHILE (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAR ->
          let _menhir_s = MenhirState029 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | THIS ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NEW ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAR ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BOOL _v ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_072 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_RETURN (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState072 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_075 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_PUTCHAR (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAR ->
          let _menhir_s = MenhirState076 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | THIS ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NEW ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAR ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BOOL _v ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_080 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAR ->
          let _menhir_s = MenhirState081 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | THIS ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NEW ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAR ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BOOL _v ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_085 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | SET ->
          let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState086 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | THIS ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NEW ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAR ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BOOL _v ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | LPAR ->
          let _menhir_stack = MenhirCell1_IDENT (_menhir_stack, _menhir_s, _v) in
          _menhir_run_037 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT | LBRACKET | LT | PLUS | SEMI | STAR ->
          let id = _v in
          let _v = _menhir_action_08 id in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_100 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_instruction -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_instruction (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_33 x xs in
      _menhir_goto_list_instruction_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_list_instruction_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState027 ->
          _menhir_run_105 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState071 ->
          _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState099 ->
          _menhir_run_100 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState096 ->
          _menhir_run_097 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState084 ->
          _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_105 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_typ _menhir_cell0_IDENT, _menhir_box_program) _menhir_cell1_loption_separated_nonempty_list_COMMA_typed_ident__, _menhir_box_program) _menhir_cell1_list_variable_decl_ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_list_variable_decl_ (_menhir_stack, _, locals) = _menhir_stack in
      let MenhirCell1_loption_separated_nonempty_list_COMMA_typed_ident__ (_menhir_stack, _, xs) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, name) = _menhir_stack in
      let MenhirCell1_typ (_menhir_stack, _menhir_s, return) = _menhir_stack in
      let code = _v in
      let _v = _menhir_action_19 code locals name return xs in
      _menhir_goto_fun_def _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_fun_def : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState118 ->
          _menhir_run_119 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState014 ->
          _menhir_run_107 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_119 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_METHOD -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_METHOD (_menhir_stack, _menhir_s) = _menhir_stack in
      let mdef = _v in
      let _v = _menhir_action_44 mdef in
      let _menhir_stack = MenhirCell1_method_def (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | METHOD ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState120
      | END ->
          let _v_0 = _menhir_action_34 () in
          _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
      | _ ->
          _eRR ()
  
  and _menhir_run_118 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_METHOD (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState118 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYP_VOID ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_INT ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_BOOL ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_121 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_method_def -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_method_def (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_35 x xs in
      _menhir_goto_list_method_def_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_list_method_def_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState117 ->
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState120 ->
          _menhir_run_121 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_122 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_CLASS _menhir_cell0_IDENT _menhir_cell0_option___anonymous_0_, _menhir_box_program) _menhir_cell1_list_attribute_decl_ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_list_attribute_decl_ (_menhir_stack, _, fields) = _menhir_stack in
      let MenhirCell0_option___anonymous_0_ (_menhir_stack, parent) = _menhir_stack in
      let MenhirCell0_IDENT (_menhir_stack, name) = _menhir_stack in
      let MenhirCell1_CLASS (_menhir_stack, _menhir_s) = _menhir_stack in
      let methods = _v in
      let _v = _menhir_action_02 fields methods name parent in
      let c = _v in
      let _v = _menhir_action_03 c in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_decl (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VAR ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState131
      | FUNCTION ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState131
      | CLASS ->
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState131
      | EOF ->
          let _v_0 = _menhir_action_30 () in
          _menhir_run_132 _menhir_stack _v_0
      | _ ->
          _eRR ()
  
  and _menhir_run_014 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_FUNCTION (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState014 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYP_VOID ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_INT ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_BOOL ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_108 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_CLASS (_menhir_stack, _menhir_s) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | EXTENDS ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | IDENT _v_0 ->
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let p = _v_0 in
                  let _v = _menhir_action_46 p in
                  _menhir_goto_option___anonymous_0_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
              | _ ->
                  _eRR ())
          | BEGIN ->
              let _v = _menhir_action_45 () in
              _menhir_goto_option___anonymous_0_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_option___anonymous_0_ : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_CLASS _menhir_cell0_IDENT -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let _menhir_stack = MenhirCell0_option___anonymous_0_ (_menhir_stack, _v) in
      match (_tok : MenhirBasics.token) with
      | BEGIN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | ATTRIBUTE ->
              _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState113
          | END | METHOD ->
              let _v_0 = _menhir_action_28 () in
              _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState113 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_114 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _menhir_stack = MenhirCell1_ATTRIBUTE (_menhir_stack, _menhir_s) in
      let _menhir_s = MenhirState114 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | TYP_VOID ->
          _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_INT ->
          _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | TYP_BOOL ->
          _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LBRACKET ->
          _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_117 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_CLASS _menhir_cell0_IDENT _menhir_cell0_option___anonymous_0_ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_list_attribute_decl_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | METHOD ->
          _menhir_run_118 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState117
      | END ->
          let _v_0 = _menhir_action_34 () in
          _menhir_run_122 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_107 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_FUNCTION -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_FUNCTION (_menhir_stack, _menhir_s) = _menhir_stack in
      let fdef = _v in
      let _v = _menhir_action_20 fdef in
      let f = _v in
      let _v = _menhir_action_05 f in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_103 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_WHILE, _menhir_box_program) _menhir_cell1_expression -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_expression (_menhir_stack, _, c) = _menhir_stack in
      let MenhirCell1_WHILE (_menhir_stack, _menhir_s) = _menhir_stack in
      let s = _v in
      let _v = _menhir_action_24 c s in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_097 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expression, _menhir_box_program) _menhir_cell1_list_instruction_ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_list_instruction_ (_menhir_stack, _, s1) = _menhir_stack in
      let MenhirCell1_expression (_menhir_stack, _, c) = _menhir_stack in
      let MenhirCell1_IF (_menhir_stack, _menhir_s) = _menhir_stack in
      let s2 = _v in
      let _v = _menhir_action_23 c s1 s2 in
      _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_093 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_expression as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_list_instruction_ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | BEGIN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | WHILE ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
              | THIS ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
              | RETURN ->
                  _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
              | PUTCHAR ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
              | NEW ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
              | LPAR ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
              | IF ->
                  _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState096
              | IDENT _v_0 ->
                  _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState096
              | CST _v_1 ->
                  _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState096
              | BOOL _v_2 ->
                  _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState096
              | END ->
                  let _v_3 = _menhir_action_32 () in
                  _menhir_run_097 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_050 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expression -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState050 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_057 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expression -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState057 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_047 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expression -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _menhir_s = MenhirState047 in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
      | IDENT _v ->
          _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | CST _v ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | BOOL _v ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_052 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expression -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | IDENT _v ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAR ->
              let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v) in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | THIS ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState054
              | NEW ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState054
              | LPAR ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState054
              | IDENT _v_0 ->
                  _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState054
              | CST _v_1 ->
                  _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState054
              | BOOL _v_2 ->
                  _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState054
              | RPAR ->
                  let _v_3 = _menhir_action_38 () in
                  _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3
              | _ ->
                  _eRR ())
          | COMMA | DOT | LBRACKET | LT | PLUS | RBRACKET | RPAR | SEMI | SET | STAR ->
              let MenhirCell1_expression (_menhir_stack, _menhir_s, e) = _menhir_stack in
              let id = _v in
              let _v = _menhir_action_43 e id in
              _menhir_goto_mem_access _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_055 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expression _menhir_cell0_IDENT -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell0_IDENT (_menhir_stack, f) = _menhir_stack in
      let MenhirCell1_expression (_menhir_stack, _menhir_s, e) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_14 e f xs in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_mem_access : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState027 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState071 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState099 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState096 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState084 ->
          _menhir_run_089 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState090 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState086 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState081 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState076 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState072 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState029 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState066 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState034 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState035 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState059 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState057 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState054 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState050 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState047 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState045 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState037 ->
          _menhir_run_041 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_089 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | SET ->
          let _menhir_stack = MenhirCell1_mem_access (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState090 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | THIS ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NEW ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAR ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BOOL _v ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | DOT | LBRACKET | LT | PLUS | SEMI | STAR ->
          let m = _v in
          let _v = _menhir_action_17 m in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_041 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let m = _v in
      let _v = _menhir_action_17 m in
      _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_091 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_mem_access as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_mem_access (_menhir_stack, _menhir_s, m) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_27 e m in
          _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_087 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_IDENT (_menhir_stack, _menhir_s, id) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_22 e id in
          _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_082 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAR ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | BEGIN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | WHILE ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
              | THIS ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
              | RETURN ->
                  _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
              | PUTCHAR ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
              | NEW ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
              | LPAR ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
              | IF ->
                  _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState084
              | IDENT _v_0 ->
                  _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState084
              | CST _v_1 ->
                  _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState084
              | BOOL _v_2 ->
                  _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState084
              | END ->
                  let _v_3 = _menhir_action_32 () in
                  _menhir_run_093 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState084
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | PLUS ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_077 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_PUTCHAR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAR ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | SEMI ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              let MenhirCell1_PUTCHAR (_menhir_stack, _menhir_s) = _menhir_stack in
              let e = _v in
              let _v = _menhir_action_21 e in
              _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
          | _ ->
              _eRR ())
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_073 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_RETURN as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_RETURN (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_25 e in
          _menhir_goto_instruction _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_069 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_WHILE as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | STAR ->
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAR ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | BEGIN ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | WHILE ->
                  _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
              | THIS ->
                  _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
              | RETURN ->
                  _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
              | PUTCHAR ->
                  _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
              | NEW ->
                  _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
              | LPAR ->
                  _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
              | IF ->
                  _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState071
              | IDENT _v_0 ->
                  _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState071
              | CST _v_1 ->
                  _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState071
              | BOOL _v_2 ->
                  _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState071
              | END ->
                  let _v_3 = _menhir_action_32 () in
                  _menhir_run_103 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | PLUS ->
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_063 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_NEW, _menhir_box_program) _menhir_cell1_typ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_typ (_menhir_stack, _, ty) = _menhir_stack in
          let MenhirCell1_NEW (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_16 e ty in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_061 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_LPAR as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RPAR ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LPAR (_menhir_stack, _menhir_s) = _menhir_stack in
          let e = _v in
          let _v = _menhir_action_09 e in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_058 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_expression as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | LT | RBRACKET | RPAR | SEMI ->
          let MenhirCell1_expression (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_12 e1 e2 in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_051 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_expression as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | LT | PLUS | RBRACKET | RPAR | SEMI ->
          let MenhirCell1_expression (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_10 e1 e2 in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_048 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_expression as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_expression (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_42 e1 e2 in
          _menhir_goto_mem_access _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_046 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_expression as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA | LT | PLUS | RBRACKET | RPAR | SEMI | STAR ->
          let MenhirCell1_expression (_menhir_stack, _menhir_s, e1) = _menhir_stack in
          let e2 = _v in
          let _v = _menhir_action_11 e1 e2 in
          _menhir_goto_expression _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_044 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | STAR ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_045 _menhir_stack _menhir_lexbuf _menhir_lexer
      | PLUS ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_050 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_057 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LBRACKET ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_047 _menhir_stack _menhir_lexbuf _menhir_lexer
      | DOT ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          _menhir_run_052 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_expression (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState059 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | THIS ->
              _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | NEW ->
              _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LPAR ->
              _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_036 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | CST _v ->
              _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | BOOL _v ->
              _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | RPAR ->
          let x = _v in
          let _v = _menhir_action_49 x in
          _menhir_goto_separated_nonempty_list_COMMA_expression_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_expression_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState059 ->
          _menhir_run_060 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState066 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState054 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState037 ->
          _menhir_run_040 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_060 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_expression -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_expression (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_50 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_expression_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_040 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_39 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_expression__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_expression__ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState066 ->
          _menhir_run_067 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState054 ->
          _menhir_run_055 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState037 ->
          _menhir_run_042 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_015 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | IDENT _v_0 ->
          let _menhir_stack = MenhirCell0_IDENT (_menhir_stack, _v_0) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LPAR ->
              let _menhir_s = MenhirState017 in
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | TYP_VOID ->
                  _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TYP_INT ->
                  _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | TYP_BOOL ->
                  _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | LBRACKET ->
                  _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
              | IDENT _v ->
                  _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | RPAR ->
                  let _v = _menhir_action_40 () in
                  _menhir_goto_loption_separated_nonempty_list_COMMA_typed_ident__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_goto_loption_separated_nonempty_list_COMMA_typed_ident__ : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_typ _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _menhir_stack = MenhirCell1_loption_separated_nonempty_list_COMMA_typed_ident__ (_menhir_stack, _menhir_s, _v) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | BEGIN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | VAR ->
              _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState024
          | BOOL _ | CST _ | END | IDENT _ | IF | LPAR | NEW | PUTCHAR | RETURN | THIS | WHILE ->
              let _v_0 = _menhir_action_36 () in
              _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState024 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_027 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_typ _menhir_cell0_IDENT, _menhir_box_program) _menhir_cell1_loption_separated_nonempty_list_COMMA_typed_ident__ as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_list_variable_decl_ (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | WHILE ->
          _menhir_run_028 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState027
      | THIS ->
          _menhir_run_030 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState027
      | RETURN ->
          _menhir_run_072 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState027
      | PUTCHAR ->
          _menhir_run_075 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState027
      | NEW ->
          _menhir_run_031 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState027
      | LPAR ->
          _menhir_run_035 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState027
      | IF ->
          _menhir_run_080 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState027
      | IDENT _v_0 ->
          _menhir_run_085 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 MenhirState027
      | CST _v_1 ->
          _menhir_run_038 _menhir_stack _menhir_lexbuf _menhir_lexer _v_1 MenhirState027
      | BOOL _v_2 ->
          _menhir_run_039 _menhir_stack _menhir_lexbuf _menhir_lexer _v_2 MenhirState027
      | END ->
          let _v_3 = _menhir_action_32 () in
          _menhir_run_105 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_012 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | IDENT _v_0 ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (id, ty) = (_v_0, _v) in
          let _v = _menhir_action_58 id ty in
          _menhir_goto_typed_ident _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_typed_ident : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState114 ->
          _menhir_run_115 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState019 ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState017 ->
          _menhir_run_018 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState002 ->
          _menhir_run_010 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_115 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_ATTRIBUTE -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_ATTRIBUTE (_menhir_stack, _menhir_s) = _menhir_stack in
          let tid = _v in
          let _v = _menhir_action_01 tid in
          let _menhir_stack = MenhirCell1_attribute_decl (_menhir_stack, _menhir_s, _v) in
          (match (_tok : MenhirBasics.token) with
          | ATTRIBUTE ->
              _menhir_run_114 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState124
          | END | METHOD ->
              let _v_0 = _menhir_action_28 () in
              _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 _tok
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_125 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_attribute_decl -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_attribute_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_29 x xs in
      _menhir_goto_list_attribute_decl_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_list_attribute_decl_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState124 ->
          _menhir_run_125 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | MenhirState113 ->
          _menhir_run_117 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_018 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_typed_ident (_menhir_stack, _menhir_s, _v) in
          let _menhir_s = MenhirState019 in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | TYP_VOID ->
              _menhir_run_003 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TYP_INT ->
              _menhir_run_004 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | TYP_BOOL ->
              _menhir_run_005 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | LBRACKET ->
              _menhir_run_006 _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s
          | IDENT _v ->
              _menhir_run_007 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
          | _ ->
              _eRR ())
      | RPAR ->
          let x = _v in
          let _v = _menhir_action_51 x in
          _menhir_goto_separated_nonempty_list_COMMA_typed_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_typed_ident_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState017 ->
          _menhir_run_021 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | MenhirState019 ->
          _menhir_run_020 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_021 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_typ _menhir_cell0_IDENT as 'stack) -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let x = _v in
      let _v = _menhir_action_41 x in
      _menhir_goto_loption_separated_nonempty_list_COMMA_typed_ident__ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_020 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_typed_ident -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_typed_ident (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_52 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_typed_ident_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_010 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_VAR -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | SEMI ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_VAR (_menhir_stack, _menhir_s) = _menhir_stack in
          let tid = _v in
          let _v = _menhir_action_59 tid in
          _menhir_goto_variable_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_variable_decl : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState131 ->
          _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState000 ->
          _menhir_run_126 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState025 ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState024 ->
          _menhir_run_025 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_126 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let v = _v in
      let _v = _menhir_action_04 v in
      _menhir_goto_decl _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_run_025 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_variable_decl (_menhir_stack, _menhir_s, _v) in
      match (_tok : MenhirBasics.token) with
      | VAR ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState025
      | BOOL _ | CST _ | END | IDENT _ | IF | LPAR | NEW | PUTCHAR | RETURN | THIS | WHILE ->
          let _v_0 = _menhir_action_36 () in
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v_0 _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_026 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_variable_decl -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      let MenhirCell1_variable_decl (_menhir_stack, _menhir_s, x) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_37 x xs in
      _menhir_goto_list_variable_decl_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
  
  and _menhir_goto_list_variable_decl_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState024 ->
          _menhir_run_027 _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | MenhirState025 ->
          _menhir_run_026 _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_008 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_LBRACKET -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _tok ->
      match (_tok : MenhirBasics.token) with
      | RBRACKET ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          let MenhirCell1_LBRACKET (_menhir_stack, _menhir_s) = _menhir_stack in
          let ty = _v in
          let _v = _menhir_action_56 ty in
          _menhir_goto_typ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  let _menhir_run_000 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | VAR ->
          _menhir_run_002 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | FUNCTION ->
          _menhir_run_014 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | CLASS ->
          _menhir_run_108 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState000
      | EOF ->
          let _ = _menhir_action_30 () in
          _menhir_run_128 _menhir_stack
      | _ ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _startpos__1_ = _startpos in
          let _v = _menhir_action_48 _startpos__1_ in
          MenhirBox_program _v
  
end

let program =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_program v = _menhir_run_000 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
