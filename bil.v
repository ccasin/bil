Require Import Arith.
Require Import Bool.
Require Import List.
Require Import String.

Inductive typ : Set := 
 | typ_imm (sz:nat)            (* immediate of size $sz$ *)
 | typ_mem (sz1:nat) (sz2:nat) (* memory with address size sz1 and element size sz2 *)
.

Inductive cast : Set := 
 | cast_low      : cast (* extract lower bits *)
 | cast_high     : cast (* extract high bits *)
 | cast_signed   : cast (* extend with sign bit *)
 | cast_unsinged : cast (* extend with zero *)
.

Inductive bop : Set := 
 | bop_plus     : bop (* plus *)
 | bop_minus    : bop (* minus *)
 | bop_times    : bop (* times *)
 | bop_divide   : bop (* divide *)
 | bop_sdivide  : bop (* signed divide *)
 | bop_mod      : bop (* modulo *)
 | bop_smod     : bop (* signed modulo *)
 | bop_lshift   : bop (* logical shift left *)
 | bop_rshift   : bop (* logical shift right *)
 | bop_arshift  : bop (* arithmetic shift right *)
 | bop_and      : bop (* bitwise and *)
 | bop_or       : bop (* bitwise or *)
 | bop_xor      : bop (* bitwise xor *)
 | bop_eq       : bop (* equality *)
 | bop_neq      : bop (* non-equality *)
 | bop_lt       : bop (* less than *)
 | bop_le       : bop (* less than or equal *)
 | bop_slt      : bop (* signed less than *)
 | bop_sle      : bop (* signed less than or equal *)
.

Definition var : Set := (nat * typ).

(* First nat is value, second nat is width (in bits).
   To be replaced with better notion of bits, probably from bedrock library. *)
Definition word : Set := (nat * nat).

Inductive endian : Set := 
 | endian_little : endian (* little endian *)
 | endian_big    : endian (* big endian *)
.

Inductive uop : Set := 
 | uop_neg : uop (* unary negation *)
 | uop_not : uop (* bitwise complement *)
.

Inductive exp : Set := 
 | exp_var (x:var)      (* a variable *)
 | exp_imm (w:word)     (* an immediate value *)
 | exp_load (e1:exp) (e2:exp) (endn:endian) (sz:nat)
     (* load a value from address e2 at storage e1 *)
 | exp_store (e1:exp) (e2:exp) (endn:endian) (sz:nat) (e3:exp)
     (* update a storage e1 with binding e2 -> e3 *)
 | exp_binop (e1:exp) (b:bop) (e2:exp)
     (* perform binary operation on e1 and e2 *)
 | exp_unop (u:uop) (e1:exp)
     (* perform an unary operation on e1 *)
 | exp_cast (c:cast) (sz:nat) (e:exp)
     (* extract or extend bitvector e *)
 | exp_let (t:typ) (e1:exp) (e2:exp)
     (* bind e1 in expression e2 *)
 | exp_unk (s:string) (t:typ)
     (* unknown or undefined value of a given type *)
 | exp_ite (e1:exp) (e2:exp) (e3:exp)
     (* evaluates to e2 if e1 is true else to e3 *)
 | exp_ext (loc1:nat) (loc2:nat) (e:exp)
     (* extract or extend bitvector e - take bits from loc1 to loc2 inclusive *)
 | exp_concat (e1:exp) (e2:exp)
     (* concatenate two bitvector $e_1$ to $e_2$ *)
.

Inductive stmt : Set := 
 | stmt_move (x:var) (e:exp) (* assign e to x *)
 | stmt_jump (e:exp)         (* transfer control to a given address e *)
 | stmt_cpuexn (n:nat)       (* interrupt CPU witth a given interrupt n *)
 | stmt_special (s:string)   (* instruction with unknown semantics *)
 | stmt_while (e:exp) (seq:list stmt)   (* eval seq while e is true *)
 | stmt_ifthen (e:exp) (seq:list stmt)  (* eval seq if e is true *)
 | stmt_if (e:exp) (seq1:list stmt) (seq2:list stmt)
     (* if e is true then eval seq1 else seq2 *)
.

Definition stmts : Set := list stmt.

Definition delta : Set := list (typ * exp).

Inductive instruction : Set := 
 | insn (addr:word) (sz:word) (seq:stmts)
.

Inductive val : exp -> Prop :=
 | val_imm : forall (w:word), val (exp_imm w)
 | val_store : forall e1 e2 endn sz e3,
        val e1 -> val e2 -> val e3
        -> val (exp_store e1 e2 endn sz e3)
 | val_unk : forall s t, val (exp_unk s t)
.

(* defns typing_exp *)
Inductive typ_exp : exp -> typ -> Prop :=    (* defn typ_exp *)
 | etyp_var : forall (n:nat) (t:typ),
     typ_exp (exp_var (n,t)) t
 | etyp_int : forall (val sz:nat),
     typ_exp (exp_imm (val,sz)) (typ_imm sz)
 | etyp_load : forall (e1 e2:exp) (endn:endian) (sz_addr sz_el:nat),
     typ_exp e1 (typ_mem sz_addr sz_el) ->
     typ_exp e2 (typ_imm sz_addr) ->
     typ_exp (exp_load e1 e2 endn sz_el) (typ_imm sz_el)
 | etyp_store : forall (e1 e2:exp) (endn:endian) (sz_addr sz_el:nat) (e3:exp),
     typ_exp e1 (typ_mem sz_addr sz_el) ->
     typ_exp e2 (typ_imm sz_addr) ->
     typ_exp e3 (typ_imm sz_el) ->
     typ_exp (exp_store e1 e2 endn sz_el e3) (typ_mem sz_addr sz_el)
 | etyp_bop : forall (e1:exp) (b:bop) (e2:exp) (sz:nat),
     typ_exp e1 (typ_imm sz) ->
     typ_exp e2 (typ_imm sz) ->
     typ_exp (exp_binop e1 b e2) (typ_imm sz)
 | etyp_uop : forall (u:uop) (e1:exp) (sz:nat),
     typ_exp e1 (typ_imm sz) ->
     typ_exp (exp_unop u e1) (typ_imm sz)
 | etyp_cast : forall (cst:cast) (sz sz':nat) (e:exp),
     typ_exp e (typ_imm sz) ->
     typ_exp (exp_cast cst sz' e) (typ_imm sz')
 | etyp_let : forall (e1 e2:exp) (t' t:typ),
     typ_exp e1 t ->
     typ_exp e2 t' ->
     typ_exp (exp_let t e1 e2) t'
 | etyp_unknown : forall (str:string) (t:typ),
     typ_exp (exp_unk str t) t
 | etyp_ite : forall (e1 e2 e3:exp) (t:typ),
     typ_exp e1 (typ_imm 1) ->
     typ_exp e2 t ->
     typ_exp e3 t ->
     typ_exp (exp_ite e1 e2 e3) t
 | etyp_extract : forall (sz sz1 sz2:nat) (e:exp),
     typ_exp e (typ_imm sz) ->
     (sz1 >= sz2)  ->
     typ_exp (exp_ext sz1 sz2 e) (typ_imm ((sz1 - sz2) + 1))
 | etyp_concat : forall (e1 e2:exp) (sz1 sz2:nat),
     typ_exp e1 (typ_imm sz1) ->
     typ_exp e2 (typ_imm sz2) ->
     typ_exp (exp_concat e1 e2) (typ_imm (sz1 + sz2))
.

Inductive typ_delta : delta -> Prop :=
 | dtyp_nil  : typ_delta nil
 | dtyp_cons : forall t e d,
     val e ->
     typ_exp e t ->
     typ_delta d ->
     typ_delta ((t,e)::d).

Inductive typ_stmt : stmt -> Prop :=
 | styp_move : forall (x:var) (e:exp) (t:typ),
     typ_exp (exp_var x) t ->
     typ_exp e t ->
     typ_stmt (stmt_move x e)
 | styp_jmp : forall (e:exp) (sz:nat),
     typ_exp e (typ_imm sz) ->
     typ_stmt (stmt_jump e)
 | styp_cpuexn : forall (n:nat),
     typ_stmt (stmt_cpuexn n)
 | styp_special : forall (str:string),
     typ_stmt (stmt_special str)
 | styp_while : forall (e:exp) (seq:stmts),
     typ_exp e (typ_imm 1) ->
     Forall typ_stmt seq ->
     typ_stmt (stmt_while e seq)
 | styp_ifthen : forall (e:exp) (seq:stmts),
     typ_exp e (typ_imm 1) ->
     Forall typ_stmt seq ->
     typ_stmt (stmt_ifthen e seq)
 | styp_if : forall (e:exp) (seq1 seq2:stmts),
     typ_exp e (typ_imm 1) ->
     Forall typ_stmt seq1 ->
     Forall typ_stmt seq2 ->
     typ_stmt (stmt_if e seq1 seq2)
.

(* For now we comment out iterated statement execution, which requires a clearer notion of decode. *)
(*
Inductive step : delta -> word -> var -> delta -> word -> var -> Prop :=    (* defn step *)
 | step : forall (delta5:delta) (w:word) (var5:var) (delta':delta) (w3 w1:word) (bil5:bil) (w2:word),
     is_delta_of_delta delta5 ->
     is_delta_of_delta delta' ->
     decode (insn_insn w1 bil5) ->
     seq delta5  w1  +  w2  bil5 delta' w3 (seq_many Nil_list_stmt) ->
     step delta5 w var5 delta' w3 var5
with decode : insn -> Prop :=    (* defn decode *)
 | decode : forall (insn5:insn),
     decode insn5.
 *)

Definition succ (w : word) :=
  let (val,sz) := w in (val+1,sz).

Inductive step_exp : delta -> exp -> exp -> Prop :=
 | estep_var_in : forall (d:delta) (n : nat) (t t' : typ) (v:exp),
     nth_error d n = Some (t',v) ->
     step_exp d (exp_var (n,t)) v
 | estep_var_unknown : forall (d:delta) (n : nat) (t : typ),
     nth_error d n = None -> 
     step_exp d (exp_var  (n, t)) (exp_unk "unbound variable" t)
 | estep_load_step_addr : forall (d:delta) (e1 e2:exp) (endn:endian) (sz:nat) (e2':exp),
     step_exp d e2 e2' ->
     step_exp d (exp_load e1 e2 endn sz) (exp_load e1 e2' endn sz)
 | estep_load_step_mem : forall (d:delta) (e1 v2:exp) (endn:endian) (sz:nat) (e1':exp),
     val v2 ->
     step_exp d e1 e1' ->
     step_exp d (exp_load e1 v2 endn sz) (exp_load e1' v2 endn sz)
 | estep_load_byte : forall (d:delta) (v1:exp) (w_addr:word) (endn endn':endian) (data : nat),
     val v1 ->
     step_exp d (exp_load (exp_store v1 (exp_imm w_addr) endn 8 (exp_imm (data,8)))
                          (exp_imm w_addr) endn' 8)
                (exp_imm (data,8))
 | estep_load_un_addr : forall (d:delta) (v1:exp) (str:string) (t:typ) (endn:endian) (v2 v3:exp),
     val v1 ->
     val v2 ->
     val v3 ->
     step_exp d (exp_load ((exp_store v1 (exp_unk str t) endn 8 v2)) v3 endn 8)
                (exp_unk str (typ_imm 8))
 | estep_load_rec : forall (d:delta) (v1:exp) (w1 w2:word) (endn:endian) (v3:exp),
     val v1 ->
     val v3 ->
     w1 <> w2 ->
     step_exp d (exp_load ((exp_store v1 (exp_imm w1) endn 8 v3))
                          (exp_imm w2) endn 8)
                (exp_load v1 (exp_imm w2) endn 8)
 | estep_load_un_mem : forall (d:delta) (str:string) (t : typ) (v3:exp) (endn:endian) (sz:nat),
     val v3 ->
     step_exp d (exp_load (exp_unk str t) v3 endn sz) (exp_unk str (typ_imm sz))
.
 | load_word_be : forall (d:delta) (v:exp) (w:word) (sz:nat) (w':word),
     is_delta_of_delta d ->
     val v ->
     succ w (exp_imm w') ->
     step_exp d (exp_load v (exp_imm w) endian_big sz) (exp_concat (exp_load v (exp_imm w) endian_big  8 )  ( (exp_load v (exp_imm w') endian_big  (  sz  -   8   ) ) ) )
 | load_word_el : forall (d:delta) (v:exp) (w:word) (sz:nat) (w':word),
     is_delta_of_delta d ->
     val v ->
     succ w (exp_imm w') ->
     step_exp d (exp_load v (exp_imm w) endian_little sz) (exp_concat (exp_load v (exp_imm w') endian_little  (  sz  -   8   ) )  ( (exp_load v (exp_imm w) endian_big  8 ) ) )
 | store_step_val : forall (d:delta) (e1 e2:exp) (endn:endian) (sz:nat) (e3 e3':exp),
     is_delta_of_delta d ->
     step_exp d e3 e3' ->
     step_exp d (exp_store e1 e2 endn sz e3) (exp_store e1 e2 endn sz e3')
 | store_step_addr : forall (d:delta) (e1 e2:exp) (endn:endian) (sz:nat) (v3 e2':exp),
     is_delta_of_delta d ->
     val v3 ->
     step_exp d e2 e2' ->
     step_exp d (exp_store e1 e2 endn sz v3) (exp_store e1 e2' endn sz v3)
 | store_step_mem : forall (d:delta) (e1 v2:exp) (endn:endian) (sz:nat) (v3 e1':exp),
     is_delta_of_delta d ->
     val v2 ->
     val v3 ->
     step_exp d e1 e1' ->
     step_exp d (exp_store e1 v2 endn sz v3) (exp_store e1' v2 endn sz v3)
 | store_word_be : forall (d:delta) (v:exp) (w:word) (sz:nat) (val5 e1:exp) (w':word),
     is_delta_of_delta d ->
     val v ->
     val val5 ->
     succ w (exp_imm w') ->
      let  e1  =   ( (exp_store v (exp_imm w) endian_big  8  (exp_cast cast_high  8  val5)) )   in  ->
     step_exp d (exp_store v (exp_imm w) endian_big sz val5) (exp_store e1 (exp_imm w') endian_big  (  sz  -   8   )  (exp_cast cast_low  (  sz  -   8   )  val5))
 | store_word_el : forall (d:delta) (v:exp) (w:word) (sz:nat) (val5 e1:exp) (w':word),
     is_delta_of_delta d ->
     val v ->
     val val5 ->
     succ w (exp_imm w') ->
      let  e1  =   ( (exp_store v (exp_imm w) endian_little  8  (exp_cast cast_low  8  val5)) )   in  ->
     step_exp d (exp_store v (exp_imm w) endian_little sz val5) (exp_store e1 (exp_imm w') endian_little  (  sz  -   8   )  (exp_cast cast_high  (  sz  -   8   )  val5))
 | let_step : forall (d:delta) (var5:var) (e1 e2 e1':exp),
     is_delta_of_delta d ->
     step_exp d e1 e1' ->
     step_exp d (exp_let var5 e1 e2) (exp_let var5 e1' e2)
 | let : forall (d:delta) (var5:var) (v e:exp),
     is_delta_of_delta d ->
     val v ->
     step_exp d (exp_let var5 v e)  subst_exp_exp  v   var5   e 
 | ite_step : forall (d:delta) (e1 e2 e3 e1':exp),
     is_delta_of_delta d ->
     step_exp d e1 e1' ->
     step_exp d (exp_ite e1 e2 e3) (exp_ite e1' e2 e3)
 | ite_true : forall (d:delta) (e2 e3:exp),
     is_delta_of_delta d ->
     step_exp d (exp_ite (exp_imm  1 ) e2 e3) e2
 | ite_false : forall (d:delta) (e2 e3:exp),
     is_delta_of_delta d ->
     step_exp d (exp_ite (exp_imm  0 ) e2 e3) e3
 | bop_rhs : forall (d:delta) (e1:exp) (bop5:bop) (e2 e2':exp),
     is_delta_of_delta d ->
     step_exp d e2 e2' ->
     step_exp d (exp_binop e1 bop5 e2) (exp_binop e1 bop5 e2')
 | bop_lhs : forall (d:delta) (e1:exp) (bop5:bop) (v2 e1':exp),
     is_delta_of_delta d ->
     val v2 ->
     step_exp d e1 e1' ->
     step_exp d (exp_binop e1 bop5 v2) (exp_binop e1' bop5 v2)
 | bop_unk_rhs : forall (d:delta) (e:exp) (bop5:bop) (str:string) (t:typ),
     is_delta_of_delta d ->
     step_exp d (exp_binop e bop5 (exp_unk str t)) (exp_unk str t)
 | bop_unk_lhs : forall (d:delta) (str:string) (t:typ) (bop5:bop) (e:exp),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_unk str t) bop5 e) (exp_unk str t)
 | plus : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_plus (exp_imm w2)) (exp_imm  w1  +  w2 )
 | minus : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_minus (exp_imm w2)) (exp_imm  w1  -  w2 )
 | times : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_times (exp_imm w2)) (exp_imm  w1  *  w2 )
 | div : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_divide (exp_imm w2)) (exp_imm  div  w1   w2 )
 | sdiv : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_sdivide (exp_imm w2)) (exp_imm  undefined_word )
 | mod : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_mod (exp_imm w2)) (exp_imm  w1  mod  w2 )
 | smod : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_smod (exp_imm w2)) (exp_imm  undefined_word )
 | lsl : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_lshift (exp_imm w2)) (exp_imm  w1  * (2 ^  w2 ) )
 | lsr : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_rshift (exp_imm w2)) (exp_imm  w1  / (2 ^  w2 ) )
 | asr : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_arshift (exp_imm w2)) (exp_imm  undefined_word )
 | land : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_and (exp_imm w2)) (exp_imm  undefined_word )
 | lor : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_or (exp_imm w2)) (exp_imm  undefined_word )
 | xor : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_xor (exp_imm w2)) (exp_imm  undefined_word )
 | eq : forall (d:delta) (w:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w) binop_eq (exp_imm w)) (exp_imm  1 )
 | neq : forall (d:delta) (w:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w) binop_neq (exp_imm w)) (exp_imm  0 )
 | less : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_lt (exp_imm w2)) (exp_imm  undefined_word )
 | less_eq : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_le (exp_imm w2)) (exp_binop  ( (exp_binop (exp_imm w1) binop_lt (exp_imm w2)) )  binop_or  ( (exp_binop (exp_imm w1) binop_eq (exp_imm w2)) ) )
 | signed_less : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_slt (exp_imm w2)) (exp_imm  undefined_word )
 | signed_less_eq : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_binop (exp_imm w1) binop_sle (exp_imm w2)) (exp_binop  ( (exp_binop (exp_imm w1) binop_eq (exp_imm w2)) )  binop_and  ( (exp_binop (exp_imm w1) binop_slt (exp_imm w2)) ) )
 | uop : forall (d:delta) (uop5:uop) (e e':exp),
     is_delta_of_delta d ->
     step_exp d e e' ->
     step_exp d (exp_unop uop5 e) (exp_unop uop5 e')
 | not_true : forall (d:delta),
     is_delta_of_delta d ->
     step_exp d (exp_unop unop_not (exp_imm  1 )) (exp_imm  0 )
 | not_false : forall (d:delta),
     is_delta_of_delta d ->
     step_exp d (exp_unop unop_not (exp_imm  0 )) (exp_imm  1 )
 | concat_rhs : forall (d:delta) (e1 e2 e2':exp),
     is_delta_of_delta d ->
     step_exp d e2 e2' ->
     step_exp d (exp_concat e1 e2) (exp_concat e1 e2')
 | concat_lhs : forall (d:delta) (e1 v2 e1':exp),
     is_delta_of_delta d ->
     val v2 ->
     step_exp d e1 e1' ->
     step_exp d (exp_concat e1 v2) (exp_concat e1' v2)
 | concat_lhs_un : forall (d:delta) (str:string) (t:typ) (v2:exp),
     is_delta_of_delta d ->
     val v2 ->
     step_exp d (exp_concat (exp_unk str t) v2) (exp_unk str t)
 | concat_rhs_un : forall (d:delta) (v1:exp) (str:string) (t:typ),
     is_delta_of_delta d ->
     val v1 ->
     step_exp d (exp_concat v1 (exp_unk str t)) (exp_unk str t)
 | concat : forall (d:delta) (w1 w2:word),
     is_delta_of_delta d ->
     step_exp d (exp_concat (exp_imm w1) (exp_imm w2)) (exp_imm  undefined_word )
 | extract_reduce : forall (d:delta) (sz1 sz2:nat) (e e':exp),
     is_delta_of_delta d ->
     step_exp d e e' ->
     step_exp d (exp_ext sz1 sz2 e) (exp_ext sz1 sz2 e')
 | extract_un : forall (d:delta) (sz1 sz2:nat) (str:string) (t:typ),
     is_delta_of_delta d ->
     step_exp d (exp_ext sz1 sz2 (exp_unk str t)) (exp_unk str t)
 | extract : forall (d:delta) (sz1 sz2:nat) (w:word),
     is_delta_of_delta d ->
     step_exp d (exp_ext sz1 sz2 (exp_imm w)) (exp_imm  undefined_word )
 | cast_reduce : forall (d:delta) (cast5:cast) (sz:nat) (e e':exp),
     is_delta_of_delta d ->
     step_exp d e e' ->
     step_exp d (exp_cast cast5 sz e) (exp_cast cast5 sz e')
 | cast_low : forall (d:delta) (sz:nat) (w:word),
     is_delta_of_delta d ->
     step_exp d (exp_cast cast_low sz (exp_imm w)) (exp_imm  undefined_word )
 | cast_high : forall (d:delta) (sz:nat) (num5:num) (sz':nat),
     is_delta_of_delta d ->
     step_exp d (exp_cast cast_high sz (exp_imm  num5 )) (exp_imm  undefined_word )
 | cast_signed : forall (d:delta) (sz:nat) (w:word),
     is_delta_of_delta d ->
     step_exp d (exp_cast cast_signed sz (exp_imm w)) (exp_imm  undefined_word )
 | cast_unsigned : forall (d:delta) (sz:nat) (w:word),
     is_delta_of_delta d ->
     step_exp d (exp_cast cast_unsinged sz (exp_imm w)) (exp_cast cast_low sz (exp_imm w)).
(** definitions *)

(* defns reduce_stmt *)
Inductive stmt : delta -> word -> stmt -> delta -> word -> Prop :=    (* defn stmt *)
 | move : forall (d:delta) (w:word) (var5:var) (e v:exp),
     is_delta_of_delta d ->
     val v ->
     mexp d e v ->
     stmt d w (stmt_move var5 e) (delta_cons d var5 v) w
 | jmp : forall (d:delta) (w:word) (e:exp) (w':word),
     is_delta_of_delta d ->
     mexp d e (exp_imm w') ->
     stmt d w (stmt_jump e) d w'
 | cpuexn : forall (d:delta) (w:word) (num5:num),
     is_delta_of_delta d ->
     stmt d w (stmt_cpuexn num5) d w
 | special : forall (d:delta) (w:word) (str:string),
     is_delta_of_delta d ->
     stmt d w (stmt_special str) d w
 | ifthen_true : forall (d:delta) (word5:word) (e:exp) (seq:bil) (delta':delta) (word':word),
     is_delta_of_delta d ->
     is_delta_of_delta delta' ->
     mexp d e (exp_imm  1 ) ->
     seq d word5 seq delta' word' (seq_many Nil_list_stmt) ->
     stmt d word5 (stmt_ifthen e seq) delta' word'
 | if_true : forall (d:delta) (word5:word) (e:exp) (seq seq1:bil) (delta':delta) (word':word),
     is_delta_of_delta d ->
     is_delta_of_delta delta' ->
     mexp d e (exp_imm  1 ) ->
     seq d word5 seq delta' word' (seq_many Nil_list_stmt) ->
     stmt d word5 (stmt_if e seq seq1) delta' word'
 | if_false : forall (d:delta) (word5:word) (e:exp) (seq1 seq:bil) (delta':delta) (word':word),
     is_delta_of_delta d ->
     is_delta_of_delta delta' ->
     mexp d e (exp_imm  0 ) ->
     seq d word5 seq delta' word' (seq_many Nil_list_stmt) ->
     stmt d word5 (stmt_if e seq1 seq) delta' word'
 | while : forall (delta1:delta) (word1:word) (e:exp) (seq:bil) (delta3:delta) (word3:word) (delta2:delta) (word2:word),
     is_delta_of_delta delta1 ->
     is_delta_of_delta delta3 ->
     is_delta_of_delta delta2 ->
     mexp delta1 e (exp_imm  1 ) ->
     seq delta1 word1 seq delta2 word2 (seq_many Nil_list_stmt) ->
     stmt delta2 word2 (stmt_while e seq) delta3 word3 ->
     stmt delta1 word1 (stmt_while e seq) delta3 word3
 | while_false : forall (d:delta) (word5:word) (e:exp) (seq:bil),
     is_delta_of_delta d ->
     mexp d e (exp_imm  0 ) ->
     stmt d word5 (stmt_while e seq) d word5
with seq : delta -> word -> bil -> delta -> word -> bil -> Prop :=    (* defn seq *)
 | seq_rec : forall (s_list:list_stmt) (UNK: NUM 1:UNK_CTP) (d:delta) (word5:word) (delta':delta) (word':word) (t103 t104:stmt),
          nth_list_stmt (1 - 2) s_list = Some t103 ->
     nth_list_stmt (1 - 2) s_list = Some t104 ->
is_delta_of_delta d ->
     is_delta_of_delta delta' ->
     stmt d word5 t103 delta' word' ->
     seq d word5 (seq_many ((app_list_stmt (Cons_list_stmt t104 Nil_list_stmt) (app_list_stmt s_list Nil_list_stmt)))) delta' word' (seq_many s_list)
 | seq_last : forall (d:delta) (word5:word) (s1 s2:stmt) (delta':delta) (word':word),
     is_delta_of_delta d ->
     is_delta_of_delta delta' ->
     stmt d word5 s1 delta' word' ->
     seq d word5 (seq_many ((app_list_stmt (Cons_list_stmt s1 Nil_list_stmt) (app_list_stmt (Cons_list_stmt s2 Nil_list_stmt) Nil_list_stmt)))) delta' word' (seq_many (Cons_list_stmt s2 Nil_list_stmt))
 | seq_one : forall (d:delta) (word5:word) (s1:stmt) (delta':delta) (word':word),
     is_delta_of_delta d ->
     is_delta_of_delta delta' ->
     stmt d word5 s1 delta' word' ->
     seq d word5 (seq_many (Cons_list_stmt s1 Nil_list_stmt)) delta' word' (seq_many Nil_list_stmt)
 | seq_nil : forall (d:delta) (word5:word),
     is_delta_of_delta d ->
     seq d word5 (seq_many Nil_list_stmt) d word5 (seq_many Nil_list_stmt).
(** definitions *)

(* defns multistep_exp *)
Inductive mexp : delta -> exp -> exp -> Prop :=    (* defn mexp *)
 | refl : forall (d:delta) (e:exp),
     is_delta_of_delta d ->
     mexp d e e
 | reduce : forall (d:delta) (e1 e3 e2:exp),
     is_delta_of_delta d ->
     step_exp d e1 e2 ->
     mexp d e2 e3 ->
     mexp d e1 e3.


