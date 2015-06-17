(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Michaël Armand                                                     *)
(*     Benjamin Grégoire                                                  *)
(*     Chantal Keller                                                     *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab                  *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open SmtMisc
open CoqTerms

(** Syntaxified version of Coq type *)
type indexed_type = Term.constr gen_hashed

let dummy_indexed_type i = {index = i; hval = Term.mkProp}
let indexed_type_index i = i.index

type btype =
  | Tbool
  | Tint

module Btype =
  struct

    let equal t1 t2 = t1 == t2

    let to_coq = function
      | Tbool -> Lazy.force cTbool
      | Tint -> Lazy.force cTint

    let of_coq t =
      if t = Lazy.force cint then Tint
      else if t = Lazy.force cbool then Tbool
      else failwith "The decision procedure for machine integers does not handle other types than bool and int"

    let interp_to_coq = function
      | Tbool -> Lazy.force cbool
      | Tint -> Lazy.force cint

  end

(** Operators *)

type cop =
   | CO_int of Structures.int63

type uop =
   | UO_index of int

type bop =
   | BO_int_xor
   | BO_eq of btype

type op_def = {
    tres : btype;
    op_val : Term.constr }

type indexed_op = op_def gen_hashed

let dummy_indexed_op i codom = {index = i; hval = {tres = codom; op_val = Term.mkProp}}
let indexed_op_index op = op.index

type op =
  | Cop of cop
  | Uop of uop
  | Bop of bop
  | Iop of indexed_op

module Op =
  struct
    let c_to_coq = function
      | CO_int i -> mklApp cCO_int [|Structures.mkInt63 i|]

    let c_type_of = function
      | CO_int _ -> Tint

    let interp_cop = function
      | CO_int i -> Structures.mkInt63 i

    let u_to_coq = function
      | UO_index i -> mklApp cUO_index [|Structures.mkInt i|]

    let u_type_of = function
      | UO_index _ -> Tbool

    let u_type_arg = function
      | UO_index _ -> Tint

    let interp_uop = function
      | UO_index i -> mklApp cbit_rev [|Structures.mkInt i|]

    let eq_tbl = Hashtbl.create 17

    let eq_to_coq t =
      try Hashtbl.find eq_tbl t
      with Not_found ->
	let op = mklApp cBO_eq [|Btype.to_coq t|] in
	Hashtbl.add eq_tbl t op;
	op

    let b_to_coq = function
      | BO_int_xor -> Lazy.force cBO_int_xor
      | BO_eq t -> eq_to_coq t

    let b_type_of = function
      | BO_eq _ -> Tbool
      | BO_int_xor -> Tint

    let b_type_args = function
      | BO_eq t -> (t,t)
      | BO_int_xor -> (Tint, Tint)

    let interp_eq = function
      | Tbool -> Lazy.force ceqb
      | Tint -> Lazy.force ceq63

    let interp_bop = function
      | BO_int_xor -> Lazy.force clxor
      | BO_eq t -> interp_eq t

    let i_to_coq i = mkInt i.index

    let i_type_of i = i.hval.tres

    (* reify table *)
    type reify_tbl =
        { mutable count : int;
	          tbl : (Term.constr, indexed_op) Hashtbl.t
	}

    let create () =
      { count = 0;
	tbl =  Hashtbl.create 17 }

    let declare reify op tres =
      assert (not (Hashtbl.mem reify.tbl op));
      let v = { tres = tres; op_val = op } in
      let res = {index = reify.count; hval = v } in
      Hashtbl.add reify.tbl op res;
      reify.count <- reify.count + 1;
      res

    let of_coq reify op =
      Hashtbl.find reify.tbl op

    let interp_tbl tval mk_Tval reify =
      let t = Array.make (reify.count + 1)
	  (mk_Tval Tbool (Lazy.force ctrue))  in
      let set _ v =
	t.(v.index) <- mk_Tval v.hval.tres v.hval.op_val in
      Hashtbl.iter set reify.tbl;
      Structures.mkArray (tval, t)

    let to_list reify =
      let set _ op acc =
        let value = op.hval in
        (op.index,value.tres,op)::acc in
      Hashtbl.fold set reify.tbl []

    let c_equal op1 op2 = op1 == op2

    let u_equal op1 op2 = op1 == op2

    let b_equal op1 op2 =
      match op1,op2 with
        | BO_eq t1, BO_eq t2 -> Btype.equal t1 t2
        | _ -> op1 == op2

    let i_equal op1 op2 = op1.index == op2.index

  end


(** Definition of atoms *)

type atom =
  | Acop of cop
  | Auop of uop * hatom
  | Abop of bop * hatom * hatom
  | Avar of indexed_op

and hatom = atom gen_hashed


module HashedAtom =
  struct
    type t = atom

    let equal a b =
      match a, b with
      | Acop opa, Acop opb -> Op.c_equal opa opb
      | Auop(opa,ha), Auop(opb,hb) -> Op.u_equal opa opb && ha.index == hb.index
      | Abop(opa,ha1,ha2), Abop(opb,hb1,hb2) ->
	  Op.b_equal opa opb && ha1.index == hb1.index && ha2.index == hb2.index
      | Avar va, Avar vb -> Op.i_equal va vb
      | _, _ -> false

    let hash = function
      |	Acop op -> ((Hashtbl.hash op) lsl 3) lxor 1
      | Auop (op,h) ->
          (( (h.index lsl 3) + (Hashtbl.hash op)) lsl 3) lxor 2
      | Abop (op,h1,h2) ->
          (((( (h1.index lsl 2) + h2.index) lsl 3) + Hashtbl.hash op) lsl 3) lxor 3
      | Avar op -> op.index lxor 4

  end

module HashAtom = Hashtbl.Make(HashedAtom)

module Atom =
  struct

    type t = hatom

    let atom h = h.hval
    let index h = h.index


    let equal h1 h2 = h1.index == h2.index

    let type_of h =
      match h.hval with
      | Acop op -> Op.c_type_of op
      | Auop (op,_) -> Op.u_type_of op
      | Abop (op,_,_) -> Op.b_type_of op
      | Avar op -> Op.i_type_of op

    let is_bool_type h = Btype.equal (type_of h) Tbool

    exception NotWellTyped of atom

    let check a =
      match a with
      | Acop _ -> ()
      | Auop(op,h) ->
	  if not (Btype.equal (Op.u_type_arg op) (type_of h)) then
	    raise (NotWellTyped a)
      | Abop(op,h1,h2) ->
	  let (t1,t2) = Op.b_type_args op in
	  if not (Btype.equal t1 (type_of h1) && Btype.equal t2 (type_of h2))
	  then raise (NotWellTyped a)
      | Avar op -> ()

    type reify_tbl =
        { mutable count : int;
	          tbl : hatom HashAtom.t
	}

    let create () =
      { count = 0;
	tbl =  HashAtom.create 17 }

    let clear reify =
      reify.count <- 0;
      HashAtom.clear reify.tbl

    let declare reify a =
      check a;
      let res = {index = reify.count; hval = a} in
      HashAtom.add reify.tbl a res;
      reify.count <- reify.count + 1;
      res

    let get reify a =
      try HashAtom.find reify.tbl a
      with Not_found -> declare reify a


    (** Given a coq term, build the corresponding atom *)
    type coq_cst =
      | CCbit
      | CClxor
      | CCeqb
      | CCunknown

    let op_tbl () =
      let tbl = Hashtbl.create 3 in
      let add (c1,c2) = Hashtbl.add tbl (Lazy.force c1) c2 in
      List.iter add
	[ cbit, CCbit;
          clxor, CClxor;
          ceqb,CCeqb
        ];
      tbl

    let op_tbl = lazy (op_tbl ())

    let of_coq ro reify env sigma c =
      let op_tbl = Lazy.force op_tbl in
      let get_cst c =
	try Hashtbl.find op_tbl c with Not_found -> CCunknown in
      let mk_cop op = get reify (Acop op) in
      let rec mk_hatom h =
        if Structures.isInt h then mk_cop (CO_int (mk_int63 h)) else
	let c, args = Term.decompose_app h in
	match get_cst c with
          | CCbit ->
             (match args with
               | [x;i] -> mk_uop (UO_index (mk_int i)) [x]
               | _ -> assert false)
          | CClxor -> mk_bop BO_int_xor args
          | CCeqb -> mk_bop (BO_eq Tbool) args
	  | CCunknown -> mk_unknown h (Retyping.get_type_of env sigma h)

      and mk_uop op = function
        | [a] -> let h = mk_hatom a in get reify (Auop (op,h))
        | _ -> assert false

      and mk_bop op = function
        | [a1;a2] ->
          let h1 = mk_hatom a1 in
          let h2 = mk_hatom a2 in
          get reify (Abop (op,h1,h2))
        | _ -> assert false

      and mk_int   i = assert (Structures.isInt i); Structures.destInt   i
      and mk_int63 i = assert (Structures.isInt i); Structures.destInt63 i

      and mk_unknown c ty =
        let op =
          try Op.of_coq ro c
          with | Not_found ->
            let tres = Btype.of_coq ty in
            Op.declare ro c tres in
        get reify (Avar op) in

       mk_hatom c


    let to_coq h = mkInt h.index

    let a_to_coq a =
      match a with
      | Acop op -> mklApp cAcop [|Op.c_to_coq op|]
      | Auop (op,h) -> mklApp cAuop [|Op.u_to_coq op; to_coq h|]
      | Abop (op,h1,h2) ->
	  mklApp cAbop [|Op.b_to_coq op;to_coq h1; to_coq h2|]
      | Avar op ->
        let cop = Op.i_to_coq op in
        let cargs = mklApp cnil [|Lazy.force cint|] in
        mklApp cAapp [|cop; cargs|]

    let dft_atom = lazy (mklApp cAcop [| mklApp cCO_int [|Structures.mkInt 0|] |])

    let to_array reify dft f =
      let t = Array.make (reify.count + 1) dft in
      let set _ h = t.(h.index) <- f h.hval in
      HashAtom.iter set reify.tbl;
      t

    let interp_tbl reify =
      let t = to_array reify (Lazy.force dft_atom) a_to_coq in
      Structures.mkArray (Lazy.force catom, t)


    (** Producing a Coq term corresponding to the interpretation of an atom *)
    let interp_to_coq atom_tbl a =
      let rec interp_atom a =
	let l = index a in
	try Hashtbl.find atom_tbl l
	with Not_found ->
	  let pc =
	    match atom a with
              | Acop c -> Op.interp_cop c
              | Auop (op,h) -> Term.mkApp (Op.interp_uop op, [|interp_atom h|])
              | Abop (op,h1,h2) -> Term.mkApp (Op.interp_bop op, [|interp_atom h1; interp_atom h2|])
              | Avar op -> op.hval.op_val in
	  Hashtbl.add atom_tbl l pc;
	  pc in
      interp_atom a


    (* Generation of atoms *)

    let mk_binop op reify h1 h2 = get reify (Abop (op, h1, h2))

    let mk_unop op reify h = get reify (Auop (op, h))

    let mk_eq reify ty h1 h2 =
      let op = BO_eq ty in
      try
        HashAtom.find reify.tbl (Abop (op, h1, h2))
      with
        | Not_found ->
          try
            HashAtom.find reify.tbl (Abop (op, h2, h1))
          with
            | Not_found ->
              declare reify (Abop (op, h1, h2))

  end


module Form = SmtForm.Make(Atom)
module Trace = SmtTrace.MakeOpt(Form)
module Cnf = SmtCnf.MakeCnf(Form)
