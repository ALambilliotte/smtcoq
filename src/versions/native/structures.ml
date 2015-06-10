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


open Entries
open Coqlib



let gen_constant modules constant = lazy (gen_constant_in_modules "SMT" modules constant)



(* Int63 *)
let int63_modules = [["Coq";"Numbers";"Cyclic";"Int63";"Int63Native"];["Coq";"Numbers";"Cyclic";"Int63";"Int63Op"]]

type int63 = Uint63.t
let mkInt : int -> Term.constr =
  fun i -> Term.mkInt (Uint63.of_int i)
let mkInt63 : int63 -> Term.constr = Term.mkInt
let isInt : Term.constr -> bool = Term.isInt
let destInt : Term.constr -> int =
  fun t -> Uint63.to_int (Term.destInt t)
let destInt63 : Term.constr -> int63 = Term.destInt

let cint = gen_constant int63_modules "int"

(* PArray *)
let parray_modules = [["Coq";"Array";"PArray"]]

let max_array_size : int =
  Parray.trunc_size (Uint63.of_int 4194303)
let mkArray : Term.types * Term.constr array -> Term.constr =
  Term.mkArray


(* Differences between the two versions of Coq *)
let dummy_loc = Pp.dummy_loc

let mkConst c =
  { const_entry_body = c;
    const_entry_type = None;
    const_entry_secctx = None;
    const_entry_opaque = false;
    const_entry_inline_code = false}

let glob_term_CbvVm = Glob_term.CbvVm None

let error = Errors.error
