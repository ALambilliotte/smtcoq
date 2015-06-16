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


type indexed_type

val dummy_indexed_type: int -> indexed_type
val indexed_type_index : indexed_type -> int

type btype =
  | Tbool
  | Tint

module Btype :
    sig

      val equal : btype -> btype -> bool

      val to_coq : btype -> Term.constr

      val of_coq : Term.constr -> btype

      val interp_to_coq : btype -> Term.constr

    end

(** Operators *)

type cop =
   | CO_int of Structures.int63

type uop =
   | UO_index of int

type bop =
   | BO_int_xor
   | BO_eq of btype

type indexed_op

val dummy_indexed_op: int -> btype -> indexed_op
val indexed_op_index : indexed_op -> int

module Op :
  sig

    type reify_tbl

    val create : unit -> reify_tbl

    val declare : reify_tbl -> Term.constr -> btype -> indexed_op

    val of_coq : reify_tbl -> Term.constr -> indexed_op

    val interp_tbl : Term.constr ->
      (btype -> Term.constr -> Term.constr) ->
      reify_tbl -> Term.constr

    val to_list : reify_tbl -> (int * btype * indexed_op) list

  end


(** Definition of atoms *)

type hatom

type atom =
  | Acop of cop
  | Auop of uop * hatom
  | Abop of bop * hatom * hatom
  | Avar of indexed_op



module Atom :
    sig

      type t = hatom

      val equal : hatom -> hatom -> bool

      val index : hatom -> int

      val atom : hatom -> atom

      val type_of : hatom -> btype

      exception NotWellTyped of atom

      type reify_tbl

      val create : unit -> reify_tbl

      val clear : reify_tbl -> unit

      val get : reify_tbl -> atom -> hatom

      (** Given a coq term, build the corresponding atom *)
      val of_coq : Op.reify_tbl -> reify_tbl ->
        Environ.env -> Evd.evar_map -> Term.constr -> t

      val to_coq : hatom -> Term.constr

      val to_array : reify_tbl -> 'a -> (atom -> 'a) -> 'a array

      val interp_tbl : reify_tbl -> Term.constr

      val interp_to_coq : (int, Term.constr) Hashtbl.t ->
	t -> Term.constr

      (* Generation of atoms *)
      val mk_eq : reify_tbl -> btype -> hatom -> hatom -> hatom

    end


module Form : SmtForm.FORM with type hatom = hatom
module Trace : sig
  val share_prefix : Form.t SmtCertif.clause -> int -> unit
end
module Cnf : sig
  val make_cnf_list : Form.reify -> Form.t SmtCertif.clause -> Form.t list -> Form.t SmtCertif.clause
end
