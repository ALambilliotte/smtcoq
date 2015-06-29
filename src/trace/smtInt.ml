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


open SmtForm
open IntAtom
open SmtCertif
open SmtTrace

(* The current strategy:
   - first generate all the tautologies associated to each sub-atom
     involving int63 objects; this gives, in addition to the original
     formula, a bunch of clauses whose sub-formulas are not in CNF
   - then generate the CNF certificate needed both for the original
     formula and for the new clauses
*)

(* TODO:
   - support other integer operations (currently supported: equality)
   - generate only the tautologies needed depending on polarity, and
     remove unused ones
   - support Immediate rules
   - support generation of tautologies "on the fly" (instead of
     everything at the beginning) to have fewer clauses alive at the
     same time (lazy bit-blasting)
*)

module MakeBB = struct

  (* type atom_info = *)
  (*   (\* | Immediate of bool (\\* true if the positive literal is set *\\) *\) *)
  (*   | Done (\* means that the equivalence clauses have been generated *\) *)
  (*   | Todo (\* nothing has been done, process the bit blasting transformation *\) *)

  type atom_form = Atom of hatom | Form of Form.t

  let init_last =
    let last = SmtTrace.mk_scertif Root None in
    SmtTrace.clear ();
    last

  let last = ref init_last

  let not_in_cnf = ref []

  let clear () =
    last := init_last;
    not_in_cnf := []

  let link_Other other cl =
    let c = mkOther other (Some cl) in
    link !last c;
    last := c

  let mkBits rf ra x y =
    let bit i x = Form.get rf (Fatom (Atom.get ra (Auop (UO_index i, x)))) in
    let rec mkBits acc i =
      if i < 0 then acc else
        let f = Form.get rf (Fapp (Fiff, [|bit i x; bit i y|])) in
        mkBits (f::acc) (i-1) in
    mkBits [] 62

  let bb rf ra af =
    let rec bb af =
      (match af with
        (* For formulae, we go done to atoms *)
        | Form l ->
           (match Form.pform l with
	     | Fatom a -> bb (Atom a)
	     | Fapp (_,args) ->
                Array.iter (fun f -> bb (Form f)) args)
        | Atom l ->
           (match Atom.atom l with
             (* For the moment, we just handle equality between integers *)
             | Abop (BO_eq Tint, x, y) ->
                let feq = Form.get rf (Fatom l) in
                let fneq = Form.neg feq in
                let bits = mkBits rf ra x y in
                not_in_cnf := bits@(!not_in_cnf);
                let clDef = feq::(List.map Form.neg bits) in
                link_Other (BuildDefInt (Array.of_list clDef)) clDef;
                List.iteri (fun i beq ->
                  let clProj = [fneq; beq] in
                  link_Other (BuildProjInt (Array.of_list clProj, i)) clProj;
                ) bits;
                bb (Atom x); bb (Atom y)
             | Auop (UO_index i, hh) ->
		(match Atom.atom hh with
		   | Abop (BO_int_xor, x, y) ->
		      let feq = Form.get rf (Fatom l) in
               	      let fneq = Form.neg feq in
		      let bitx = Form.get rf (Fatom (Atom.get ra (Auop (UO_index i, x)))) in
		      let bity = Form.get rf (Fatom (Atom.get ra (Auop (UO_index i, x)))) in
		      let bitxneg = Form.neg bitx in
		      let bityneg = Form.neg bity in
		      let clDef1 = [fneq;bitx;bity] in
		      let clDef2 = [feq;bitxneg;bity] in
		      let clDef3 = [feq;bitx;bityneg] in
		      let clDef4 = [fneq;bitxneg;bityneg] in
	              link_Other (BuildDefInt [|fneq;bitx;bity|]) clDef1;
	              link_Other (BuildDefInt2 [|feq;bitx;bity|]) clDef2;
	              link_Other (BuildDefInt [|feq;bitx;bity|]) clDef3;
	              link_Other (BuildDefInt2 [|fneq;bitx;bity|]) clDef4;
		      bb (Atom x); bb (Atom y)
	           | _ -> bb (Atom hh))
	     (* In the other cases, we just propagate down to the leaves *)
             | Acop _ | Avar _ -> ()
             | Auop (_, x) -> bb (Atom x)
             | Abop (_, x, y) -> bb (Atom x); bb (Atom y))) in

    bb af

  let make_bb rf ra c =
    last := c;
    (match c.value with
      | Some ls -> List.iter (fun l -> not_in_cnf := l::!(not_in_cnf); bb rf ra (Form l)) ls
      | None -> assert false);
    let aux = !last in
    let res = Cnf.make_cnf_list rf aux !not_in_cnf in
    clear ();
    res

end
