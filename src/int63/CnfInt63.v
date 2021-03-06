(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2015                                          *)
(*                                                                        *)
(*     Antonin Lambilliotte                                               *)
(*                                                                        *)
(*     Inria - École Polytechnique - MSR-Inria Joint Lab - ÉNS de Lyon    *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Require Import Bool.
Require Import List.
Require Import Int63.
Require Import PArray.
Require Import BoolEq.
Require Import NZParity.

Add LoadPath ".." as SMTCoq.

Require Import Misc State.
Require Import SMT_terms.


Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.



Section Checker.

  Import Atom.


  Variable t_form : PArray.array form.
  Variable t_atom : PArray.array atom.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).

  Variable s : S.t.



(* * and_neg          : {(and a_1 a2) (not a_1) (not a_2)}
     * or_pos           : {(not (or a_1 a_2)) a_1 a_n} 
     * xor_pos1         : {(not (xor a b)) a b}
     * xor_neg1         : {(xor a b) a (not b)} *)

  Definition check_BuildDefInt lits :=
    let n := PArray.length lits in
    match get_form (Lit.blit (lits.[0])) with
    | Fatom a => 
      match get_atom a with
      | Abop b h1 h2 => 
        match (b) with
        | (BO_eq Typ.Tint) => 
          let test_correct i0 l :=
            if i0 == 0
            then Lit.is_pos l
            else (
              match get_form (Lit.blit l) with
              | Fiff l1 l2 =>
                match (get_form (Lit.blit l1),get_form (Lit.blit l2)) with
                | (Fatom a1,Fatom a2) =>
                  match (get_atom a1,get_atom a2) with
                  | (Auop (UO_index j) h1',Auop (UO_index k) h2') => (Lit.is_pos l1)&&(Lit.is_pos l2)&&(negb (Lit.is_pos l))&&(j == i0-1)&&(k == j)&&(h1 == h1')&&(h2'==h2)
                  | _ => false
                  end
                | _ => false
                end
              | _ => false
              end
                 )
          in
          if (n == Int63Op.digits + 1)&&(Lit.is_pos (lits.[0]))&&forallbi (fun i6 l => test_correct i6 l) lits
          then PArray.to_list lits
          else C._true
        | _ => C._true
        end
      | Auop (UO_index i1) hh =>
        match get_atom hh with
        | Acop (CO_int i) => 
          if Lit.is_pos (lits.[0])
          then (
            if (bit_rev i1 i)
            then (lits.[0])::nil
            else (Lit.neg (lits.[0]))::nil
               )
          else C._true
        | Abop b h1 h2 =>
          match (b) with
          | (BO_int_xor) =>
            if n == 3
            then (
              match (get_form (Lit.blit (lits.[1])),get_form (Lit.blit (lits.[2]))) with
              | (Fatom a1,Fatom a2) =>
                match (get_atom a1,get_atom a2) with
                | (Auop (UO_index i2) h1', Auop (UO_index i3) h2') => 
                  if (h1' == h1)&&(h2 == h2')&&(i1 ==i2)&&(i2 == i3)&&(Lit.is_pos (lits.[1]))&&(Lit.is_pos (lits.[2]))
                  then (
                    if (Lit.is_pos (lits.[0]))
                    then lits.[0]::lits.[1]::(Lit.neg (lits.[2]))::nil
                    else lits.[0]::lits.[1]::lits.[2]::nil
                       )
                  else C._true   
                | _ => C._true
                end
              | _ => C._true
              end
                 )
            else C._true
          | (BO_int_and) =>
            if n == 3
            then (
              match (get_form (Lit.blit (lits.[1])),get_form (Lit.blit (lits.[2]))) with
              | (Fatom a1,Fatom a2) =>
                match (get_atom a1,get_atom a2) with
                | (Auop (UO_index i2) h1', Auop (UO_index i3) h2') => 
                  if (h1' == h1)&&(h2 == h2')&&(i1 ==i2)&&(i2 == i3)&&(negb (Lit.is_pos (lits.[1])))&&(negb(Lit.is_pos (lits.[2])))
                  then (
                    if (Lit.is_pos (lits.[0]))
                    then lits.[0]::lits.[1]::lits.[2]::nil
                    else C._true
                       )
                  else C._true   
                | _ => C._true
                end
              | _ => C._true
              end
                 )
            else C._true
          | (BO_int_or) =>
            if n == 3
            then (
              match (get_form (Lit.blit (lits.[1])),get_form (Lit.blit (lits.[2]))) with
              | (Fatom a1,Fatom a2) =>
                match (get_atom a1,get_atom a2) with
                | (Auop (UO_index i2) h1', Auop (UO_index i3) h2') => 
                  if (h1' == h1)&&(h2 == h2')&&(i1 ==i2)&&(i2 == i3)&&(Lit.is_pos (lits.[1]))&&(Lit.is_pos (lits.[2]))
                  then (
                    if (Lit.is_pos (lits.[0]))
                    then C._true
                    else lits.[0]::lits.[1]::lits.[2]::nil
                       )
                  else C._true   
                | _ => C._true
                end
              | _ => C._true
              end
                 )
            else C._true
          | _ => C._true
          end
        | _ => C._true
        end
      | _ => C._true
      end
   | _ => C._true
   end
   .
   
   (* * xor_pos2          : {(not (xor a b)) (not a) (not b)}
     * xor_neg2          : {(xor a b) (not a) b} *)
    Definition check_BuildDefInt2 lits :=
    let n := PArray.length lits in
    match get_form (Lit.blit (lits.[0])) with
    | Fatom a => 
      match get_atom a with
      | Auop (UO_index i1) hxor =>
        match get_atom hxor with
        | Abop b h1 h2 =>
          match (b) with
          | (BO_int_xor) =>
            if n == 3
            then (
              match (get_form (Lit.blit (lits.[1])),get_form (Lit.blit (lits.[2]))) with
              | (Fatom a1,Fatom a2) =>
                match (get_atom a1,get_atom a2) with
                | (Auop (UO_index i2) h1', Auop (UO_index i3) h2') => 
                  if (h1' == h1)&&(h2 == h2')&&(i1 ==i2)&&(i2 == i3)&&(Lit.is_pos (lits.[1]))&&(Lit.is_pos (lits.[2]))
                  then (
                    if (Lit.is_pos (lits.[0]))
                    then lits.[0]::(Lit.neg (lits.[1]))::lits.[2]::nil
                    else lits.[0]::(Lit.neg (lits.[1]))::(Lit.neg (lits.[2]))::nil
                       )
                  else C._true   
                | _ => C._true
                end
              | _ => C._true
              end
                 )
            else C._true
          | _ => C._true
          end
        | _ => C._true
        end
      | _ => C._true
      end
   | _ => C._true
   end.


(* * or_neg           : {(or a_1 a_2) (not a_i)}
     * and_pos          : {(not (and a_1 a_2)) a_i} 
*)

  Definition check_BuildProjInt lits i :=
    let n := PArray.length lits in
    match get_form (Lit.blit (lits.[0])) with
    | Fatom a => 
      match get_atom a with
      | Abop b h1 h2 => 
        match (b) with
        | (BO_eq Typ.Tint) => 
          let test_correct i0 l :=
            match get_form (Lit.blit l) with
            | Fiff l1 l2 =>
              match (get_form (Lit.blit l1),get_form (Lit.blit l2)) with
              | (Fatom a1,Fatom a2) =>
                match (get_atom a1,get_atom a2) with
                | (Auop (UO_index j) h1',Auop (UO_index k) h2') => (n == Int63Op.digits + 1)&&(i < Int63Op.digits)&&(Lit.is_pos l1)&&(Lit.is_pos l2)&&(negb (Lit.is_pos (lits.[0])))&&(Lit.is_pos l)&&(j == i0)&&(k == j)&&(h1 == h1')&&(h2'==h2)
                | _ => false
                end
              | _ => false
              end
            | _ => false
            end            
          in
          if test_correct i (lits.[i+1]) 
          then (lits.[i+1])::(lits.[0])::nil
          else C._true
        | _ => C._true
        end
      | Auop (UO_index i1) hh =>
        match get_atom hh with
        | Abop b h1 h2 =>
          match (b) with
          | (BO_int_or) =>
            if (n == 3)&&(i < 2)
            then (
              match get_form (Lit.blit (lits.[i+1])) with
              | Fatom a0 =>
                match get_atom a0 with
                | Auop (UO_index i2) h0 => 
                  if ((h0 == h1)||(h2 == h0))&&(i1 ==i2)&&(negb (Lit.is_pos (lits.[i+1])))
                  then (
                    if (Lit.is_pos (lits.[0]))
                    then lits.[0]::lits.[i+1]::nil
                    else C._true
                       )
                  else C._true   
                | _ => C._true
                end
              | _ => C._true
              end
                 )
            else C._true
          | (BO_int_and) =>
            if (n == 3)&&(i < 2)
            then (
              match get_form (Lit.blit (lits.[i+1])) with
              | Fatom a0 =>
                match get_atom a0 with
                | Auop (UO_index i2) h0 => 
                  if ((h0 == h1)||(h2 == h0))&&(i1 ==i2)&&(Lit.is_pos (lits.[i+1]))
                  then (
                    if (Lit.is_pos (lits.[0]))
                    then C._true
                    else lits.[0]::lits.[i+1]::nil
                       )
                  else C._true   
                | _ => C._true
                end
              | _ => C._true
              end
                 )
            else C._true
          | _ => C._true
          end
        | _ => C._true
        end
      | _ => C._true
      end
    | _ => C._true
    end.

  Section Proof.
    
    Variables (t_i : array typ_eqb)
              (t_func : array (Atom.tval t_i))
              (ch_atom : Atom.check_atom t_atom)
              (ch_form : Form.check_form t_form)
              (wt_t_atom : Atom.wt t_i t_func t_atom).

    Local Notation check_atom :=
      (check_aux t_i t_func (get_type t_i t_func t_atom)).

    Local Notation interp_form_hatom :=
      (Atom.interp_form_hatom t_i t_func t_atom).

    Local Notation rho :=
      (Form.interp_state_var interp_form_hatom t_form).

    Local Notation t_interp := (t_interp t_i t_func t_atom).

    Local Notation interp_atom :=   
      (interp_aux t_i t_func (get t_interp)).

    Let wf_t_atom : Atom.wf t_atom.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_atom : default t_atom = Atom.Acop Atom.CO_xH.
    Proof. destruct (Atom.check_atom_correct _ ch_atom); auto. Qed.

    Let def_t_form : default t_form = Form.Ftrue.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom _ ch_form) as [H _]; destruct H; auto.
    Qed.

    Let wf_t_form : Form.wf t_form.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom _ ch_form) as [H _]; destruct H; auto.
    Qed.

    Let wf_rho : Valuation.wf rho.
    Proof.
      destruct (Form.check_form_correct interp_form_hatom _ ch_form); auto.
    Qed.

    Lemma lit_interp_true : Lit.interp rho Lit._true = true.
    Proof.
      apply Lit.interp_true.
      apply wf_rho.
    Qed.


    Let rho_interp : forall x : int, rho x = Form.interp interp_form_hatom t_form (t_form.[ x]).
    Proof.
      destruct (check_form_correct interp_form_hatom _ ch_form) as ((H,H0), _).
      intros x;apply wf_interp_form;trivial.
    Qed.

    Lemma bool_impl : forall a b, (b = true -> a = true) -> a = true \/ b = false.
    Proof.
      intros;destruct a;
      [(left;trivial) | (right;destruct b;[(symmetry;apply H;trivial) | trivial])].
    Qed.

    Lemma lit_interp_impl : forall a b rho,(Lit.interp rho b = true -> Lit.interp rho a = true) -> (Lit.interp rho a =true \/Lit.interp rho (Lit.neg b) = true).
    Proof.
      intros;rewrite (Lit.interp_neg rho b);rewrite negb_true_iff;apply bool_impl;apply H.
    Qed.
    

    Lemma valid_check_BuildProjInt : forall lits i, C.valid rho (check_BuildProjInt lits i).
    Proof.
      unfold wt, is_true in wt_t_atom; rewrite forallbi_spec in wt_t_atom;
      unfold check_BuildProjInt,C.valid; intros lits i.

      case_eq (t_form.[Lit.blit (lits.[0])]);[intros a H|intro H|intro H|intros z1 z2 H|intros z1 H|intros z1 H|intros z1 H|intros z1 z2 H|intros z1 z2 H|intros z1 z2 z3 H]; auto using C.interp_true;
      case_eq (t_atom.[a]);[intros z1 H1|intros u hh H1|intros b h1 h2 H1|intros z1 z2 H1|intros z1 z2 H1]; auto using C.interp_true.
      
      (*bitwise operators*)
      case_eq u;intro i1;auto using C.interp_true;intro H2;
      case_eq (t_atom .[ hh]);[intros z1 H3|intros z1 z2 H3|intros b h1 h2 H3|intros no ah H3|intros z1 z2 H3];auto using C.interp_true;
      case_eq b;intro H5;auto using C.interp_true;
      assert (H100: hh < length t_atom) by (apply PArray.get_not_default_lt; rewrite H3, def_t_atom; discriminate);
      generalize (wt_t_atom _ H100); rewrite H3, H5; simpl;
      rewrite !andb_true_iff; intros [[_ H101] H102]; change (is_true (Typ.eqb (get_type' t_i t_interp h1) Typ.Tint)) in H101; change (is_true (Typ.eqb (get_type' t_i t_interp h2) Typ.Tint)) in H102; rewrite Typ.eqb_spec in H101; rewrite Typ.eqb_spec in H102;
      unfold get_type' in H101; rewrite t_interp_wf in H101; auto;
      unfold get_type' in H102; rewrite t_interp_wf in H102; auto;
      case_eq ((length lits == 3) && (i < 2));intro H6;auto using C.interp_true; rewrite andb_true_iff in H6;destruct H6 as (H6,H7);
      case_eq (t_form.[Lit.blit (lits.[i+1])]);[intros a0 H8|intros|intros|intros|intros|intros|intros|intros|intros|intros|intros a0 H8|intros|intros|intros|intros|intros|intros|intros|intros|intros]; auto using C.interp_true;
      case_eq (t_atom.[a0]);[intros|intros u0 h0 H9|intros|intros|intros|intros|intros u0 h0 H9|intros|intros|intros]; auto using C.interp_true;
      case_eq u0;intro i2;auto using C.interp_true;intro H10;
      [case_eq (((h0 == h1) || (h2 == h0)) && (i1 == i2) && negb (Lit.is_pos (lits .[ i + 1])))|case_eq (((h0 == h1) || (h2 == h0)) && (i1 == i2) && Lit.is_pos (lits .[ i + 1]))];intro H11;auto using C.interp_true;rewrite !andb_true_iff in H11;destruct H11 as (H11,H12);destruct H11 as (H11,H13);
      case_eq (Lit.is_pos (lits .[ 0]));intro H14;auto using C.interp_true;
      rewrite orb_true_iff in H11;destruct H11;
      rewrite Int63Properties.eqb_spec in H0;rewrite Int63Properties.eqb_spec in H13;subst i2;subst h0;rewrite <- H2 in H10;subst u0; [rewrite negb_true_iff in H12|rewrite negb_true_iff in H12| | ];
      unfold C.interp;simpl;rewrite orb_true_iff;rewrite orb_false_r;simpl; unfold Lit.interp;rewrite H12;rewrite H14; unfold Var.interp; rewrite !rho_interp; rewrite H;rewrite H8; simpl; unfold Atom.interp_form_hatom;unfold interp_hatom; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom); rewrite H1;rewrite H9; simpl; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom); simpl; rewrite H3; simpl; unfold interp_uop;unfold interp_bop; rewrite H2;rewrite H5; simpl; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);simpl; unfold apply_unop;unfold apply_binop;
      case_eq (interp_atom (t_atom.[h1])); intros t1 v1 H15;
      rewrite H15 in H101; simpl in H101; subst t1;
      case_eq (interp_atom (t_atom.[h2])); intros t2 v2 H16;
      rewrite H16 in H102; simpl in H102; subst t2;
      rewrite Typ.cast_refl;
      simpl; unfold bit_rev;simpl; [rewrite lor_spec|rewrite lor_spec|rewrite land_spec|rewrite land_spec]; rewrite negb_true_iff;
      [rewrite orb_true_iff|rewrite orb_true_iff|rewrite andb_false_iff|rewrite andb_false_iff];
      [case_eq (bit v1 i1);intro H00; [left;left|right]|case_eq (bit v2 i1);intro H00; [left;right|right]|case_eq (bit v1 i1);intro H00; [right|left;left]|case_eq (bit v2 i1);intro H00; [right|left;right]];trivial.


      (*equality*)
      case_eq b; intro t; auto using C.interp_true;intro H3;
      
      assert (H100: a < length t_atom) by (apply PArray.get_not_default_lt; rewrite H1, def_t_atom; discriminate);
      generalize (wt_t_atom _ H100); rewrite H1, H3; simpl;
      rewrite !andb_true_iff; intros [[_ H101] H102]; change (is_true (Typ.eqb (get_type' t_i t_interp h1) t)) in H101; change (is_true (Typ.eqb (get_type' t_i t_interp h2) t)) in H102; rewrite Typ.eqb_spec in H101; rewrite Typ.eqb_spec in H102;
      unfold get_type' in H101; rewrite t_interp_wf in H101; auto;
      unfold get_type' in H102; rewrite t_interp_wf in H102; auto;

      case_eq t;intro H04;auto using C.interp_true; rewrite H04 in H101;rewrite H04 in H102;subst t;
      case_eq (t_form.[Lit.blit (lits.[i+1])]);[intros z1 H4|intros H4|intros H4|intros z1 z2 H4|intros z1 H4|intros z1 H4|intros z1 H4|intros z1 z2 H4|intros l1 l2 H4|intros z1 z2 z3 H4];auto using C.interp_true;
      case_eq (t_form.[Lit.blit l1]);[intros a1 H8|intros H8|intros H8|intros z1 z2 H8|intros z1 H8|intros z1 H8|intros z1 H8|intros z1 z2 H8|intros z1 z2 H8|intros z1 z2 z3 H8];auto using C.interp_true;
      case_eq (t_form.[Lit.blit l2]);[intros a2 H9|intros H9|intros H9|intros z1 z2 H9|intros z1 H9|intros z1 H9|intros z1 H9|intros z1 z2 H9|intros z1 z2 H9|intros z1 z2 z3 H9];auto using C.interp_true;
      case_eq (t_atom.[a1]);[intros z1 H5|intros u1 h1' H5|intros z1 z2 z3 H5|intros z1 z2 H5|intros z1 z2 H5];auto using C.interp_true;
      case_eq u1; intro j; auto using C.interp_true;intro H6;
      case_eq (t_atom.[a2]);[intros z1 H7|intros u2 h2' H7|intros z1 z2 z3 H7|intros z1 z2 H7|intros z1 z2 H7];auto using C.interp_true;
      case_eq u2; intro k; auto using C.interp_true;intro H10;

      case_eq ((length lits == digits + 1) && (i < digits) && Lit.is_pos l1 && Lit.is_pos l2 && negb (Lit.is_pos (lits .[ 0])) && Lit.is_pos (lits .[ i + 1]) && (j == i) && (k == j) && (h1 == h1') &&(h2' == h2));intro H17;auto using C.interp_true;
      apply andb_true_iff in H17; destruct H17 as (H17,H18); apply andb_true_iff in H17; destruct H17 as (H17,H19); apply andb_true_iff in H17; destruct H17 as (H17,H20); apply andb_true_iff in H17; destruct H17 as (H17,H21); apply andb_true_iff in H17; destruct H17 as (H17,H22); apply andb_true_iff in H17; destruct H17 as (H17,H23); apply andb_true_iff in H17; destruct H17 as (H17,H24); apply andb_true_iff in H17; destruct H17 as (H17,H25); apply andb_true_iff in H17; destruct H17 as (H17,H26);
     
      rewrite Int63Properties.eqb_spec in H19; rewrite Int63Properties.eqb_spec in H20; rewrite Int63Properties.eqb_spec in H21; rewrite Int63Properties.eqb_spec in H18;rewrite Int63Properties.eqb_spec in H17;subst h1'; subst h2'; subst j; subst k;
      rewrite <- H6 in H10;subst u2;
      rewrite negb_true_iff in H23;
      
      simpl; rewrite orb_false_r; apply orb_true_iff;
      unfold Lit.interp; rewrite H22; rewrite H23; rewrite negb_true_iff; unfold Var.interp; rewrite !rho_interp; rewrite H4; rewrite H;
      simpl; unfold Lit.interp; rewrite H25; rewrite H24; unfold Var.interp; rewrite !rho_interp; rewrite H8; rewrite H9;simpl;
      unfold Atom.interp_form_hatom; unfold interp_hatom; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      rewrite H5; rewrite H7;rewrite H1; simpl; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      unfold interp_uop; unfold interp_bop; rewrite H6;rewrite H3; simpl; unfold apply_binop;unfold apply_unop;
      
      case_eq (interp_atom (t_atom.[h1])); intros t1 v1 H15;
      rewrite H15 in H101; simpl in H101; subst t1;
      case_eq (interp_atom (t_atom.[h2])); intros t2 v2 H16;
      rewrite H16 in H102; simpl in H102; subst t2;
      rewrite Typ.cast_refl;

      simpl;apply bool_impl; intro H28; apply Int63Properties.eqb_spec in H28;rewrite H28; apply Bool.eqb_true_iff; trivial.
    Qed.

    Lemma digit_plus_1_not_0 : (0 == digits+1) = false.
    Proof.
      reflexivity.
    Qed.

   Lemma digit_plus_1_not_02 : (digits+1 == 0) = false.
    Proof.
      reflexivity.
    Qed.

    Lemma contrap : forall a b, (a = true -> b = true) <-> (b = false -> a = false).
    Proof.
      intros [ | ] [ | ];split; intros H H0; try (symmetry; apply H);trivial;apply H0.
    Qed.


    Lemma forallb_existsb f from to :
      Int63Op.forallb f from to =
        negb (Int63Op.existsb (fun i => negb (f i)) from to).
    Proof.
      unfold Int63Op.forallb, Int63Op.existsb.
      apply (foldi_cont_ind2 _ _ _ _ (fun x y => x tt = negb (y tt))); auto.
      intros i c1 c2 H1 H2 H3. case (f i); simpl; auto.
    Qed.


    Lemma bit_eq_false i1 i2: i1 <> i2 -> exists i, bit i1 i <> bit i2 i /\ i < digits = true.
    Proof.
      intro H;rewrite bit_eq in H.
      Search (bool -> bool -> bool).
      assert (H': ~ (forall i, 0 <= i = true -> i <= max_int = true -> Bool.eqb (bit i1 i) (bit i2 i) = true)).
        intro H'.
        apply H. intro i.
        assert (H1:=leb_0 i). assert (H2:=leb_max_int i).
        specialize (H' _ H1 H2). apply eqb_prop in H'. auto.
      rewrite <- Int63Properties.forallb_spec in H'.
      rewrite forallb_existsb in H'.
      case_eq (Int63Op.existsb (fun i => negb (Bool.eqb (bit i1 i) (bit i2 i))) 0 max_int); intro Heq; rewrite Heq in H'; simpl in H';
        [ |elim H'; reflexivity].
      rewrite Int63Properties.existsb_spec in Heq.
      destruct Heq as [x Heq].
      rewrite !andb_true_iff in Heq. destruct Heq as [[H1 H2] H3].
      exists x. split.
      - intro H4. rewrite H4, eqb_reflx in H3. discriminate.
      - assert (H10: digits <= x = true -> (Bool.eqb (bit i1 x) (bit i2 x) = true)).
          intros H12;rewrite !bit_M;simpl;trivial;apply H12.
        assert (H20: Bool.eqb (bit i1 x) (bit i2 x) = false) by (generalize H3; case (Bool.eqb (bit i1 x) (bit i2 x)); auto). clear H3.
        apply contrap in H10; auto.
        apply negb_true_iff in H10;rewrite <- H10;rewrite <- ltb_negb_geb;trivial.
    Qed. 
    
    Lemma inf_plus_un : forall a b, (b < max_int) = true -> (a < b) = true -> (a + 1 < b + 1) = true.
    Proof.
      intros a b H1 H2.
      rewrite ltb_leb_sub1.
      generalize H2.
      rewrite <- (ltb_leb_add1 (b +1 -1) b a).
      intro H.
      assert (b = b+1-1).
      rewrite <- to_Z_eq.
      rewrite (to_Z_sub_1 (b+1) 0).
      rewrite (to_Z_add_1 b max_int).
      intuition.
      apply H1.
      apply succ_max_int;apply H1.
      rewrite <- H0;apply H.
      apply H2.
      apply not_0_ltb;apply succ_max_int;apply H1.
    Qed.

    Lemma valid_check_BuildDefInt : forall lits, C.valid rho (check_BuildDefInt lits).
    Proof.
      unfold wt,is_true in wt_t_atom; rewrite forallbi_spec in wt_t_atom;
      unfold check_BuildDefInt,C.valid; intros lits.
      
      case_eq (t_form .[ Lit.blit (lits .[ 0])]); [intros a H|intro H|intro H|intros z1 z2 H|intros z1 H|intros z1 H|intros z1 H|intros z1 z2 H|intros z1 z2 H|intros z1 z2 z3 H]; auto using C.interp_true;
      case_eq (t_atom.[a]);[intros z1 H0|intros u hh H0|intros u h1 h2 H0|intros z1 z2 H0|intros z1 z2 H0]; auto using C.interp_true.
      
      (*First the different cases for equality*)
      case_eq u;intro i1;auto using C.interp_true; intro H1;
      case_eq (t_atom.[hh]);[intros c H2|intros z1 z2 H2|intros b h1 h2 H2|intros n ah H2|intros z1 z2 H2];auto using C.interp_true.
      (*Case of the constants*)
      case_eq c; intro i;auto using C.interp_true;intro H3;
      case_eq (Lit.is_pos (lits .[ 0])); intro H4;auto using C.interp_true;
      case_eq (bit_rev i1 i);intro H5;simpl; 
      rewrite orb_false_r;unfold Lit.interp; [rewrite H4|rewrite Lit.is_pos_neg; rewrite H4]; unfold Var.interp; rewrite rho_interp;[simpl|simpl;rewrite Lit.blit_neg]; rewrite H;simpl; unfold Atom.interp_form_hatom; unfold interp_hatom;  rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom); rewrite H0; simpl; unfold interp_uop; rewrite H1; unfold bit_rev; rewrite t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom); rewrite H2; simpl; unfold interp_cop; rewrite H3; simpl; [apply H5|rewrite negb_true_iff; apply H5].
      
      (*bitwise operations*)
      case_eq b; intro H3;auto using C.interp_true;
      case_eq (length lits == 3); intros H4; auto using C.interp_true;
      case_eq (t_form .[ Lit.blit (lits .[ 1])]);[intros a1 H5|intros|intros|intros|intros|intros|intros|intros|intros|intros|intros a1 H5|intros|intros|intros|intros|intros|intros|intros|intros|intros|intros a1 H5|intros|intros|intros|intros|intros|intros|intros|intros|intros]; auto using C.interp_true;
      case_eq (t_form .[ Lit.blit (lits .[ 2])]);[intros a2 H6|intros|intros|intros|intros|intros|intros|intros|intros|intros|intros a2 H6|intros|intros|intros|intros|intros|intros|intros|intros|intros|intros a2 H6|intros|intros|intros|intros|intros|intros|intros|intros|intros]; auto using C.interp_true;
      case_eq (t_atom .[ a1]);[intros|intros c1 h1' H7|intros|intros|intros|intros|intros c1 h1' H7|intros|intros|intros|intros|intros c1 h1' H7|intros|intros|intros]; auto using C.interp_true;
      case_eq c1;intro i2;auto using C.interp_true; intro H8;
      case_eq (t_atom .[ a2]);[intros|intros c2 h2' H9|intros|intros|intros|intros|intros c2 h2' H9|intros|intros|intros|intros|intros c2 h2' H9|intros|intros|intros]; auto using C.interp_true;
      case_eq c2;intro i3;auto using C.interp_true;intro H10;
      [case_eq ((h1' == h1) && (h2 == h2') && (i1 == i2) && (i2 == i3) && Lit.is_pos (lits .[ 1]) && Lit.is_pos (lits .[ 2]))|case_eq ((h1' == h1) && (h2 == h2') && (i1 == i2) && (i2 == i3) && Lit.is_pos (lits .[ 1]) && Lit.is_pos (lits .[ 2]))|case_eq ((h1' == h1) && (h2 == h2') && (i1 == i2) && (i2 == i3) && negb (Lit.is_pos (lits .[ 1])) && negb (Lit.is_pos (lits .[ 2])))]; auto using C.interp_true;intros H23;
      rewrite !andb_true_iff in H23; destruct H23 as (H23,H31);destruct H23 as (H23,H26); destruct H23 as (H23,H27); destruct H23 as (H23,H29); destruct H23 as (H23,H30);
      apply Int63Properties.eqb_spec in H23;apply Int63Properties.eqb_spec in H27;apply Int63Properties.eqb_spec in H29;apply Int63Properties.eqb_spec in H30; subst h1';subst h2';subst i2;subst i3; rewrite <- H1 in H10;rewrite <- H1 in H8; subst c1; subst c2;
      assert (H100: hh < length t_atom) by (apply PArray.get_not_default_lt; rewrite H2, def_t_atom; discriminate);
      generalize (wt_t_atom _ H100); rewrite H2, H3; simpl;
      rewrite !andb_true_iff; intros [[_ H101] H102]; change (is_true (Typ.eqb (get_type' t_i t_interp h1) Typ.Tint)) in H101; change (is_true (Typ.eqb (get_type' t_i t_interp h2) Typ.Tint)) in H102; rewrite Typ.eqb_spec in H101; rewrite Typ.eqb_spec in H102;
      unfold get_type' in H101; rewrite t_interp_wf in H101; auto;
      unfold get_type' in H102; rewrite t_interp_wf in H102; auto;
      case_eq (Lit.is_pos (lits.[0]));intro H14;auto using C.interp_true;
      simpl; rewrite orb_false_r;rewrite !orb_true_iff;
      unfold Lit.interp;[rewrite Lit.is_pos_neg| | |rewrite negb_true_iff in H26;rewrite negb_true_iff in H31]; rewrite H26,H14,H31;simpl;unfold Var.interp; rewrite !rho_interp; [rewrite Lit.blit_neg| | | ]; rewrite H,H5,H6; simpl;unfold Atom.interp_form_hatom; unfold interp_hatom; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      rewrite H0,H7,H9; simpl; unfold interp_uop; rewrite H1; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      rewrite H2; simpl; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      unfold interp_bop; rewrite H3;simpl; unfold apply_binop;
      case_eq (interp_atom (t_atom.[h1])); intros t1' v1 H32;
      rewrite H32 in H101; simpl in H101; subst t1';
      case_eq (interp_atom (t_atom.[h2])); intros t2' v2 H33;
      rewrite H33 in H102; simpl in H102; subst t2';
      rewrite Typ.cast_refl;
      simpl;unfold bit_rev;[rewrite lxor_spec|rewrite lxor_spec|rewrite lor_spec|rewrite land_spec];destruct (bit v1 i1);destruct (bit v2 i1);[right;left|left|left|right;right|left|right;left|right;right|left|right;left|right;left|right;right|left|left|right;right|right;left|right;left];trivial.

      (*equality*)
      case_eq (u);[intros|intros|intros|intros|intros|intros|intros|intros|intros|intros|intros t H1]; auto using C.interp_true;
      case_eq t;[intros|intro|intro|intro|intro H2];auto using C.interp_true; subst t;
      case_eq ((length lits == digits + 1) && Lit.is_pos (lits .[ 0]) && forallbi (fun i6 l : int => if i6 == 0 then Lit.is_pos l else match t_form .[ Lit.blit l] with | Fiff l1 l2 => match t_form .[ Lit.blit l1] with | Fatom a1 => match t_form .[ Lit.blit l2] with | Fatom a2 => match t_atom .[ a1] with | Auop (UO_index j) h1' => match t_atom .[ a2] with | Auop (UO_index k) h2' => Lit.is_pos l1 && Lit.is_pos l2 && negb (Lit.is_pos l) && (j == i6 - 1) && (k == j) && (h1 == h1') && (h2' == h2) | _ => false end | _ => false end | _ => false end | _ => false end | _ => false end) lits );intros H6; auto using C.interp_true;
      apply andb_true_iff in H6; destruct H6 as (H6,H7);apply andb_true_iff in H6; destruct H6 as (H6,H9);

      rewrite forallbi_spec in H7; unfold C.interp;apply existsb_exists;
      
      assert (H100: a < length t_atom) by (apply PArray.get_not_default_lt; rewrite H0, def_t_atom; discriminate);
      generalize (wt_t_atom _ H100); rewrite H0, H1; simpl;
      rewrite !andb_true_iff; intros [[_ H101] H102]; change (is_true (Typ.eqb (get_type' t_i t_interp h1) Typ.Tint)) in H101; change (is_true (Typ.eqb (get_type' t_i t_interp h2) Typ.Tint)) in H102; rewrite Typ.eqb_spec in H101; rewrite Typ.eqb_spec in H102;
      unfold get_type' in H101; rewrite t_interp_wf in H101; auto;
      unfold get_type' in H102; rewrite t_interp_wf in H102; auto;

      case_eq (interp_atom (t_atom.[h1])); intros t1' v1 H32;
      rewrite H32 in H101; simpl in H101; subst t1';
      case_eq (interp_atom (t_atom.[h2])); intros t2' v2 H33;
      rewrite H33 in H102; simpl in H102; subst t2';
      
      case_eq ( v1 == v2);intro H8.
      rewrite Int63Properties.eqb_spec in H8;rewrite Int63Properties.eqb_spec in H6;

      exists (lits.[0]);split;
      [apply to_list_In;rewrite H6;reflexivity
      |unfold Lit.interp; rewrite H9; unfold Var.interp; rewrite rho_interp; rewrite H; simpl;unfold Atom.interp_form_hatom; unfold interp_hatom; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);   
      rewrite H0; simpl; unfold interp_bop; rewrite H1; simpl; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      unfold apply_binop;rewrite H32;rewrite H33;simpl; apply Int63Properties.eqb_spec;apply H8].

      apply Int63Properties.eqb_spec in H6; apply Int63Properties.eqb_false_spec in H8; apply bit_eq_false in H8; inversion H8; destruct H2 as (H10,H11); clear H8;
      exists (lits.[x+1]);split;
      [apply (to_list_In lits (x+1));rewrite H6; rewrite inf_plus_un; trivial; reflexivity;  apply H11
      
      |assert (H12 := H7 (x+1));rewrite H6 in H12; rewrite inf_plus_un in H12;clear H7;try reflexivity; try (apply H11);
      assert (( if x + 1 == 0 then Lit.is_pos (lits .[ x + 1]) else match t_form .[ Lit.blit (lits .[ x + 1])] with | Fiff l1 l2 => match t_form .[ Lit.blit l1] with | Fatom a1 => match t_form .[ Lit.blit l2] with | Fatom a2 => match t_atom .[ a1] with | Auop (UO_index j) h1' => match t_atom .[ a2] with  | Auop (UO_index k) h2' => Lit.is_pos l1 && Lit.is_pos l2 && negb (Lit.is_pos (lits .[ x + 1])) && (j == x + 1 - 1) && (k == j) && (h1 == h1') && (h2' == h2) | _ => false end | _ => false end | _ => false end  | _ => false end | _ => false end) = true) as H2 by (apply H12;trivial); 
      clear H12; assert (H12:=H2); clear H2;
      assert (x + 1 == 0 = false) as H7 by (apply eqb_false_spec; apply not_0_ltb; apply succ_max_int;apply (ltb_trans x digits max_int); try (apply H11); try reflexivity); rewrite H7 in H12;
      case_eq (t_form .[ Lit.blit (lits .[ x + 1])]); [intros i02 H2|intro H2|intro H2|intros i02 i03 H2|intros i02 H2|intros i02 H2| intros i02 H2| intros i02 i03 H2|intros l1 l2 H2|intros i02 i3 i4 H2]; rewrite H2 in H12; try (apply diff_false_true in H12; inversion H12);
      case_eq (t_form .[ Lit.blit l1]); [intros a1 H3|intros H3|intro H3|intros a1 a2 H3| intros a1 H3|intros z H3| intros z H3|intros z1 z2 H3|intros z1 z2 H3|intros z1 z2 z3 H3];rewrite H3 in H12; try (apply diff_false_true in H12; inversion H12);
      case_eq (t_form .[ Lit.blit l2]); [intros a2 H4|intros H4|intro H4|intros z1 z2 H4| intros z2 H4|intros z H4| intros z H4|intros z1 z2 H4|intros z1 z2 H4|intros z1 z2 z3 H4]; rewrite H4 in H12; try (apply diff_false_true in H12; inversion H12);
      case_eq (t_atom .[a1]); [intros z1 H05|intros u1 h1' H05|intros z3 z1 z2 H05|intros z1 z2 H05|intros z1 z2 H05]; rewrite H05 in H12; try (apply diff_false_true in H12; inversion H12);
      case_eq (u1); [intro H06|intro H06|intro H06|intro H06|intro H06|intros j H06]; rewrite H06 in H12; try (apply diff_false_true in H12; inversion H12);
      case_eq (t_atom .[a2]); [intros z1 H07|intros u2 h2' H07|intros z3 z1 z2 H07|intros z1 z2 H07|intros z1 z2 H07]; rewrite H07 in H12; try (apply diff_false_true in H12; inversion H12);
      case_eq (u2); [intro H08|intro H08|intro H08|intro H08|intro H08|intros k H08]; rewrite H08 in H12; try (apply diff_false_true in H12; inversion H12);
      apply andb_true_iff in H12; destruct H12 as (H12,H13);apply andb_true_iff in H12; destruct H12 as (H12,H14);apply andb_true_iff in H12; destruct H12 as (H12,H15);apply andb_true_iff in H12; destruct H12 as (H12,H16);apply andb_true_iff in H12; destruct H12 as (H12,H17);apply andb_true_iff in H12; destruct H12 as (H12,H18);
      apply negb_true_iff in H17; apply Int63Properties.eqb_spec in H16;apply Int63Properties.eqb_spec in H14;apply Int63Properties.eqb_spec in H15;apply Int63Properties.eqb_spec in H13; subst j;subst k;subst h1'; subst h2'; rewrite <- H06 in H08; subst u2;
      
      unfold Lit.interp; rewrite H17; apply negb_true_iff; unfold Var.interp; rewrite rho_interp; rewrite H2; simpl; unfold Lit.interp; rewrite H12;rewrite H18; unfold Var.interp; rewrite !rho_interp; rewrite H3; rewrite H4; simpl; unfold Atom.interp_form_hatom; unfold interp_hatom; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      rewrite H07; rewrite H05; simpl; unfold interp_uop; rewrite H06; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom); 
      assert (x = x+1-1) as H5 by (rewrite <- to_Z_eq; rewrite (to_Z_sub_1 (x+1) 0); [rewrite (to_Z_add_1 x max_int); intuition; apply (ltb_trans x digits max_int);[apply H11|reflexivity] |apply eqb_false_spec in H7; apply not_0_ltb in H7; apply H7]); rewrite <- H5; unfold bit_rev; apply Bool.eqb_false_iff;
      unfold apply_unop;rewrite H32;rewrite H33;apply H10].
    Qed.
    
    Lemma valid_check_BuildDefInt2 : forall lits, C.valid rho (check_BuildDefInt2 lits).
    Proof.
      unfold wt,is_true in wt_t_atom; rewrite forallbi_spec in wt_t_atom;
      unfold check_BuildDefInt2,C.valid; intros lits;
      
      case_eq (t_form .[ Lit.blit (lits .[ 0])]); [intros a H|intro H|intro H|intros z1 z2 H|intros z1 H|intros z1 H|intros z1 H|intros z1 z2 H|intros z1 z2 H|intros z1 z2 z3 H]; auto using C.interp_true;
      case_eq (t_atom.[a]);[intros z1 H0|intros u hh H0|intros u h1 h2 H0|intros z1 z2 H0|intros z1 z2 H0]; auto using C.interp_true;
      case_eq u;intro i1;auto using C.interp_true; intro H1;
      case_eq (t_atom.[hh]);[intros c H2|intros z1 z2 H2|intros b h1 h2 H2|intros n ah H2|intros z1 z2 H2];auto using C.interp_true;
      case_eq b; intro H3;auto using C.interp_true;
      case_eq (length lits == 3); intros H4; auto using C.interp_true; 
      case_eq (t_form .[ Lit.blit (lits .[ 1])]);[intros a1 H5|intros|intros|intros|intros|intros|intros|intros|intros|intros]; auto using C.interp_true;
      case_eq (t_form .[ Lit.blit (lits .[ 2])]);[intros a2 H6|intros|intros|intros|intros|intros|intros|intros|intros|intros]; auto using C.interp_true;
      case_eq (t_atom .[ a1]);[intros|intros c1 h1' H7|intros|intros|intros]; auto using C.interp_true;
      case_eq c1;intro i2;auto using C.interp_true; intro H8;
      case_eq (t_atom .[ a2]);[intros|intros c2 h2' H9|intros|intros|intros]; auto using C.interp_true;
      case_eq c2;intro i3;auto using C.interp_true;intro H10; 
      case_eq ((h1' == h1) && (h2 == h2') && (i1 == i2) && (i2 == i3) && Lit.is_pos (lits .[ 1]) && Lit.is_pos (lits .[ 2])); auto using C.interp_true;intros H23;
      apply andb_true_iff in H23; destruct H23 as (H23,H31);apply andb_true_iff in H23; destruct H23 as (H23,H26);apply andb_true_iff in H23; destruct H23 as (H23,H27);apply andb_true_iff in H23; destruct H23 as (H23,H29);apply andb_true_iff in H23; destruct H23 as (H23,H30);
      apply Int63Properties.eqb_spec in H23;apply Int63Properties.eqb_spec in H27;apply Int63Properties.eqb_spec in H29;apply Int63Properties.eqb_spec in H30; subst h1';subst h2';subst i2;subst i3; rewrite <- H1 in H10;rewrite <- H1 in H8; subst c1; subst c2;

      assert (H100: hh < length t_atom) by (apply PArray.get_not_default_lt; rewrite H2, def_t_atom; discriminate);
      generalize (wt_t_atom _ H100); rewrite H2, H3; simpl;
      rewrite !andb_true_iff; intros [[_ H101] H102]; change (is_true (Typ.eqb (get_type' t_i t_interp h1) Typ.Tint)) in H101; change (is_true (Typ.eqb (get_type' t_i t_interp h2) Typ.Tint)) in H102; rewrite Typ.eqb_spec in H101; rewrite Typ.eqb_spec in H102;
      unfold get_type' in H101; rewrite t_interp_wf in H101; auto;
      unfold get_type' in H102; rewrite t_interp_wf in H102; auto;
      
      case_eq (Lit.is_pos (lits.[0]));intro H14;
      simpl; rewrite orb_false_r; apply orb_true_iff; rewrite orb_true_iff;
      unfold Lit.interp; rewrite !Lit.is_pos_neg;rewrite H31;rewrite H14;rewrite H26;simpl;unfold Var.interp; rewrite !rho_interp;rewrite !Lit.blit_neg;rewrite H;rewrite H5;rewrite H6; simpl; unfold Atom.interp_form_hatom; unfold interp_hatom; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      rewrite H0;rewrite H7;rewrite H9; simpl; unfold interp_uop; rewrite H1; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      rewrite H2; simpl; rewrite !t_interp_wf;try (apply wf_t_atom);try (apply def_t_atom);
      unfold interp_bop; rewrite H3;simpl; unfold apply_binop;
      case_eq (interp_atom (t_atom.[h1])); intros t1' v1 H32;
      rewrite H32 in H101; simpl in H101; subst t1';
      case_eq (interp_atom (t_atom.[h2])); intros t2' v2 H33;
      rewrite H33 in H102; simpl in H102; subst t2';
      rewrite Typ.cast_refl;
      simpl;unfold bit_rev;rewrite lxor_spec;destruct (bit v1 i1);destruct (bit v2 i1);[right;right|left|left|right;left|left|right;right|right;left|left];trivial.
    Qed.

  End Proof.
  
End Checker.
