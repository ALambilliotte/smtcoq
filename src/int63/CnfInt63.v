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

Require Import Bool.
Require Import List.
Require Import Int63.
Require Import PArray.
Require Import BoolEq.
Require Import NZParity.
Require Import Classical.

Add LoadPath ".." as SMTCoq.

Require Import Misc State.
Require Import SMT_terms.


Import Form.

Local Open Scope array_scope.
Local Open Scope int63_scope.

Set Implicit Arguments.
Unset Strict Implicit.


Definition or_of_imp args :=
  let last := PArray.length args - 1 in
  PArray.mapi (fun i l => if i == last then l else Lit.neg l) args.
(* Register or_of_imp as PrimInline. *)

Lemma length_or_of_imp : forall args,
  PArray.length (or_of_imp args) = PArray.length args.
Proof. intro; unfold or_of_imp; apply length_mapi. Qed.

Lemma get_or_of_imp : forall args i,
  i < (PArray.length args) - 1 -> (or_of_imp args).[i] = Lit.neg (args.[i]).
Proof.
  unfold or_of_imp; intros args i H; case_eq (0 < PArray.length args).
  intro Heq; rewrite get_mapi.
  replace (i == PArray.length args - 1) with false; auto; symmetry; rewrite eqb_false_spec; intro; subst i; unfold is_true in H; rewrite ltb_spec, (to_Z_sub_1 _ _ Heq) in H; omega.
  rewrite ltb_spec; unfold is_true in H; rewrite ltb_spec, (to_Z_sub_1 _ _ Heq) in H; omega.
  rewrite ltb_negb_geb; case_eq (PArray.length args <= 0); try discriminate; intros Heq _; assert (H1: PArray.length args = 0).
  apply to_Z_inj; rewrite leb_spec in Heq; destruct (to_Z_bounded (PArray.length args)) as [H1 _]; change [|0|] with 0%Z in *; omega.
  rewrite !get_outofbound.
  rewrite default_mapi, H1; auto.
  rewrite H1; case_eq (i < 0); auto; intro H2; eelim ltb_0; eassumption.
  rewrite length_mapi, H1; case_eq (i < 0); auto; intro H2; eelim ltb_0; eassumption.
Qed.

Lemma get_or_of_imp2 : forall args i, 0 < PArray.length args ->
  i = (PArray.length args) - 1 -> (or_of_imp args).[i] = args.[i].
Proof.
  unfold or_of_imp; intros args i Heq Hi; rewrite get_mapi; subst i.
  rewrite Int63Axioms.eqb_refl; auto.
  rewrite ltb_spec, (to_Z_sub_1 _ _ Heq); omega.
Qed.


Section Checker.

  Import Atom.


  Variable t_form : PArray.array form.
  Variable t_atom : PArray.array atom.

  Local Notation get_form := (PArray.get t_form) (only parsing).
  Local Notation get_atom := (PArray.get t_atom) (only parsing).

  Variable s : S.t.


  Definition atom_to_int (a : atom) :=
    match a with
    | Acop (CO_int i) => i
    | Auop (UO_index i) a => i
    | _ => 0%int63
    end.

  Fixpoint clean {A:Type} (l:list A) := 
    match l with 
    | nil => nil
    | a::nil => a::nil
    | a::b::c => a::(clean c)
    end.

  Definition check_BuildDefInt lits :=
    let n := PArray.length lits in
    if (n == Int63Op.digits + 1)&&(Lit.is_pos (lits.[0]))
    then (
      match get_form (Lit.blit (lits.[0])) with
      | Fatom a => 
        match get_atom a with
        | Abop b h1 h2 => 
          match (b,get_atom h1,get_atom h2) with
          | (BO_eq t,Acop (CO_int x),Acop (CO_int y)) => 
            let test_correct i0 l :=
              if i0 == 0
              then Lit.is_pos l
              else (
                match get_form (Lit.blit l) with
                | Fiff l1 l2 =>
                  match (get_form (Lit.blit l1),get_form (Lit.blit l2)) with
                  | (Fatom a1,Fatom a2) =>
                    match (get_atom a1,get_atom a2) with
                    | (Auop (UO_index j) hx1,Auop (UO_index k) hy1) => 
                      match (get_atom hx1,get_atom hy1) with
                      | (Acop (CO_int x1),Acop (CO_int y1)) => (Lit.is_pos l1)&&(Lit.is_pos l2)&&(negb (Lit.is_pos l))&&(j == i0-1)&&(k == j)&&(x == x1)&&(y==y1)
                      | _ => false
                      end
                    | _ => false
                    end
                  | _ => false
                  end
                | _ => false
                end
                   )
            in
            if (Typ.eqb t Typ.Tint)&&forallbi (fun i l => test_correct i l) lits
            then PArray.to_list lits
            else C._true
          | _ => C._true
          end
        | _ => C._true
        end
      | _ => C._true
      end
         )
    else C._true
  .


  Definition check_BuildProjInt lits i :=
    let n := PArray.length lits in
    if (n == Int63Op.digits + 1)&&(i < Int63Op.digits)
    then (
      match get_form (Lit.blit (lits.[0])) with
      | Fatom a => 
        match get_atom a with
        | Abop b h1 h2 => 
          match (b,get_atom h1,get_atom h2) with
          | (BO_eq t,Acop (CO_int x),Acop (CO_int y)) => 
            let test_correct i0 l :=
              match get_form (Lit.blit l) with
              | Fiff l1 l2 =>
                match (get_form (Lit.blit l1),get_form (Lit.blit l2)) with
                | (Fatom a1,Fatom a2) =>
                  match (get_atom a1,get_atom a2) with
                  | (Auop (UO_index j) hx1,Auop (UO_index k) hy1) => 
                    match (get_atom hx1,get_atom hy1) with
                    | (Acop (CO_int x1),Acop (CO_int y1)) => (Lit.is_pos l1)&&(Lit.is_pos l2)&&(negb (Lit.is_pos (lits.[0])))&&(Lit.is_pos l)&&(Typ.eqb t Typ.Tint)&&(j == i0)&&(k == j)&&(x == x1)&&(y==y1)
                    | _ => false
                    end

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
        | _ => C._true
        end
      | _ => C._true
      end
         )
    else C._true
  .

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
      Check interp_atom.
      Check interp_form_hatom.

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
      unfold check_BuildProjInt,C.valid. intros lits i.
      case_eq ((length lits == digits + 1) && (i < digits)).
      
      intros. case_eq (t_form.[Lit.blit (lits.[0])]).
      intros. case_eq (t_atom.[i0]);intros; auto using C.interp_true.
      case_eq b;intros; auto using C.interp_true.
      case_eq (t_atom.[i1]);intros; auto using C.interp_true.
      case_eq c;intros; auto using C.interp_true.
      case_eq (t_atom.[i2]);intros; auto using C.interp_true.
      case_eq c0;intros; auto using C.interp_true.
      case_eq (t_form.[Lit.blit (lits.[i+1])]);intros;auto using C.interp_true.
      case_eq (t_form.[Lit.blit i5]);intros;auto using C.interp_true.
      case_eq (t_form.[Lit.blit i6]);intros;auto using C.interp_true.
      case_eq (t_atom.[i7]);intros;auto using C.interp_true.
      case_eq u;intros;auto using C.interp_true.
      case_eq (t_atom.[i8]);intros;auto using C.interp_true.
      case_eq u0;intros;auto using C.interp_true.
      case_eq (t_atom.[i9]);intros;auto using C.interp_true.
      case_eq c1;intros;auto using C.interp_true.
      case_eq (t_atom.[i11]);intros;auto using C.interp_true.
      case_eq c2;intros;auto using C.interp_true.
      case_eq (Lit.is_pos i5 && Lit.is_pos i6 && negb (Lit.is_pos (lits .[ 0])) && Lit.is_pos (lits .[ i + 1]) && Typ.eqb t Typ.Tint && (i10 == i) && (i12 == i10) && (i3 == i13) && (i4 == i14));intros.
      apply andb_true_iff in H18; destruct H18;apply andb_true_iff in H18; destruct H18;apply andb_true_iff in H18; destruct H18;apply andb_true_iff in H18; destruct H18;apply andb_true_iff in H18; destruct H18;apply andb_true_iff in H18; destruct H18;apply andb_true_iff in H18; destruct H18;apply andb_true_iff in H18; destruct H18.
      
      rewrite Int63Properties.eqb_spec in H19; rewrite Int63Properties.eqb_spec in H20; rewrite Int63Properties.eqb_spec in H21; rewrite Int63Properties.eqb_spec in H22;apply Typ.eqb_spec in H23;subst i10; subst i12; subst i13; subst i14.
      symmetry in H11;symmetry in H4; symmetry in H6; rewrite H4 in H15; rewrite H6 in H17; rewrite H11 in H13;subst u0;subst t; subst c1; subst c2;symmetry in H11;symmetry in H4; symmetry in H6.
      rewrite negb_true_iff in H25.
      
      simpl; rewrite orb_false_r; apply orb_true_iff.
      unfold Lit.interp; rewrite H24; rewrite H25; rewrite negb_true_iff; unfold Var.interp; rewrite !rho_interp; rewrite H7; rewrite H0.
      simpl; unfold Lit.interp; rewrite H18; rewrite H26; unfold Var.interp; rewrite !rho_interp; rewrite H8; rewrite H9;simpl.
      unfold Atom.interp_form_hatom; unfold interp_hatom; rewrite !t_interp_wf. 
      rewrite H1; rewrite H10;rewrite H12; simpl; rewrite !t_interp_wf.
      unfold interp_uop; unfold interp_bop; rewrite H11; rewrite H2; simpl; rewrite H3;rewrite H5;rewrite H14;rewrite H16; simpl; unfold interp_cop; rewrite H4;rewrite H6;simpl.
      apply bool_impl; intro H27; apply Int63Properties.eqb_spec in H27; subst i4; trivial; apply Bool.eqb_true_iff; trivial.
      
      apply wf_t_atom. apply def_t_atom. 
      apply wf_t_atom. apply def_t_atom.
      apply wf_t_atom. apply def_t_atom.
      apply wf_t_atom. apply def_t_atom.
      apply wf_t_atom. apply def_t_atom.
      apply wf_t_atom. apply def_t_atom.
      apply wf_t_atom. apply def_t_atom. 
      auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
      intros; auto using C.interp_true.
    Qed.

    Lemma digit_plus_1_not_0 : (0 == digits+1) = false.
    Proof.
      apply Int63Properties.eqb_false_complete.
      apply not_eq_sym.
      apply Int63Properties.not_0_ltb.
      apply succ_max_int.
      reflexivity.
    Qed.

   Lemma digit_plus_1_not_02 : (digits+1 == 0) = false.
    Proof.
      apply Int63Properties.eqb_false_complete.
      apply Int63Properties.not_0_ltb.
      apply succ_max_int.
      reflexivity.
    Qed.

    Axiom afold_left_or : forall a,
      afold_left bool int false orb (Lit.interp rho) a =
      C.interp rho (to_list a).

    Ltac tauto_check :=
      try (rewrite !Lit.interp_neg);
      repeat 
      match goal with |- context [Lit.interp rho ?x] => 
      destruct (Lit.interp rho x);trivial end.

    Axiom afold_left_and : forall a,
      afold_left bool int true andb (Lit.interp rho) a =
      List.forallb (Lit.interp rho) (to_list a).

    Axiom afold_right_impb : forall a,
      (afold_right bool int true implb (Lit.interp rho) a) =
      C.interp rho (to_list (or_of_imp a)).

    Lemma contrap : forall a b, (a = true -> b = true) <-> (b = false -> a = false).
    Proof.
      intros.
      split.
      intros.
      destruct a.
      destruct b.
      trivial.
      symmetry.
      apply H.
      trivial.
      trivial.
      intros;destruct a;destruct b.
      trivial.
      symmetry.
      apply H; trivial.
      trivial.
      apply H0.
    Qed.

    Lemma bit_eq_false i1 i2: i1 <> i2 -> exists i, bit i1 i <> bit i2 i /\ i < digits = true.
    Proof.
      intros.
      rewrite bit_eq in H. 
      apply not_all_ex_not in H.
      inversion H.
      exists x.
      split.
      apply H0.
      assert (digits <= x = true -> (Bool.eqb (bit i1 x) (bit i2 x) = true)).
      intros.
      rewrite !bit_M.
      simpl.
      trivial.
      apply H1. apply H1.
      apply contrap in H1.
      apply negb_true_iff in H1.
      rewrite <- H1.
      rewrite ltb_negb_geb.
      trivial.
      rewrite Bool.eqb_false_iff.
      apply H0.
    Qed. 
    
    
    Lemma inf_plus_un : forall a b, (b < max_int) = true -> (a < b) = true -> (a + 1 < b + 1) = true.
    Proof.
      intros a b H1 H2.
      rewrite ltb_leb_sub1.
      generalize H2.
      rewrite <- (ltb_leb_add1 (b +1 -1) b a).
      intro.
      assert (b = b+1-1).
      rewrite <- to_Z_eq.
      rewrite (to_Z_sub_1 (b+1) 0).
      rewrite (to_Z_add_1 b max_int).
      intuition.
      apply H1.
      apply succ_max_int.
      apply H1.
      rewrite <- H0.
      apply H.
      apply H2.
      apply not_0_ltb.
      apply succ_max_int.
      apply H1.
    Qed.

    Lemma valid_check_BuildDefInt : forall lits, C.valid rho (check_BuildDefInt lits).
    Proof.
      unfold check_BuildDefInt,C.valid. intro lits.
      
      case_eq ((length lits == digits + 1) && Lit.is_pos (lits .[ 0])); intro H. apply andb_true_iff in H; destruct H; rewrite Int63Properties.eqb_spec in H.
      case_eq (t_form .[ Lit.blit (lits .[ 0])]); intros.
      case_eq (t_atom.[i]);intros; auto using C.interp_true.
      case_eq (b);intros; auto using C.interp_true.
      case_eq (t_atom.[i0]);intros; auto using C.interp_true.
      case_eq (c);intros; auto using C.interp_true.
      case_eq (t_atom .[ i1]);intros; auto using C.interp_true.
      case_eq (c0);intros; auto using C.interp_true.
      case_eq ( Typ.eqb t Typ.Tint &&
        forallbi
        (fun i4 l : int =>
         if i4 == 0
         then Lit.is_pos l
         else
          match t_form .[ Lit.blit l] with
          | Fatom _ => false
          | Ftrue => false
          | Ffalse => false
          | Fnot2 _ _ => false
          | Fand _ => false
          | For _ => false
          | Fimp _ => false
          | Fxor _ _ => false
          | Fiff l1 l2 =>
              match t_form .[ Lit.blit l1] with
              | Fatom a1 =>
                  match t_form .[ Lit.blit l2] with
                  | Fatom a2 =>
                      match t_atom .[ a1] with
                      | Acop _ => false
                      | Auop UO_xO _ => false
                      | Auop UO_xI _ => false
                      | Auop UO_Zpos _ => false
                      | Auop UO_Zneg _ => false
                      | Auop UO_Zopp _ => false
                      | Auop (UO_index j) hx1 =>
                          match t_atom .[ a2] with
                          | Acop _ => false
                          | Auop UO_xO _ => false
                          | Auop UO_xI _ => false
                          | Auop UO_Zpos _ => false
                          | Auop UO_Zneg _ => false
                          | Auop UO_Zopp _ => false
                          | Auop (UO_index k) hy1 =>
                              match t_atom .[ hx1] with
                              | Acop CO_xH => false
                              | Acop CO_Z0 => false
                              | Acop (CO_int x1) =>
                                  match t_atom .[ hy1] with
                                  | Acop CO_xH => false
                                  | Acop CO_Z0 => false
                                  | Acop (CO_int y1) =>
                                      Lit.is_pos l1 && Lit.is_pos l2 &&
                                      negb (Lit.is_pos l) && (j == i4 - 1) &&
                                      (k == j) && (i2 == x1) && (i3 == y1)
                                  | Auop _ _ => false
                                  | Abop _ _ _ => false
                                  | Anop _ _ => false
                                  | Aapp _ _ => false
                                  end
                              | Auop _ _ => false
                              | Abop _ _ _ => false
                              | Anop _ _ => false
                              | Aapp _ _ => false
                              end
                          | Abop _ _ _ => false
                          | Anop _ _ => false
                          | Aapp _ _ => false
                          end
                      | Abop _ _ _ => false
                      | Anop _ _ => false
                      | Aapp _ _ => false
                      end
                  | Ftrue => false
                  | Ffalse => false
                  | Fnot2 _ _ => false
                  | Fand _ => false
                  | For _ => false
                  | Fimp _ => false
                  | Fxor _ _ => false
                  | Fiff _ _ => false
                  | Fite _ _ _ => false
                  end
              | Ftrue => false
              | Ffalse => false
              | Fnot2 _ _ => false
              | Fand _ => false
              | For _ => false
              | Fimp _ => false
              | Fxor _ _ => false
              | Fiff _ _ => false
              | Fite _ _ _ => false
              end
          | Fite _ _ _ => false
          end) lits
              );intros; auto using C.interp_true.
      apply andb_true_iff in H8; destruct H8 as [H10 H8];apply Typ.eqb_spec in H10; subst t.

      rewrite forallbi_spec in H8.
      unfold C.interp. SearchAbout List.existsb. apply existsb_exists. 
      case_eq (i2 == i3);intros. rewrite Int63Properties.eqb_spec in H9; subst i2.
      exists (lits.[0]). unfold Lit.interp. rewrite H0. unfold Var.interp. rewrite rho_interp. rewrite H1. simpl. unfold Atom.interp_form_hatom. unfold interp_hatom. rewrite !t_interp_wf. rewrite H2. simpl. unfold interp_bop. rewrite H3. simpl. rewrite !t_interp_wf. rewrite H4. rewrite H6. simpl. unfold interp_cop. rewrite H5. rewrite H7. simpl. rewrite Int63Properties.eqb_spec. simpl. split.
      apply to_list_In. rewrite H. reflexivity.
      trivial.
      apply wf_t_atom. apply def_t_atom.
      apply wf_t_atom. apply def_t_atom.
      apply wf_t_atom. apply def_t_atom.

      apply Int63Properties.eqb_false_spec in H9. apply bit_eq_false in H9. inversion H9. destruct H10.
      exists (lits.[x+1]).
      split. apply (to_list_In lits (x+1)). rewrite H. rewrite inf_plus_un. trivial. reflexivity. apply H11.
      
      unfold Lit.interp. assert (H12 := H8 (x+1)). rewrite H in H12. rewrite inf_plus_un in H12. 

      assert ( (true = true ->
      (if x + 1 == 0
       then Lit.is_pos (lits .[ x + 1])
       else
        match t_form .[ Lit.blit (lits .[ x + 1])] with
        | Fatom _ => false
        | Ftrue => false
        | Ffalse => false
        | Fnot2 _ _ => false
        | Fand _ => false
        | For _ => false
        | Fimp _ => false
        | Fxor _ _ => false
        | Fiff l1 l2 =>
            match t_form .[ Lit.blit l1] with
            | Fatom a1 =>
                match t_form .[ Lit.blit l2] with
                | Fatom a2 =>
                    match t_atom .[ a1] with
                    | Acop _ => false
                    | Auop UO_xO _ => false
                    | Auop UO_xI _ => false
                    | Auop UO_Zpos _ => false
                    | Auop UO_Zneg _ => false
                    | Auop UO_Zopp _ => false
                    | Auop (UO_index j) hx1 =>
                        match t_atom .[ a2] with
                        | Acop _ => false
                        | Auop UO_xO _ => false
                        | Auop UO_xI _ => false
                        | Auop UO_Zpos _ => false
                        | Auop UO_Zneg _ => false
                        | Auop UO_Zopp _ => false
                        | Auop (UO_index k) hy1 =>
                            match t_atom .[ hx1] with
                            | Acop CO_xH => false
                            | Acop CO_Z0 => false
                            | Acop (CO_int x1) =>
                                match t_atom .[ hy1] with
                                | Acop CO_xH => false
                                | Acop CO_Z0 => false
                                | Acop (CO_int y1) =>
                                    Lit.is_pos l1 && Lit.is_pos l2 &&
                                    negb (Lit.is_pos (lits .[ x + 1])) &&
                                    (j == x + 1 - 1) && (k == j) &&
                                    (i2 == x1) && (i3 == y1)
                                | Auop _ _ => false
                                | Abop _ _ _ => false
                                | Anop _ _ => false
                                | Aapp _ _ => false
                                end
                            | Auop _ _ => false
                            | Abop _ _ _ => false
                            | Anop _ _ => false
                            | Aapp _ _ => false
                            end
                        | Abop _ _ _ => false
                        | Anop _ _ => false
                        | Aapp _ _ => false
                        end
                    | Abop _ _ _ => false
                    | Anop _ _ => false
                    | Aapp _ _ => false
                    end
                | Ftrue => false
                | Ffalse => false
                | Fnot2 _ _ => false
                | Fand _ => false
                | For _ => false
                | Fimp _ => false
                | Fxor _ _ => false
                | Fiff _ _ => false
                | Fite _ _ _ => false
                end
            | Ftrue => false
            | Ffalse => false
            | Fnot2 _ _ => false
            | Fand _ => false
            | For _ => false
            | Fimp _ => false
            | Fxor _ _ => false
            | Fiff _ _ => false
            | Fite _ _ _ => false
            end
        | Fite _ _ _ => false
        end) = true) -> (if x + 1 == 0
       then Lit.is_pos (lits .[ x + 1])
       else
        match t_form .[ Lit.blit (lits .[ x + 1])] with
        | Fatom _ => false
        | Ftrue => false
        | Ffalse => false
        | Fnot2 _ _ => false
        | Fand _ => false
        | For _ => false
        | Fimp _ => false
        | Fxor _ _ => false
        | Fiff l1 l2 =>
            match t_form .[ Lit.blit l1] with
            | Fatom a1 =>
                match t_form .[ Lit.blit l2] with
                | Fatom a2 =>
                    match t_atom .[ a1] with
                    | Acop _ => false
                    | Auop UO_xO _ => false
                    | Auop UO_xI _ => false
                    | Auop UO_Zpos _ => false
                    | Auop UO_Zneg _ => false
                    | Auop UO_Zopp _ => false
                    | Auop (UO_index j) hx1 =>
                        match t_atom .[ a2] with
                        | Acop _ => false
                        | Auop UO_xO _ => false
                        | Auop UO_xI _ => false
                        | Auop UO_Zpos _ => false
                        | Auop UO_Zneg _ => false
                        | Auop UO_Zopp _ => false
                        | Auop (UO_index k) hy1 =>
                            match t_atom .[ hx1] with
                            | Acop CO_xH => false
                            | Acop CO_Z0 => false
                            | Acop (CO_int x1) =>
                                match t_atom .[ hy1] with
                                | Acop CO_xH => false
                                | Acop CO_Z0 => false
                                | Acop (CO_int y1) =>
                                    Lit.is_pos l1 && Lit.is_pos l2 &&
                                    negb (Lit.is_pos (lits .[ x + 1])) &&
                                    (j == x + 1 - 1) && (k == j) &&
                                    (i2 == x1) && (i3 == y1)
                                | Auop _ _ => false
                                | Abop _ _ _ => false
                                | Anop _ _ => false
                                | Aapp _ _ => false
                                end
                            | Auop _ _ => false
                            | Abop _ _ _ => false
                            | Anop _ _ => false
                            | Aapp _ _ => false
                            end
                        | Abop _ _ _ => false
                        | Anop _ _ => false
                        | Aapp _ _ => false
                        end
                    | Abop _ _ _ => false
                    | Anop _ _ => false
                    | Aapp _ _ => false
                    end
                | Ftrue => false
                | Ffalse => false
                | Fnot2 _ _ => false
                | Fand _ => false
                | For _ => false
                | Fimp _ => false
                | Fxor _ _ => false
                | Fiff _ _ => false
                | Fite _ _ _ => false
                end
            | Ftrue => false
            | Ffalse => false
            | Fnot2 _ _ => false
            | Fand _ => false
            | For _ => false
            | Fimp _ => false
            | Fxor _ _ => false
            | Fiff _ _ => false
            | Fite _ _ _ => false
            end
        | Fite _ _ _ => false
        end) = true).
        intros. apply H13. trivial. apply H13 in H12.
        clear H13.
        assert (x + 1 == 0 = false).
        apply eqb_false_spec.
        apply not_0_ltb.
        apply succ_max_int.
        assert (digits < max_int = true).
        reflexivity.
        apply (ltb_trans x digits max_int).
        apply H11. apply H13.
        rewrite H13 in H12.
        case_eq (t_form .[ Lit.blit (lits .[ x + 1])]); intros; rewrite H14 in H12; try (apply diff_false_true in H12; inversion H12).
        case_eq (t_form .[ Lit.blit i4]); intros; rewrite H15 in H12; try (apply diff_false_true in H12; inversion H12).
        case_eq (t_form .[ Lit.blit i5]); intros; rewrite H16 in H12; try (apply diff_false_true in H12; inversion H12).
        case_eq (t_atom .[i6]); intros; rewrite H17 in H12; try (apply diff_false_true in H12; inversion H12).
 simpl in H12.
      
    Qed.
 
  End Proof.
  
End Checker.