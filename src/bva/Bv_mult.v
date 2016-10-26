(**************************************************************************)
(*                                                                        *)
(*     DTBitVector                                                        *)
(*     Copyright (C) 2011 - 2016                                          *)
(*                                                                        *)
(*     Chantal Keller  *                                                  *)
(*     Tianyi  Liang   ♯                                                  *)
(*     Alain   Mebsout ♯                                                  *)
(*     Burak   Ekici   ♯                                                  *)
(*                                                                        *)
(*    * Inria - École Polytechnique - Université Paris-Sud                *)
(*    ♯ The University of Iowa                                            *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

Add Rec LoadPath "." as SMTCoq.

Require Import List Bool NArith Psatz BVList Int63 Nnat.
Require Import Misc.
Import ListNotations.
Local Open Scope list_scope.
Local Open Scope N_scope.
Local Open Scope bool_scope.

Module MULT.

Import RAWBITVECTOR_LIST.



End MULT.

(*



Lemma helper1: forall l1 l2, (length l2 > length l1)%nat ->
add_list (true :: true :: l2)
  (false
   :: mult_bool_step (true :: true :: l1) (true :: true :: l2)
        (true :: true :: and_with_bool l1 true) 1 (length l1)) =
mult_bool_step (true :: true :: true :: l1) (true :: true :: l2)
  (true
   :: false
      :: true
         :: mult_bool_step_k_h (and_with_bool l1 true)
              (and_with_bool (firstn (length l1) (true :: l1)) true) true 
              (-2)) 2 (length l1).
Proof. intro l1.
       case_eq l1; simpl; intros.
       - case_eq l2; simpl; intros.
         subst. simpl in H0; now contradict H0.
         case_eq b; simpl; intros;
         case_eq l; simpl; intros; now compute.
       - case_eq l2; simpl; intros.
         subst. simpl in H0; now contradict H0.
         case_eq l; simpl; intros.
         case_eq l0; simpl; intros.
         case_eq b0; simpl; intros. subst. 
         contradict H0. simpl. lia.
         subst. contradict H0. simpl. lia.
         case_eq b0; simpl; intros;
         case_eq b1; simpl; intros;
         case_eq b; simpl; intros;
         case_eq l3; simpl; intros; now compute.
         simpl.
         case_eq l0; simpl; intros.
         case_eq b0; simpl; intros. subst. 
         contradict H0. simpl. lia.
         subst. contradict H0. simpl. lia.
         case_eq l3; simpl; intros.
         case_eq l4; simpl; intros. subst.
         contradict H0. simpl. lia.
         case_eq l5; simpl; intros;
         case_eq b; simpl; intros;
         case_eq b0; simpl; intros;
         case_eq b1; simpl; intros;
         case_eq b2; simpl; intros;
         case_eq b3; simpl; intros;
         now compute.
Admitted.

Lemma bvmults: forall a b, (length b >= length a)%nat ->  
      mult_list_carry a b (length a) = bvmult_bool a b (length a).
Proof.
    intro a.
    induction a as [ | xa xsa IHa ]; intros.
    - now simpl in *.
    - case_eq b; intros.
      + subst; now contradict H.
      + case_eq xa; intros.
        assert ((length (true :: xsa)) = S (length xsa)) by auto.
        rewrite <- H0, H2 in *.
        rewrite mult_list_carry_comm, mult_list_carry_add_list_t_f; auto.
        rewrite mult_list_carry_comm, IHa; auto.

        simpl.
        case_eq xsa; simpl; intros.
        rewrite H0. simpl.
        case_eq b0; simpl; intros.
        now rewrite add_list_t.
        now rewrite add_list_f.

        case_eq l0; simpl; intros.
        rewrite H0. simpl.
        case_eq l; simpl; intros.
        rewrite H4 in H3. rewrite H5 in H0. rewrite H3, H0 in H.
        contradict H. simpl. lia.
        case_eq l1; simpl; intros;
        case_eq b0; case_eq b1; case_eq b2; simpl; intros; now compute.
        rewrite H0. simpl.

        admit.

        apply (@length_ge _ b xsa xa); easy.
        apply (@length_ge _ b xsa xa); easy.

        assert ((length (false :: xsa)) = S (length xsa)) by auto.
        rewrite <- H0, H2.
        rewrite mult_list_carry_f_f_1.
        rewrite IHa. simpl.
        
        case_eq (xsa); simpl; intros.
        rewrite H0; simpl. case b0; easy.
        case_eq l0; simpl; intros.
        rewrite H0; simpl.
        case_eq l; simpl; intros;
        case_eq b0; case_eq b1; intros; try now simpl.
        case_eq b2; intros; now compute.
        case_eq b2; intros; now compute.
        case_eq b2; intros; now compute.
        case_eq b2; intros; now compute.

        admit.

        apply (@length_ge _ b xsa xa); easy.
Admitted.

(* bitvector MULT properties *)

(**
Lemma bv_mult_size: forall n a b, (size a) = n -> (@size b) = n -> size (bv_mult a b) = n.
Proof. intros n a b H0 H1.
       unfold bv_mult, size, bits in *.
       rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       specialize (@mult_list_length_eq a b). intro H2.
       rewrite <- H2; lia.
Qed.

Lemma bv_mult_comm: forall n a b, (size a) = n -> (size b) = n -> bv_mult a b = bv_mult b a.
Proof. intros n a b H0 H1.
       unfold bv_mult, size, bits in *. rewrite H0, H1.
       rewrite N.eqb_compare. rewrite N.compare_refl.
       rewrite (@mult_list_comm a b (nat_of_N n)). reflexivity.
       rewrite <- H0. now rewrite Nat2N.id.
       rewrite <- H1. now rewrite Nat2N.id.
Qed.
*)