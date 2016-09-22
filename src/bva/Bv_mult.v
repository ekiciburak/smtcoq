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

Import RAWBITVECTOR_LIST.

Lemma mult_list_empty_l: forall (a: list bool), (mult_list [] a) = [].
Proof. intro a. induction a as [ | a xs IHxs].
         - unfold mult_list. simpl. reflexivity.
         - apply IHxs.
Qed.

Lemma mult_list_carry_0: forall a b, mult_list_carry a b 0 = [].
Proof. intro a. induction a as [ | a' xs IHxs].
       - intro b. simpl. reflexivity.
       - intros [ | b' ys].
         + simpl. case_eq a'.
           * simpl. intro H. rewrite add_list_empty_l; reflexivity.
           * simpl. intro H. apply IHxs.
         + simpl. case_eq a'.
           * simpl. intro H. rewrite IHxs. rewrite add_list_empty_r; reflexivity.
           * simpl. intro H. apply IHxs.
Qed.

Lemma mult_list_true: forall a n, ((length a) = n)%nat -> mult_list_carry [true] a n = a.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros n H. simpl in H. rewrite <- H.
         rewrite mult_list_carry_0. reflexivity.
       - intros [ | n] H.
         + contradict H. easy.
         + rewrite <- (IHxs n) at 2; try auto. simpl.
           case a. unfold add_list. simpl. reflexivity.
           unfold add_list. simpl. reflexivity.
Qed.

Lemma mult_list_false_l: forall a n, mult_list_carry [false] a n = mk_list_false n.
Proof. intro a.
       induction a as [ | a xs IHxs]; simpl; reflexivity.
Qed.

Lemma mult_list_carry_empty_l: forall (a: list bool) (c: nat), mult_list_carry [] a c = mk_list_false c.
Proof. intro a. induction a as [ | a' xs IHxs]; auto. Qed.

Lemma strictly_positive_0_unique: forall n: nat, (0 >= n)%nat <-> (n = 0)%nat.
Proof. intro n. induction n as [ | n IHn].
       split; try auto.
       split; intro H; contradict H; easy.
Qed.

Lemma mult_list_carry_length: forall (a b: list bool) n, ((length b) >= n)%nat -> n = length (mult_list_carry a b n).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H. rewrite mult_list_carry_empty_l, length_mk_list_false; reflexivity.
       - intros [ | b ys] n H. simpl in H. rewrite strictly_positive_0_unique in H.
         rewrite H. rewrite mult_list_carry_0. easy.
         simpl. case a.
         + specialize (@length_add_list_ge (b :: ys) (mult_list_carry xs (false :: b :: ys) n)).
           intro H1. rewrite <- H1. 
           rewrite <- (IHxs (false :: b :: ys)). reflexivity. simpl in *. lia.
           specialize (@IHxs (false :: b :: ys)). rewrite <- IHxs. easy. simpl. simpl in H. lia.
         + specialize (@IHxs (false :: b :: ys)). apply IHxs. inversion H. simpl. lia. simpl in *. lia.
Qed.

Lemma mult_list_length: forall (a b: list bool), ((length b) >= (length a))%nat -> (length a) = length (mult_list_native a b).
Proof. intros a b H. unfold mult_list_native.
       rewrite <- (@mult_list_carry_length a b (length a)); auto.
Qed.

Lemma mult_list_length_eq: forall (a b: list bool), ((length a) = (length b))%nat -> (length a) = length (mult_list_native a b).
Proof. intros a b H. unfold mult_list_native.
       rewrite <- (@mult_list_carry_length a b (length a)); lia.
Qed.

Lemma mult_list_cons_false1: forall (a b: list bool) n, ((length a) >= n)%nat -> ((length b) >= n)%nat ->
                       mult_list_carry (false :: a) b n = mult_list_carry a (false :: b) n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0 H1. rewrite strictly_positive_0_unique in H0. rewrite H0.
         do 2 rewrite mult_list_carry_0. reflexivity.
       - intros [ | b ys] n H0 H1.
         + rewrite strictly_positive_0_unique in H1. rewrite H1.
           do 2 rewrite mult_list_carry_0. reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false1': forall (a b: list bool) n, ((length (false :: b)) >= n)%nat ->
                       mult_list_carry (false :: a) b n = mult_list_carry a (false :: b) n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [ | b ys] n H0.
         + simpl. case a; reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false1'': forall (a b: list bool) n,
                       mult_list_carry (false :: a) b n = mult_list_carry a (false :: b) n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [ | b ys] n.
         + simpl. case a; reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false2: forall (a b: list bool) n, ((length a) >= n)%nat -> ((length b) >= n)%nat ->
                       mult_list_carry a (false :: b) n = mult_list_carry (false :: a) b n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0 H1. rewrite strictly_positive_0_unique in H0. rewrite H0.
         do 2 rewrite mult_list_carry_0. reflexivity.
       - intros [ | b ys] n H0 H1.
         + rewrite strictly_positive_0_unique in H1. rewrite H1.
           do 2 rewrite mult_list_carry_0. reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false2': forall (a b: list bool) n, ((length (false :: b)) >= n)%nat ->
                       mult_list_carry a (false :: b) n = mult_list_carry (false :: a) b n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [ | b ys] n H0.
         + simpl. case a; reflexivity.
         + simpl. reflexivity.
Qed.

Lemma mult_list_cons_false2'': forall (a b: list bool) n,
                       mult_list_carry a (false :: b) n = mult_list_carry (false :: a) b n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [ | b ys] n.
         + simpl. case a; reflexivity.
         + simpl. reflexivity.
Qed.

Lemma add_list_carry_rl0: forall (a b: list bool), 
add_list_ingr (add_list_ingr a a false) b false = add_list_ingr (removelast (false :: a)) b false.
Proof. intros a b. now rewrite add_list_carry_twice. Qed.

Lemma add_list_carry_rl1: forall (a b: list bool), 
add_list_ingr (removelast (false :: a)) b true = add_list_ingr (removelast (true :: a)) b false.
Proof. intros a b.
       simpl. case a.
       simpl. reflexivity.
       intros b0 l.
       simpl. reflexivity.
Qed.

Lemma add_list_carry_rl_t: forall  (a b: list bool), a <> [] ->
add_list_ingr (removelast (true :: a)) b false =
add_list_ingr a (add_list_ingr a b false) true.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b H0. now contradict H0.
       - intros [ | b ys] H0.
         + reflexivity.
         + case a, b; 
           do 4 (rewrite <- (@add_list_carry_assoc _ _ _ false true); 
                 [rewrite add_list_carry_twice; rewrite  add_list_carry_rl1; reflexivity| auto]).
Qed.

Lemma add_list_carry_tf_t: forall (a b: list bool),
add_list (true :: a) (false :: b) = true :: add_list a b.
Proof. now simpl. Qed.

Lemma add_list_carry_ft_t: forall (a b: list bool),
add_list (false :: a) (true :: b) = true :: add_list a b.
Proof. now simpl. Qed.

Lemma add_list_carry_tf_tf_comm: forall (a b: list bool),
(add_list (true :: a) (false :: b)) = (add_list (true :: b) (false :: a)).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros [ | b ys].
         + reflexivity.
         + simpl. now do 2 rewrite add_list_carry_tf_t.
       - intros [ | b ys].
         + simpl. now do 2 rewrite add_list_carry_tf_t.
         + do 2 rewrite add_list_carry_tf_t. apply f_equal.
           case a, b; now rewrite add_list_comm.
Qed.

Lemma add_list_carry_ft_ft_comm: forall (a b: list bool),
(add_list (false :: a) (true :: b)) = (add_list (false :: b) (true :: a)).
Proof. intro a.
       induction a as [ | a xs IHxs]; intros [ | b ys]; try (now unfold add_list).
       unfold add_list. simpl. apply f_equal.
       case a, b; simpl; now rewrite add_list_carry_comm.
Qed.

Lemma add_list_carry_ff_f: forall (a b: list bool),
(add_list (false :: a) (false :: b)) = (false :: add_list a b).
Proof. intro a.
       induction a as [ | a xs IHxs]; intros [ | b ys]; now unfold add_list.
Qed.

Lemma mult_list_carry_f_f_1: forall (a b: list bool) n,
                       mult_list_carry (false :: a) b (S n) = false :: mult_list_carry a b n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [ | b ys] n.
         + case a.
          * rewrite mult_list_cons_false1''. 
            simpl. rewrite mult_list_cons_false2''.
            rewrite IHxs.
            rewrite mult_list_cons_false2''.
            now rewrite <- add_list_carry_ff_f.
          * rewrite mult_list_cons_false1''. 
            simpl. rewrite mult_list_cons_false2''.
            rewrite IHxs.
            now rewrite mult_list_cons_false2''.
         + case a, b.
           * simpl. rewrite mult_list_cons_false2''. rewrite IHxs.
             now rewrite add_list_carry_ff_f.
           * simpl. rewrite mult_list_cons_false2''. rewrite IHxs.
             now rewrite add_list_carry_ff_f.
           * simpl. rewrite mult_list_cons_false2''.
             rewrite IHxs. reflexivity.
           * simpl. rewrite mult_list_cons_false2''.
             rewrite IHxs. reflexivity.
Qed.

Lemma mult_list_carry_f_f_2: forall (a b: list bool) n,
                       mult_list_carry a (false :: b) (S n) = false :: mult_list_carry a b n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n. rewrite mult_list_carry_empty_l. simpl. reflexivity.
       - intros [ | b ys] n.
         + case a.
          * rewrite mult_list_cons_false2''. 
            simpl. rewrite IHxs.
            rewrite mult_list_cons_false2''.
            now rewrite <- add_list_carry_ff_f.
          * rewrite mult_list_cons_false1''.
            rewrite IHxs.
            now rewrite mult_list_cons_false2''.
         + case a, b.
           * simpl. rewrite IHxs.
             now rewrite add_list_carry_ff_f.
           * simpl. rewrite IHxs.
             now rewrite add_list_carry_ff_f.
           * simpl. rewrite IHxs. reflexivity.
           * simpl. rewrite IHxs. reflexivity.
Qed.

Lemma mult_list_carry_ff_ff: forall (a b: list bool) n,
                       mult_list_carry (false :: a) (false :: b) (S (S n)) = false :: false :: mult_list_carry a b n.
Proof. intros a b n.
       rewrite mult_list_carry_f_f_1, mult_list_carry_f_f_2.
       reflexivity.
Qed.

Lemma mult_list_carry_1: forall (a: list bool), (mult_list_carry a [false; true] 1) = [false].
Proof. intro a.
       induction a as [ | a xs IHxs].
       - simpl. reflexivity.
       - simpl. case a.
         + rewrite mult_list_cons_false2'.
           rewrite mult_list_carry_f_f_1. rewrite mult_list_carry_0. 
           now unfold add_list.
           simpl; lia.
         + rewrite mult_list_cons_false2'.
           rewrite mult_list_carry_f_f_1. now rewrite mult_list_carry_0.
           simpl; lia.
Qed.

Lemma nsubst_0: forall n, (n - 0)%nat = n.
Proof. intro n. 
       induction n as [ | n IHn]; now simpl.
Qed.

Lemma nsubst_S: forall n, (n <> 0)%nat -> n = S (n - 1)%nat.
Proof. intro n.
       induction n as [ | n IHn]; intro H.
       - now contradict H.
       - simpl. now rewrite nsubst_0.
Qed.


Lemma not_empty: forall (a: list bool) n, ((length a) > n)%nat -> a <> [].
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros n H. now contradict H.
       - intros [ | n] H; easy.
Qed.

Lemma mult_list_carry_add_list_t_f: forall (a b: list bool) n, ((length a) > n)%nat ->
(mult_list_carry a (true :: b) (S n)) = (add_list a (false :: mult_list_carry a b n)).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0. simpl in H0.
         now contradict H0.
      - intros [ | b ys] n H0.
         + case a.
           * simpl.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_tf_t.
             rewrite add_list_carry_tf_t.
             apply f_equal.
             now rewrite add_list_empty_r, add_list_empty_l.
           * rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f.
             apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_1.
               rewrite <- IHxs.
               reflexivity.
               simpl in *; lia.
         + case a, b.
           * simpl.
             rewrite mult_list_cons_false2''.
             rewrite mult_list_cons_false2''.
             rewrite add_list_carry_tf_tf_comm.
             symmetry; rewrite add_list_comm; symmetry.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_tf_t.
             rewrite add_list_carry_ft_t. apply f_equal.
             specialize (@IHxs (true :: ys)).
             rewrite <- add_list_assoc.
             cut ((add_list xs (true :: ys)) = (add_list (true :: ys) xs)).
             intro H3. rewrite H3.
             rewrite add_list_assoc.
             induction n.
               do 2 rewrite mult_list_carry_0. now do 3 rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_1.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             now rewrite add_list_comm.
           * simpl.
             rewrite mult_list_cons_false2''.
             rewrite mult_list_cons_false2''.
             rewrite add_list_carry_tf_tf_comm.
             symmetry; rewrite add_list_comm; symmetry.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_tf_t.
             rewrite add_list_carry_ft_t. apply f_equal.
             specialize (@IHxs (false :: ys)).
             rewrite <- add_list_assoc.
             cut ((add_list xs (false :: ys)) = (add_list (false :: ys) xs)).
             intro H3. rewrite H3.
             rewrite add_list_assoc.
             induction n.
               do 2 rewrite mult_list_carry_0. now do 3 rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_1.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             now rewrite add_list_comm.
           * rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f.
             apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_1.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
           * rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f.
             apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_1.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
Qed.

Lemma mult_list_carry_t_tt_add_list_f_t_tt: forall (a b: list bool) n, ((length a) >= n)%nat ->
mult_list_carry (true :: a) (true :: true :: b) (S n) =
add_list (false :: a)
  (true :: mult_list_carry (true :: a) (true :: b) n).
Proof. intros. simpl.
        rewrite mult_list_cons_false2''.
        rewrite mult_list_cons_false2''.
        rewrite add_list_carry_ft_ft_comm.
        symmetry; rewrite add_list_comm; symmetry.
        rewrite mult_list_carry_f_f_1.
        induction n.
         do 2 rewrite mult_list_carry_0. rewrite add_list_empty_r.
          unfold add_list. simpl. now rewrite add_list_ingr_r.
        rewrite mult_list_carry_f_f_1.
        rewrite add_list_carry_tf_t.
        rewrite add_list_carry_tf_t. apply f_equal.
        rewrite add_list_carry_tf_tf_comm. simpl.
        rewrite mult_list_carry_add_list_t_f.
        rewrite add_list_carry_tf_tf_comm.
        rewrite <- add_list_assoc. rewrite <- add_list_assoc.
        cut (add_list (true :: b) a = add_list a (true :: b)).
        intro H3; now rewrite H3.
        now rewrite add_list_comm.
        simpl in *; lia.
Qed.

Lemma mult_list_carry_t_tf_add_list_f_t_tf: forall (a b: list bool) n, ((length a) >= n)%nat ->
mult_list_carry (true :: a) (true :: false :: b) (S n) =
add_list (false :: a) (true :: mult_list_carry (true :: a) (false :: b) n).
Proof. intros. simpl.
        rewrite mult_list_cons_false2''.
        rewrite mult_list_cons_false2''.
        rewrite add_list_carry_ft_ft_comm.
        symmetry; rewrite add_list_comm; symmetry.
        rewrite mult_list_carry_f_f_1.
        induction n.
         do 2 rewrite mult_list_carry_0. rewrite add_list_empty_r.
          unfold add_list. simpl. now rewrite add_list_ingr_r.
        rewrite mult_list_carry_f_f_1.
        rewrite add_list_carry_tf_t.
        rewrite add_list_carry_tf_t. apply f_equal.
        rewrite mult_list_carry_add_list_t_f.
        rewrite <- add_list_assoc.
        rewrite <- add_list_assoc.
        cut (add_list (false :: b) a = add_list a (false :: b)).
        intro H3; now rewrite H3.
        now rewrite add_list_comm.
        simpl in *; lia.
Qed.

Lemma mult_list_carry_tt_add_list_ft: forall (a b: list bool) n, ((length a) >= n)%nat ->
mult_list_carry a (true :: true :: b) n =
add_list a (mult_list_carry a (false :: true :: b) n).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0. rewrite strictly_positive_0_unique in H0. 
           rewrite H0. now do 2 rewrite mult_list_carry_0.
       - intros [ | b ys] n H0.
         + case a.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_tf_t.
               rewrite add_list_carry_ff_f.
               rewrite add_list_carry_tf_t. apply f_equal.
               rewrite IHxs.
               rewrite <- add_list_assoc.
               rewrite <- add_list_assoc.
               cut ((add_list [true] xs) = (add_list xs [true])). now (intro H1; rewrite H1).
               now rewrite add_list_comm.
               simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
               rewrite IHxs. reflexivity.
               simpl in *; lia.
         + case a, b.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tt_add_list_f_t_tt.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tt_add_list_f_t_tt.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f. apply f_equal.
             rewrite IHxs.
             rewrite mult_list_cons_false1''. reflexivity.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f. apply f_equal.
             rewrite IHxs.
             rewrite mult_list_cons_false1''. reflexivity.
             simpl in *; lia.
Qed.

Lemma mult_list_carry_tf_add_list_ff: forall (a b: list bool) n, ((length a) >= n)%nat  ->
mult_list_carry a (true :: false :: b) n =
add_list a (mult_list_carry (false :: a) (false :: b) n).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0. rewrite strictly_positive_0_unique in H0. 
           rewrite H0. now do 2 rewrite mult_list_carry_0.
       - intros [ | b ys] n H0.
         + case a.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_tf_t.
               rewrite add_list_carry_ff_f.
               rewrite add_list_carry_tf_t. apply f_equal.
               rewrite IHxs.
               rewrite <- add_list_assoc.
               rewrite <- add_list_assoc.
               cut ((add_list [false] xs) = (add_list xs [false])). now (intro H1; rewrite H1).
               now rewrite add_list_comm.
               simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
               rewrite IHxs. reflexivity.
               simpl in *; lia.
         + case a, b.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tf_add_list_f_t_tf.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tf_add_list_f_t_tf.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f. apply f_equal.
             rewrite IHxs.
             rewrite mult_list_cons_false1''. reflexivity.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_1.
             rewrite add_list_carry_ff_f. apply f_equal.
             rewrite IHxs.
             rewrite mult_list_cons_false1''. reflexivity.
             simpl in *; lia.
Qed.

Lemma mult_list_carry_ft_add_list_f_ff: forall (a b: list bool) n, ((length a) >= n)%nat ->
(mult_list_carry a (false :: true :: b) n) =
(add_list (false :: a) ((mult_list_carry a (false :: false :: b) n))).
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0. rewrite strictly_positive_0_unique in H0. 
           rewrite H0. now do 2 rewrite mult_list_carry_0.
       - intros [ | b ys] n H0.
         + case a.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f.
               rewrite add_list_carry_ff_f.
               rewrite add_list_carry_ff_f. apply f_equal.
               rewrite IHxs.
               rewrite <- add_list_assoc.
               rewrite <- add_list_assoc.
               cut ((add_list [true] (false :: xs)) = (add_list (true :: xs) [false])). now (intro H1; rewrite H1).
               now rewrite add_list_comm.
               simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
               rewrite IHxs. reflexivity.
               simpl in *; lia.
         + case a, b.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_t_tt_add_list_f_t_tt.
               rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_t_tf_add_list_f_t_tf.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ft_ft_comm.
             now rewrite add_list_comm.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_tt_add_list_ft. reflexivity.
             simpl in *; lia.
           * induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_tf_add_list_ff. reflexivity.
             simpl in *; lia.
Qed.

Lemma mult_list_carry_comm: forall (a b: list bool) n, ((length a) >= n)%nat -> ((length b) >= n)%nat ->
                            mult_list_carry a b n = mult_list_carry b a n.
Proof. intro a.
       induction a as [ | a xs IHxs].
       - intros b n H0 H1. rewrite strictly_positive_0_unique in H0. rewrite H0.
         do 2 rewrite mult_list_carry_0. reflexivity.
       - intros [ | b ys] n H0 H1.
         + rewrite strictly_positive_0_unique in H1. rewrite H1.
           do 2 rewrite mult_list_carry_0. reflexivity.
         + case a, b.
           * simpl.
             induction n.
             do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2.
             rewrite add_list_carry_tf_t.
             rewrite add_list_carry_tf_t. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. 
               now do 2 rewrite add_list_empty_r.
             rewrite mult_list_carry_add_list_t_f.
             rewrite mult_list_carry_add_list_t_f.
             rewrite IHxs.
             rewrite <- add_list_assoc.
             rewrite <- add_list_assoc.
             cut (add_list xs ys = add_list ys xs). now (intro H2 ;rewrite H2).
             now rewrite add_list_comm.
             simpl in *; lia.
             simpl in *; lia.
             simpl in *; lia.
             simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. 
               now rewrite add_list_empty_r.
             rewrite mult_list_carry_add_list_t_f.
             rewrite mult_list_carry_f_f_2.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             simpl in *; lia.
             simpl in *; lia.
           * simpl.
             induction n.
               do 2 rewrite mult_list_carry_0. now rewrite add_list_empty_r.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2.
               rewrite add_list_carry_ff_f. apply f_equal.
             induction n.
               do 2 rewrite mult_list_carry_0. 
               now rewrite add_list_empty_r.
             rewrite mult_list_carry_add_list_t_f.
             rewrite mult_list_carry_f_f_2.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             simpl in *; lia.
             simpl in *; lia.
           * simpl.
             induction n.
               now do 2 rewrite mult_list_carry_0.
               rewrite mult_list_carry_f_f_2.
               rewrite mult_list_carry_f_f_2. apply f_equal.
             induction n.
               now do 2 rewrite mult_list_carry_0. 
             rewrite mult_list_carry_f_f_2.
             rewrite mult_list_carry_f_f_2. apply f_equal.
             rewrite IHxs. reflexivity.
             simpl in *; lia.
             simpl in *; lia.
Qed.

Lemma mult_list_comm: forall (a b: list bool) n, n = (length a) -> (n = length b) -> 
                             (mult_list_native a b) = (mult_list_native b a).
Proof. intros a b n H0 H1.
       unfold mult_list_native. 
       rewrite <- H0, H1.
       apply mult_list_carry_comm; lia.
Qed.

Definition x : list bool := [false; false; true; false; false; true;
   true; true; false; false; true; false; false; false; true; false;
   true; true; false; false; true;false; true; true; true; true; true; true; true; true; true; true; true; true; true; 
   false; false; true; true; true; true; true; true; true].
Definition y : list bool := [false; true; true; true; false; 
  true; false; false; true; true; 
  true; true; true; true; true; true; true; true; true; true; true; false; 
  false; true; true; true; true; true; true; true; true; true; true; false; false; false; true; true; true; true; true; true; true; true].

Compute length x.
Compute length y.


 Compute (false :: mult_list_carry (false :: x) y (length x)).
 Compute (false :: mult_list_carry x y (length x)).

Compute min (length x) (length y).
Compute max (length x) (length y).

Compute mult_list_carry x y (length x).
Compute bvmult_bool x y (length x).

Compute bvmult_bool x y 38.

Compute (bvmult_bool y x 38).

Compute bvmult_bool x (false :: y) (length x) = 
false :: bvmult_bool x y (length x).

Compute mult_list_carry x (false :: y) 7 = 
false :: mult_list_carry x y 6.


Compute add_list (true :: true :: y)
  (false
   :: mult_bool_step (true :: true :: x) (true :: true :: y) 
(true :: true :: and_with_bool x true) 1 (length x)) =
mult_bool_step (true :: true :: true :: x) (true :: true :: y)
  (true
   :: false
      :: true
         :: mult_bool_step_k_h (and_with_bool x true) (and_with_bool (firstn (length x) (true :: x)) true) true
              (-2)) 2 (length x).


Lemma length_ge: forall {A: Type} (b xsa: list A) xa, (length b >= length (xa :: xsa))%nat ->
                 (length b >= length xsa)%nat.
Proof. intros A b.
       induction b as [ | xb xsb IHb ]; intros.
       - simpl in *. lia.
       - simpl in *. lia.
Qed.



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

Lemma add_list_t: forall l, add_list (true :: l) [false] = [true].
Proof. intro l.
       induction l; intros.
       - now compute.
       - case_eq a; intros; now compute.
Qed.


Lemma add_list_f: forall l, add_list (false :: l) [false] = [false].
Proof. intro l.
       induction l; intros.
       - now compute.
       - case_eq a; intros; now compute.
Qed.

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