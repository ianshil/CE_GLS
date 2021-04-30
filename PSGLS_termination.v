Require Import GLS_PSGLS_calcs.
Require Import List.
Export ListNotations.

Require Import genT gen.
Require Import ddT.
Require Import gen_tacs.
Require Import gen_seq.
Require Import List_lemmasT.
Require Import existsT.
Require Import univ_gen_ext.
Require Import GLS_PSGLS_list_lems.
Require Import dd_fc.
Require Import PeanoNat.
Require Import strong_inductionT.
Require Import PSGLS_termination_measure.
Require Import GLS_PSGLS_remove_list.
Require Import GLS_PSGLS_dec.
Require Import Lia.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Definition proj1_sigT2 {A : Type} (P : A -> Type) (e:sigT P) := match e with
                                    | existT _ a b => a
                                    end.

Definition proj2_sigT2 {A : Type} (P : A -> Type) (e : sigT P) :=
  match e return (P (proj1_sigT2 e)) with
  | existT _ a b => b
  end.

Lemma In_InT : forall (A : MPropF V) l, In A l -> InT A l.
Proof.
intros. apply in_splitT in H. destruct H. destruct s. subst. apply InT_or_app. right.
apply InT_eq.
Qed.

Lemma In_InT_pair : forall (A : MPropF V) (n : nat) l, In (A, n) l -> InT (A, n) l.
Proof.
induction l.
- intro. inversion H.
- intro. assert ({(A, n) = a} + {(A, n) <> a}). destruct a.
  destruct (eq_dec_form A m). subst. destruct (eq_dec_nat n n0). subst. auto.
  right. intro. apply n1. inversion H0. auto. right. intro. inversion H0.
  auto. destruct H0. subst. apply InT_eq. apply InT_cons. apply IHl.
  inversion H. exfalso. auto. assumption.
Qed.

Lemma dec_le : forall n m, (n <= m) + ((n <= m) -> False).
Proof.
induction n.
- intro m. left. apply le_0_n.
- intro m. pose (IHn m). destruct s.
  * destruct (eq_dec_nat n m). subst. right. intro. lia. left. lia.
  * right. intro. apply f. lia.
Qed.

Lemma InT_map_iff : forall {A B : Type} (f : A -> B) (l : list A) (y : B),
       (InT y (map f l) -> (existsT2 x : A, (f x = y) * InT x l)) *
       ((existsT2 x : A, (f x = y) * InT x l) -> InT y (map f l)).
Proof.
induction l.
- intros. simpl. split. intro. inversion X. intro. destruct X. destruct p. inversion i.
- simpl. intros. split.
  * intro. inversion X.
    + subst. exists a. split ; [ reflexivity | apply InT_eq].
    + subst. pose (IHl y). destruct p. apply s in X0. destruct X0. destruct p. exists x.
      split. assumption. apply InT_cons. assumption.
  * intro. pose (IHl y). destruct p. clear s. pose (proj2_sigT2 X).
    destruct p. inversion i0. subst. rewrite <- e. rewrite <- H0. apply InT_eq.
    subst. assert (existsT2 x : A, (f x = y) * InT x l). exists (proj1_sigT2 X).
    split ; assumption. apply i in X1. apply InT_cons. assumption.
Qed.

Fixpoint top_imps (l : list (MPropF V)) : list (MPropF V) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => (Imp A B) :: top_imps t
                | _ => top_imps t
              end
end.

Fixpoint pos_top_imps (l : list (MPropF V)) : (list ((MPropF V) * nat)) :=
match l with
  | nil => nil
  | h :: t => match h with
                | Imp A B => (Imp A B, 1) :: (map (fun y => (fst y, S (snd y))) (pos_top_imps t))
                | _ => (map (fun y => (fst y, S  (snd y))) (pos_top_imps t))
              end
end.

Lemma le_False_lt : forall n m, ((n <= m) -> False) -> (m < n).
Proof.
induction n.
- intros. exfalso. apply H. apply le_0_n.
- induction m.
  * intros. lia.
  * intros. apply Lt.lt_n_S. apply IHn. intro. apply H. apply Le.le_n_S. assumption.
Qed.

Lemma top_boxes_nobox_gen_ext : forall l, nobox_gen_ext (top_boxes l) l.
Proof.
induction l.
- simpl. apply univ_gen_ext_nil.
- destruct a ; simpl.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_extra. intro. inversion X. inversion H. assumption.
  * apply univ_gen_ext_cons. assumption.
Qed.

Lemma nobox_gen_ext_top_boxes_identity : forall l0 l1, nobox_gen_ext l0 l1 ->
                                                       is_Boxed_list l0 ->
                                                       (l0 = top_boxes l1).
Proof.
intros l0 l1 X. induction X.
- intros. reflexivity.
- intro. simpl. destruct x.
  * exfalso. pose (H (# v)). assert (In # v (# v :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * exfalso. pose (H (⊥ V)). assert (In (⊥ V) (⊥ V :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * exfalso. pose (H (x1 → x2)). assert (In (x1 → x2) (x1 → x2 :: l)). apply in_eq. apply e in H0.
    destruct H0. inversion H0.
  * assert (l = top_boxes le). apply IHX. intro. intros. apply H. apply in_cons. assumption.
    rewrite H0. reflexivity.
- simpl. destruct x.
  * apply IHX.
  * apply IHX.
  * apply IHX.
  * exfalso. apply p. exists x. reflexivity.
Qed.

Fixpoint flatten_list {A : Type} (l : list (list A)) : list A :=
  match l with
  | [ ] => [ ]
  | h :: t => h ++ (flatten_list t)
  end
.

Lemma InT_flatten_list_InT_elem {A : Type} : forall (l : list (list A)) b,
        InT b (flatten_list l) -> (existsT2 bs, (InT b bs) * (InT bs l)).
Proof.
induction l.
- intros. simpl in X. inversion X.
- intros. simpl in X. apply InT_app_or in X. destruct X.
  * exists a. split ; [assumption | apply InT_eq].
  * pose (IHl b). apply s in i. destruct i. destruct p. exists x. split ; [assumption | apply InT_cons ; assumption].
Qed.

Lemma redundant_flatten_list : forall ls (s : rel (list (MPropF V))), map (fun z : list (MPropF V) * list (MPropF V) => [z;s]) ls =
flatten_list (map (fun y : list (MPropF V) * list (MPropF V) => [[y;s]]) ls).
Proof.
induction ls.
- intros. simpl. reflexivity.
- simpl. intros. rewrite IHls. reflexivity.
Qed.

Lemma InT_trans_flatten_list {A : Type} : forall (l : list (list A)) bs b,
        (InT b bs) -> (InT bs l) -> (InT b (flatten_list l)).
Proof.
induction l.
- intros. inversion X0.
- intros. inversion X0.
  * subst. simpl. apply InT_or_app. auto.
  * subst. simpl. apply InT_or_app. right. pose (IHl bs b X X1) ; assumption.
Qed.

(* In this file we prove that each sequent Γ |- Δ has a derivation (not proof) D in
   PSGLS of maximal height: all derivations in PSGLS of this sequent must have an
   inferior or equal height to that of D.

   This result can be understood as claiming that the proof search defined by PSGLS
   terminates. *)

(* The next lemma claims that for each sequent s there is a derivation of that sequent. *)

Lemma der_s_inhabited : forall s, inhabited (derrec (@PSGLS_rules V) (fun _ => True) s).
Proof.
intros s.
pose (@dpI (rel (list (MPropF V))) (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) s).
assert (H: (fun _ : rel (list (MPropF V)) => True) s). apply I. apply d in H. apply inhabits. assumption.
Qed.

(* The next definition deals with the property of being a derivation D0 of maximal height
   for the sequent s. *)

Definition is_mhd (s: rel (list (MPropF V))) (D0 : derrec (@PSGLS_rules V) (fun _ => True) s): Prop :=
      forall (D1 : derrec (@PSGLS_rules V) (fun _ => True) s), derrec_height D1 <= derrec_height D0.

(* The next lemma is key to the proof of our main theorem: it states that if all the possible
   premises of a sequent S in the calculus PSGLS have a derivation of maximal height, then
   there must be a sequent Maxprem such that it is a premise of S and has the derivation of
   largest height in all premises. 

   To prove this, we first prove that the type of all premises of a sequent S is finite. *)

Definition type_premises_of_S (s : rel (list (MPropF V))) (H : existsT2 prems, PSGLS_rules prems s): Type :=
        { prems & PSGLS_rules prems s }.

(* Lemma finite_Init_premises_of_S : forall (s : rel (list (MPropF V))),
              (forall prems, ((IdPRule prems s) + (IdBRule prems s) + (BotLRule prems s)) -> prems = []).
Proof.
intros s prems RIA. destruct RIA.
- destruct s0 ; inversion i ; auto.
- inversion b. auto.
Qed. *)

(* The next lemma says that given a list and an element, there are only finitely many
   ways to insert this element in a list. *)

Lemma list_of_splits : forall (l : list (MPropF V)), existsT2 listSplits,
                            forall l1 l2, ((l1 ++ l2 = l) <-> In (l1, l2) listSplits).
Proof.
induction l.
- exists [([],[])]. intros. destruct l1. split ; intro. simpl in H. rewrite H. apply in_eq.
  simpl in H. destruct H. inversion H. reflexivity. inversion H. split ; intro.
  simpl in H. inversion H. simpl. inversion H. inversion H0. inversion H0.
- destruct IHl. exists ([([], a :: l)] ++ (map (fun y => (a :: (fst y), snd y)) x)).
  intros. split ; intro.
  * apply in_or_app. destruct l1. simpl. left. left. simpl in H. rewrite H.
    reflexivity. simpl in H. inversion H. subst. right. pose (i l1 l2). destruct i0.
    assert (l1 ++ l2 = l1 ++ l2). reflexivity. apply H0 in H2.
    pose (in_map (fun y : list (MPropF V) * list (MPropF V) => (a :: fst y, snd y)) x (l1, l2) H2).
    simpl in i. assumption.
  * simpl in H. destruct H. inversion H. simpl. reflexivity. rewrite in_map_iff in H.
    destruct H. destruct H. inversion H. subst. simpl. pose (i (fst x0) (snd x0)).
    destruct i0. assert ((fst x0, snd x0) = x0). destruct x0. simpl. reflexivity.
    rewrite H3 in H2. apply H2 in H0. rewrite H0. reflexivity.
Qed.

Definition listInserts l (A : MPropF V) := map (fun y => (fst y) ++ A :: (snd y)) (proj1_sigT2 (list_of_splits l)).

(* The next two lemmas make sure that the definition listInserts indeed captures the intended
   list. *)

Lemma listInserts_In : forall l (A: MPropF V) l1 l2, ((l1 ++ l2 = l) -> In (l1 ++ A :: l2) (listInserts l A)).
Proof.
intros. unfold listInserts. assert (In (l1, l2) (proj1_sigT2 (list_of_splits l))). destruct (list_of_splits l).
simpl. pose (i l1 l2). apply i0. assumption.
pose (in_map (fun y : list (MPropF V) * list (MPropF V) => fst y ++ A :: snd y) (proj1_sigT2 (list_of_splits l)) (l1, l2) H0).
simpl in i. assumption.
Qed.

Lemma In_listInserts : forall l (A: MPropF V) l0, In l0 (listInserts l A) ->
                            (exists l1 l2, prod (l1 ++ l2 = l) (l1 ++ A :: l2 = l0)).
Proof.
intros. unfold listInserts in H. destruct (list_of_splits l). simpl in H. rewrite in_map_iff in H.
destruct H. destruct H. subst. exists (fst x0). exists (snd x0). split. apply i.
destruct x0. simpl. assumption. reflexivity.
Qed.

(* The definitions below allow you to create the list of all sequents given two lists and a
   formula to insert in one of them. *)

Definition listInsertsR_Seqs (Γ Δ : list (MPropF V)) (A : MPropF V) := map (fun y => (y, Δ)) (listInserts Γ A).

Definition listInsertsL_Seqs (Γ Δ : list (MPropF V)) (A : MPropF V) := map (fun y => (Γ, y)) (listInserts Δ A).

(* The next definition allows one to create all sequents *)

Definition listInsertsRL_Seqs (Γ Δ : list (MPropF V)) (A B : MPropF V) :=
                  flatten_list (map (fun z => (map (fun y => (z, y)) (listInserts Δ B))) (listInserts Γ A)).






(* Now we can prove that a sequent has only finitely many potential premises via the ImpR rules.

   The next definition simply takes a list of formulae l and a sequent s. It outputs a list of sequents.
   These sequents are generated when there is an implication (Imp A B) encountered in l. With such an
   implication, the function will stack the list of all insertions of A on the left of s and of B on
   the right of s (roughly: in fact you need to destroy all such implications on the right to get an ImpRRule
   premise), and then continues computing on the rest of l. *)

Fixpoint remove_nth (n: nat) (A : MPropF V) l:=
    match n with
      | 0 => l
      | 1 => match l with
               | [] => []
               | B::tl => if (eq_dec_form A B) then tl else B:: tl
             end
      | S m => match l with
                 | [] => []
                 | B::tl => B::(remove_nth m A tl)
               end
      end.

Fixpoint nth_split (n : nat) (l : list (MPropF V)) : (list (MPropF V) * list (MPropF V)) :=
    match n with
      | 0 => ([], l)
      | 1 => match l with
               | [] => ([], [])
               | B::tl => ([B] , tl)
             end
      | S m => match l with
                 | [] => ([], [])
                 | B::tl => (B :: (fst (nth_split m tl)), snd (nth_split m tl))
               end
      end.

Fixpoint prems_Imp_R (l : list ((MPropF V) * nat)) (s : rel (list (MPropF V))) : list (rel (list (MPropF V))) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
                    | 0 => prems_Imp_R t s
                    | S m => match C with
                                | Imp A B => (listInsertsR_Seqs (fst s)
                                               ((fst (nth_split m (remove_nth (S m) C (snd s)))) ++
                                               B :: (snd (nth_split m (remove_nth (S m) C (snd s)))))
                                               A)
                                             ++ (prems_Imp_R t s)
                                | _ => prems_Imp_R t s
                                end
                   end
end.

Lemma nth_split_length : forall (l0 l1 : list (MPropF V)), (nth_split (length l0) (l0 ++ l1)) = (l0, l1).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. pose (IHl0 l1). simpl (length (a :: l0)). simpl ((a :: l0) ++ l1).
  simpl. destruct l0.
  * simpl. reflexivity.
  * assert (match length (m :: l0) with
| 0 => ([a], (m :: l0) ++ l1)
| S _ =>
    (a :: fst (nth_split (length (m :: l0)) ((m :: l0) ++ l1)),
    snd (nth_split (length (m :: l0)) ((m :: l0) ++ l1)))
end = (a :: fst (nth_split (length (m :: l0)) ((m :: l0) ++ l1)),
    snd (nth_split (length (m :: l0)) ((m :: l0) ++ l1)))). reflexivity. rewrite H.
clear H. rewrite e. simpl. reflexivity.
Qed.

Lemma nth_split_idL : forall (l0 l1 : list (MPropF V)), l0 = fst (nth_split (length l0) (l0 ++ l1)).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. simpl (length (a :: l0)). pose (IHl0 l1). assert (fst (nth_split (S (length l0)) ((a :: l0) ++ l1)) =
  a :: fst (nth_split (length l0) (l0 ++ l1))). simpl. destruct l0. simpl. reflexivity.
  simpl. reflexivity. rewrite H. rewrite <- e. reflexivity.
Qed.

Lemma nth_split_idR : forall (l0 l1 : list (MPropF V)), l1 = snd (nth_split (length l0) (l0 ++ l1)).
Proof.
induction l0.
- intros. simpl. reflexivity.
- intros. simpl (length (a :: l0)). pose (IHl0 l1). rewrite e. destruct l0.
  * simpl. reflexivity.
  * simpl (length (m :: l0)). simpl (S (S (length l0))).
    simpl (length (m :: l0)) in e. rewrite <- e.
    assert ((S (S (length l0))) = (length (a :: m :: l0))). simpl. reflexivity.
    rewrite H. rewrite nth_split_length. simpl. reflexivity.
Qed.

Lemma nth_split_length_id : forall (l0 l1 : list (MPropF V)) n, (length l0 = n) ->
                                (fst (nth_split n (l0 ++ l1)) = l0 /\
                                snd (nth_split n (l0 ++ l1)) = l1).
Proof.
induction l0.
- intros. simpl. split. simpl in H. subst. simpl. reflexivity. simpl in H. subst. simpl. reflexivity.
- intros. simpl in H. subst. split.
  * assert (J1:length l0 = length l0). reflexivity. pose (@IHl0 l1 (length l0) J1).
    destruct a0. simpl. destruct l0. simpl. reflexivity. simpl. rewrite <- H.
    simpl. reflexivity.
  * assert (J1:length l0 = length l0). reflexivity. pose (@IHl0 l1 (length l0) J1).
    destruct a0. rewrite <- H0. simpl ((a :: l0) ++ snd (nth_split (length l0) (l0 ++ l1))).
    assert ((nth_split (S (length l0)) (a :: l0 ++ snd (nth_split (length l0) (l0 ++ l1))) =
    (a :: l0 ,snd (nth_split (length l0) (l0 ++ l1))))).
    pose (nth_split_length (a :: l0) (snd (nth_split (length l0) (l0 ++ l1)))). apply e.
    rewrite H1. simpl. reflexivity.
Qed.


Lemma In_pos_top_imps_0_False : forall l (A : MPropF V), In (A, 0) (pos_top_imps l) -> False.
Proof.
- induction l.
  * intros. inversion H.
  * intros. simpl in H. destruct a.
    + simpl in H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
      destruct p. destruct x. inversion e.
    + simpl in H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
      destruct p. destruct x. inversion e.
    + simpl in H. destruct H. inversion H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
      destruct p. destruct x. inversion e.
    + simpl in H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
      destruct p. destruct x. inversion e.
Qed.

Lemma In_pos_top_imps_imp : forall l (A : MPropF V) n, In (A, n) (pos_top_imps l) -> (existsT2 C D, A = Imp C D).
Proof.
induction l ; intros.
- simpl in H. inversion H.
- simpl in H. destruct a ; try apply IHl in H. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
  destruct p. inversion e. destruct x. subst. apply InT_In in i. apply IHl in i. assumption.
  apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
  destruct p. inversion e. destruct x. subst. apply InT_In in i. apply IHl in i. assumption.
  apply In_InT_pair in H. inversion H. subst. inversion H1. exists a1. exists a2. reflexivity.
  subst. apply InT_map_iff in H1. destruct H1. destruct p. destruct x. simpl in e. inversion e.
  subst. apply InT_In in i. apply IHl in i. assumption.
  apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
  destruct p. inversion e. destruct x. subst. apply InT_In in i. apply IHl in i. assumption.
Qed.

Lemma In_pos_top_imps_In_l : forall l (A : MPropF V) n, In (A, n) (pos_top_imps l) -> In A l.
Proof.
induction l.
- intros. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply in_cons. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e. subst. apply InT_In in i. apply IHl in i.
    assumption.
  * apply in_cons. apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e. subst. apply InT_In in i. apply IHl in i.
    assumption.
  * inversion H.
    + inversion H0. subst. apply in_eq.
    + apply in_cons. apply In_InT_pair in H0. apply InT_map_iff in H0. destruct H0.
      destruct p. destruct x. inversion e. subst. apply InT_In in i. apply IHl in i.
      assumption.
  *  apply In_InT_pair in H. apply InT_map_iff in H. destruct H.
    destruct p. destruct x. inversion e. subst. apply InT_In in i. apply IHl in i.
    apply in_cons. assumption.
Qed.

Lemma effective_remove_nth : forall A l0 l1, ((remove_nth (S (length l0)) A (l0 ++ A :: l1)) = l0 ++ l1).
Proof.
induction l0.
- intros. simpl. destruct (eq_dec_form A A). reflexivity. exfalso. auto.
- intros. simpl (S (length (a :: l0))). repeat rewrite <- app_assoc. simpl ((a :: l0) ++ A :: l1).
  pose (IHl0 l1). simpl ((a :: l0) ++ l1). rewrite <- e. simpl. reflexivity.
Qed.

Lemma In_pos_top_imps_split_l : forall l (A : MPropF V) n, In (A, S n) (pos_top_imps l) -> 
          existsT2 l0 l1, (l = l0 ++ A :: l1) *
                          (length l0 = n) *
                          (l0 = fst (nth_split n (remove_nth (S n) A l))) *
                          (l1 = snd (nth_split n (remove_nth (S n) A l))).
Proof.
induction l.
- intros. simpl. exfalso. simpl in H. destruct H.
- intros. simpl in H. destruct a.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_imps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (# v :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (# v :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    # v :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H0. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (# v :: x))). simpl. reflexivity.
    rewrite H. assert ((# v :: x ++ A :: x0) = ((# v :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (# v :: x) x0). simpl (length (# v :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_imps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (⊥ V :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (⊥ V :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      ⊥ V :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (⊥ V :: x))). simpl. reflexivity.
    rewrite H0. assert ((⊥ V :: x ++ A :: x0) = ((⊥ V :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (⊥ V :: x) x0). simpl (length (⊥ V :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (⊥ V :: x))). simpl. reflexivity.
    rewrite H. assert ((⊥ V :: x ++ A :: x0) = ((⊥ V :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (⊥ V :: x) x0). simpl (length (⊥ V :: x)) in e2.
    rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. inversion H.
    + inversion H1. subst. exists []. exists l. repeat split. simpl.
      destruct (eq_dec_form (a1 → a2) (a1 → a2)). reflexivity. exfalso. auto.
    + subst. apply InT_map_iff in H1. destruct H1. destruct p.
      destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
      apply InT_In in i. apply In_pos_top_imps_0_False in i. assumption.
      apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
      subst. exists (a1 → a2 :: x). exists x0. repeat split.
      rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
      assert (fst (a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
      a1 → a2 :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
      assert (S (S (length x)) = S (length (a1 → a2 :: x))). simpl. reflexivity.
      rewrite H1. assert ((a1 → a2 :: x ++ A :: x0) = ((a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H2. clear H2. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idL (a1 → a2 :: x) x0). simpl (length (a1 → a2 :: x)) in e2.
      rewrite <- e2. reflexivity.
      rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
      assert (S (S (length x)) = S (length (a1 → a2 :: x))). simpl. reflexivity.
      rewrite H0. assert ((a1 → a2 :: x ++ A :: x0) = ((a1 → a2 :: x) ++ A :: x0)). simpl. reflexivity.
      rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
      pose (nth_split_idR (a1 → a2 :: x) x0). simpl (length (a1 → a2 :: x)) in e2.
      rewrite <- e2. reflexivity.
  * apply In_InT_pair in H. apply InT_map_iff in H. destruct H. destruct p.
    destruct x. simpl in e. inversion e. subst. destruct n. exfalso.
    apply InT_In in i. apply In_pos_top_imps_0_False in i. assumption.
    apply InT_In in i. pose (IHl A n i). repeat destruct s. repeat destruct p.
    subst. exists (Box a :: x). exists x0. repeat split.
    rewrite effective_remove_nth in e1. rewrite effective_remove_nth in e0.
    assert (fst (Box a :: fst (nth_split (S (length x)) (x ++ x0)), snd (nth_split (S (length x)) (x ++ x0))) =
    Box a :: fst (nth_split (S (length x)) (x ++ x0))). simpl. reflexivity.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H0. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H1. clear H0. clear H1. rewrite effective_remove_nth.
    pose (nth_split_idL (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
    rewrite effective_remove_nth in e0. rewrite effective_remove_nth in e1.
    assert (S (S (length x)) = S (length (Box a :: x))). simpl. reflexivity.
    rewrite H. assert ((Box a :: x ++ A :: x0) = ((Box a :: x) ++ A :: x0)). simpl. reflexivity.
    rewrite H0. clear H. clear H0. rewrite effective_remove_nth.
    pose (nth_split_idR (Box a :: x) x0). simpl (length (Box a :: x)) in e2.
    rewrite <- e2. reflexivity.
Qed.

Lemma In_l_imp_In_pos_top_imps : forall l (A B : MPropF V), In (Imp A B) l ->
                                    existsT2 n, In ((Imp A B), n) (pos_top_imps l).
Proof.
induction l.
- intros. simpl in H. destruct H.
- intros. apply In_InT in H. inversion H.
  * subst. exists 1. simpl. left. reflexivity.
  * destruct a.
    + subst. apply InT_In in H1. apply IHl in H1. destruct H1. exists (S x). simpl.
      apply InT_In. apply InT_map_iff. exists (A → B, x). simpl. split ; auto.
      apply In_InT_pair. assumption.
    + subst. apply InT_In in H1. apply IHl in H1. destruct H1. exists (S x). simpl.
      apply InT_In. apply InT_map_iff. exists (A → B, x). simpl. split ; auto.
      apply In_InT_pair. assumption.
    + subst. apply InT_In in H1. apply IHl in H1. destruct H1. exists (S x). simpl.
      right. apply InT_In. apply InT_map_iff. exists (A → B, x). simpl. split ; auto.
      apply In_InT_pair. assumption.
    + subst. apply InT_In in H1. apply IHl in H1. destruct H1. exists (S x). simpl.
      apply InT_In. apply InT_map_iff. exists (A → B, x). simpl. split ; auto.
      apply In_InT_pair. assumption.
Qed.

Lemma Good_pos_in_pos_top_imps : forall A B Δ0 Δ1,
              In (A → B, S (length Δ0)) (pos_top_imps (Δ0 ++ A → B :: Δ1)).
Proof.
induction Δ0.
- intros. simpl. auto.
- intros. destruct a.
  * simpl. apply InT_In. apply InT_map_iff. exists (A → B, S (length Δ0)).
    split. simpl. reflexivity. apply In_InT_pair. apply IHΔ0.
  * simpl. apply InT_In. apply InT_map_iff. exists (A → B, S (length Δ0)).
    split. simpl. reflexivity. apply In_InT_pair. apply IHΔ0.
  * simpl. right. apply InT_In. apply InT_map_iff. exists (A → B, S (length Δ0)).
    split. simpl. reflexivity. apply In_InT_pair. apply IHΔ0.
  * simpl. apply InT_In. apply InT_map_iff. exists (A → B, S (length Δ0)).
    split. simpl. reflexivity. apply In_InT_pair. apply IHΔ0.
Qed.

(* From there I can show that given a specific (Imp A B) on the right of a sequent S,
   there is only finitely many premises via ImpR applied on this implication. But I
   need to do it for all implications on the right of this sequent. *)

Lemma ImpR_help01 : forall prem s l, InT prem (prems_Imp_R l s) ->
                  (existsT2 n A B Γ0 Γ1 Δ0 Δ1,
                        (In ((Imp A B), S n) l) *
                        (prem = (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)) *
                        (Γ0 ++ Γ1 = fst s) *
                        (Δ0 = (fst (nth_split n (remove_nth (S n) (Imp A B) (snd s))))) *
                        (Δ1 = (snd (nth_split n (remove_nth (S n) (Imp A B) (snd s)))))).
Proof.
intros prem s. destruct s. destruct prem. induction l3 ; intros.
- simpl in X. inversion X.
- destruct a. destruct m.
  * simpl in X. destruct n.
    + pose (IHl3 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption.
    + pose (IHl3 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption.
  * simpl in X. destruct n.
    + pose (IHl3 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption.
    + pose (IHl3 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption.
  * destruct n.
    + pose (IHl3 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption.
    + apply InT_app_or in X. destruct X.
      { simpl (fst (l, l0)) in i. simpl (snd (l, l0)) in i.
        unfold listInsertsR_Seqs in i. apply InT_map_iff in i. destruct i.
        destruct p. subst. unfold listInserts in i. apply InT_map_iff in i. destruct i.
        destruct p. destruct x0. subst. destruct (list_of_splits l). simpl in i. exists n.
        exists m1. exists m2. exists l4. exists l5. simpl (snd (l, l0)).
        simpl (fst (l, l0)).
        exists (fst (nth_split n (remove_nth (S n) (m1 → m2) l0))).
        exists (snd (nth_split n (remove_nth (S n) (m1 → m2) l0))).
        repeat split ; try auto. apply in_eq. rewrite i0. apply InT_In. assumption. }
      { pose (IHl3 i). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption. }
  * simpl in X. destruct n.
    + pose (IHl3 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption.
    + pose (IHl3 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. repeat split ; try auto. apply in_cons. assumption.
Qed.

Lemma ImpR_help1 : forall prem s, InT prem (prems_Imp_R (pos_top_imps (snd s)) s) -> ImpRRule [prem] s.
Proof.
intros. pose (ImpR_help01 _ _ X). destruct s0. destruct s.
destruct s0. repeat destruct s. repeat destruct p. subst. simpl in e1. subst.
simpl (snd (x2 ++ x3, l0)) in i. simpl (snd (x2 ++ x3, l0)) in X.
simpl (snd (x2 ++ x3, l0)). apply In_pos_top_imps_split_l in i. destruct i. destruct s. repeat destruct p.
subst. rewrite <- e. rewrite effective_remove_nth. rewrite <- nth_split_idL.
apply ImpRRule_I.
Qed.

Lemma ImpR_help002 : forall Γ0 Γ1 Δ0 Δ1 A B,
           InT (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (listInsertsR_Seqs (Γ0 ++ Γ1) (Δ0 ++ B :: Δ1) A).
Proof.
intros. unfold listInsertsR_Seqs. apply InT_map_iff. exists (Γ0 ++ A :: Γ1). split.
reflexivity. unfold listInserts. apply InT_map_iff. exists (Γ0, Γ1). simpl. split.
reflexivity. destruct (list_of_splits (Γ0 ++ Γ1)). simpl. pose (i Γ0 Γ1).
apply In_InT_seqs. apply i0. reflexivity.
Qed.

Lemma ImpR_help02 : forall Γ0 Γ1 Δ0 Δ1 A B l n,
                                ImpRRule [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)] (Γ0 ++ Γ1, Δ0 ++ (Imp A B) :: Δ1) ->
                                (length Δ0 = n) ->
                                (In ((Imp A B), S n) l) ->
                                InT (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (prems_Imp_R l (Γ0 ++ Γ1, Δ0 ++ (Imp A B) :: Δ1)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  * apply In_InT_pair in H1. inversion H1. subst. inversion H3. subst. apply InT_In in H3.
    assert (J1: length Δ0 = length Δ0). reflexivity.
    pose (IHl _ H J1 H3). simpl. destruct n0. assumption. assumption.
  * apply In_InT_pair in H1. inversion H1. subst. inversion H3. subst. apply InT_In in H3.
    assert (J1: length Δ0 = length Δ0). reflexivity.
    pose (IHl _ H J1 H3). simpl. destruct n0. assumption. assumption.
  * apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst. destruct Δ0.
      { simpl. pose (ImpR_help002 Γ0 Γ1 [] Δ1 A B). simpl in i. destruct (eq_dec_form (A → B) (A → B)).
        apply InT_or_app. auto. exfalso. auto. }
      { unfold prems_Imp_R. apply InT_or_app. left.
        assert ((remove_nth (S (length (m :: Δ0))) (A → B) (snd (Γ0 ++ Γ1, (m :: Δ0) ++ A → B :: Δ1))) =
        (m :: Δ0) ++ Δ1). simpl (snd (Γ0 ++ Γ1, (m :: Δ0) ++ A → B :: Δ1)).
        pose (effective_remove_nth (A → B) (m :: Δ0) Δ1). assumption.
        rewrite H0.
        assert (fst (nth_split (length (m :: Δ0)) ((m :: Δ0) ++ Δ1)) = (m :: Δ0) /\
        snd (nth_split (length (m :: Δ0)) ((m :: Δ0) ++ Δ1)) = Δ1). apply nth_split_length_id.
        reflexivity. destruct H2. rewrite H2. rewrite H4. apply ImpR_help002. }
    + subst. assert (J1: (length Δ0) = (length Δ0)). reflexivity. apply InT_In in H3.
      pose (IHl (length Δ0) H J1 H3). simpl. destruct n0. assumption. apply InT_or_app. auto.
  * apply In_InT_pair in H1. inversion H1. subst. inversion H3. subst. apply InT_In in H3.
    assert (J1: length Δ0 = length Δ0). reflexivity.
    pose (IHl _ H J1 H3). simpl. destruct n0. assumption. assumption.
Qed.

Lemma ImpR_help2 : forall prem s, ImpRRule [prem] s -> InT prem (prems_Imp_R (pos_top_imps (snd s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@ImpR_help02 Γ0 Γ1 Δ0 Δ1 A B (pos_top_imps (Δ0 ++ A → B :: Δ1)) (length Δ0)). apply i ; try assumption.
reflexivity. apply Good_pos_in_pos_top_imps.
Qed.

Lemma finite_ImpR_premises_of_S : forall (s : rel (list (MPropF V))), existsT2 listImpRprems,
              (forall prems, ((ImpRRule prems s) -> (InT prems listImpRprems)) *
                             ((InT prems listImpRprems) -> (ImpRRule prems s))).
Proof.
intro s. destruct s.
exists (map (fun y => [y]) (prems_Imp_R (pos_top_imps l0) (l,l0))).
intros. split ; intro.
- inversion H. subst. apply InT_map_iff.
  exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). split. reflexivity.
  pose (@ImpR_help2 (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1)). simpl in i. apply i.
  assumption.
- apply InT_map_iff in X. destruct X. destruct p. subst. apply ImpR_help1. simpl. assumption.
Qed.






(* Then, we turn to the case of the ImpL rule. *)

Fixpoint prems_Imp_L (l : list ((MPropF V) * nat)) (s : rel (list (MPropF V))) : list (list (rel (list (MPropF V)))) :=
match l with
  | nil => nil
  | (C, n) :: t => match n with
      | 0 => prems_Imp_L t s
      | S m => match C with
           | Imp A B => flatten_list
                        (map (fun y => map (fun z => [z; y])
                        (listInsertsL_Seqs ((fst (nth_split m (remove_nth (S m) C (fst s)))) ++
                        (snd (nth_split m (remove_nth (S m) C (fst s))))) (snd s) A))
                        [(((fst (nth_split m (remove_nth (S m) C (fst s)))) ++
                        B :: (snd (nth_split m (remove_nth (S m) C (fst s))))), (snd s))])
                        ++ (prems_Imp_L t s)
           | _ => prems_Imp_L t s
           end
      end
end.

Lemma ImpL_help002 : forall Γ0 Γ1 Δ0 Δ1 A B,
           InT [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
               (flatten_list (map (fun y : list (MPropF V) * list (MPropF V) => map
               (fun z : list (MPropF V) * list (MPropF V) => [y; z]) [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
               (listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A)))
              .
Proof.
intros.
pose (@InT_trans_flatten_list _ (map (fun y : list (MPropF V) * list (MPropF V) => map
(fun z : list (MPropF V) * list (MPropF V) => [y; z]) [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
(listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A))
(map (fun z : list (MPropF V) * list (MPropF V) => [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); z])
[(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]).
apply i ; clear i.
- pose (InT_map_iff (fun z : list (MPropF V) * list (MPropF V) => [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); z]) [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
  [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]).
  destruct p. clear s. apply i. exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). split. reflexivity. apply InT_eq.
- pose (InT_map_iff (fun y : list (MPropF V) * list (MPropF V) =>
  map (fun z : list (MPropF V) * list (MPropF V) => [y; z]) [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])
  (listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A) (map (fun z : list (MPropF V) * list (MPropF V) => [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); z])
  [(Γ0 ++ B :: Γ1, Δ0 ++ Δ1)])).
  destruct p. apply i. clear i. clear s. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1). split. reflexivity.
  unfold listInsertsL_Seqs.
  pose (InT_map_iff (fun y : list (MPropF V) => (Γ0 ++ Γ1, y)) (listInserts (Δ0 ++ Δ1) A) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
  destruct p. apply i. clear s. clear i. exists (Δ0 ++ A :: Δ1). split. reflexivity.
  unfold listInserts.
  pose (InT_map_iff (fun y : list (MPropF V) * list (MPropF V) => fst y ++ A :: snd y)
  (proj1_sigT2 (list_of_splits (Δ0 ++ Δ1))) (Δ0 ++ A :: Δ1)). destruct p. clear s.
  apply i. clear i. exists (Δ0,Δ1). simpl. split. reflexivity. destruct (list_of_splits (Δ0 ++ Δ1)).
  simpl. pose (i Δ0 Δ1). apply In_InT_seqs. rewrite <- i0. reflexivity.
Qed.

Lemma ImpL_help02 : forall Γ0 Γ1 Δ0 Δ1 A B l n,
            ImpLRule [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)] (Γ0 ++ (Imp A B) :: Γ1, Δ0 ++ Δ1) ->
            (length Γ0 = n) ->
            (In ((Imp A B), S n) l) ->
            InT [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)] (prems_Imp_L l (Γ0 ++ (Imp A B) :: Γ1, Δ0 ++ Δ1)).
Proof.
induction l ; intros.
- inversion H1.
- destruct a. destruct m.
  * subst. apply In_InT_pair in H1. inversion H1. subst. inversion H2. subst. apply InT_In in H2.
    assert (J1: length Γ0 = length Γ0). reflexivity.
    pose (IHl _ H J1 H2). simpl. destruct n0. assumption. assumption.
  * subst. apply In_InT_pair in H1. inversion H1. subst. inversion H2. subst. apply InT_In in H2.
    assert (J1: length Γ0 = length Γ0). reflexivity.
    pose (IHl _ H J1 H2). simpl. destruct n0. assumption. assumption.
  * apply In_InT_pair in H1. inversion H1.
    + subst. inversion H3. subst.
      pose (ImpL_help002 Γ0 Γ1 Δ0 Δ1 A B). simpl in i.
      apply InT_or_app. left.
      apply InT_trans_flatten_list with (bs:=(flatten_list
      (map (fun y : list (MPropF V) * list (MPropF V) => [[y; (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]])
         (listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A)))). assumption. apply InT_map_iff.
      exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). split.
      destruct (eq_dec_form (A → B) (A → B)).
      apply InT_flatten_list_InT_elem in i. destruct i. destruct p.
      assert ((listInsertsL_Seqs (fst
      (nth_split (length Γ0) (remove_nth (S (length Γ0)) (A → B) (fst (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)))) ++
      snd
      (nth_split (length Γ0) (remove_nth (S (length Γ0)) (A → B) (fst (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)))))
      (snd (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)) A) = (listInsertsL_Seqs (Γ0 ++ Γ1) (Δ0 ++ Δ1) A)).
      simpl (snd (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)).
      simpl (fst (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)). repeat rewrite effective_remove_nth.
      assert (length Γ0 = length Γ0). reflexivity.
      pose (@nth_split_length_id Γ0 Γ1 (length Γ0) H0). destruct a. rewrite H2. rewrite H4.
      reflexivity. rewrite H0.
      apply redundant_flatten_list. exfalso. auto.
      destruct (eq_dec_form (A → B) (A → B)). simpl (snd (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)).
      simpl (fst (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)). repeat rewrite effective_remove_nth.
      assert (length Γ0 = length Γ0). reflexivity.
      pose (@nth_split_length_id Γ0 Γ1 (length Γ0) H0). destruct a. rewrite H2. rewrite H4.
      apply InT_eq. exfalso. auto.
    + subst. assert (J1: (length Γ0) = (length Γ0)). reflexivity. apply InT_In in H3.
      pose (IHl (length Γ0) H J1 H3). simpl. destruct n0. assumption. apply InT_or_app. auto.
  * subst. apply In_InT_pair in H1. inversion H1. subst. inversion H2. subst. apply InT_In in H2.
    assert (J1: length Γ0 = length Γ0). reflexivity.
    pose (IHl _ H J1 H2). simpl. destruct n0. assumption. assumption.
Qed.

Lemma ImpL_help2 : forall prem1 prem2 s, ImpLRule [prem1; prem2] s ->
                      InT [prem1; prem2] (prems_Imp_L (pos_top_imps (fst s)) s).
Proof.
intros. inversion H. subst. simpl.
pose (@ImpL_help02 Γ0 Γ1 Δ0 Δ1 A B (pos_top_imps (Γ0 ++ (Imp A B) :: Γ1)) (length Γ0)). apply i ; try assumption.
reflexivity. apply Good_pos_in_pos_top_imps.
Qed.

Lemma ImpL_help01 : forall prems s l, InT prems (prems_Imp_L l s) ->
                  (existsT2 n prem1 prem2 A B Γ0 Γ1 Δ0 Δ1,
                        (prems = [prem1; prem2]) *
                        (In ((Imp A B), S n) l) *
                        (prem1 = (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) *
                        (prem2 = (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) *
                        (Δ0 ++ Δ1 = snd s) *
                        (Γ0 = (fst (nth_split n (remove_nth (S n) (Imp A B) (fst s))))) *
                        (Γ1 = (snd (nth_split n (remove_nth (S n) (Imp A B) (fst s)))))).
Proof.
intros prems s. destruct s. induction l1 ; intros.
- simpl in X. inversion X.
- simpl (fst (l, l0)). destruct a. destruct m.
  * simpl in X. destruct n.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try auto. apply in_cons. assumption.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try auto. apply in_cons. assumption.
  * simpl in X. destruct n.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try auto. apply in_cons. assumption.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try auto. apply in_cons. assumption.
  * destruct n.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try auto. apply in_cons. assumption.
    + apply InT_app_or in X. destruct X.
      { simpl (fst (l, l0)) in i. simpl (snd (l, l0)) in i.
        apply InT_flatten_list_InT_elem in i. destruct i. destruct p.
        apply InT_map_iff in i0. destruct i0. destruct p.
        inversion i0. subst. apply InT_map_iff in i. destruct i.
        destruct p. unfold listInsertsL_Seqs in i. apply InT_map_iff in i.
        destruct i. destruct p. subst. unfold listInserts in i. apply InT_map_iff in i. destruct i.
        destruct p. destruct x. subst. destruct (list_of_splits l0). simpl in i. exists n.
        simpl (fst (l2, l3)). simpl (snd (l2, l3)).
        exists (fst (nth_split n (remove_nth (S n) (m1 → m2) l)) ++
        snd (nth_split n (remove_nth (S n) (m1 → m2) l)), l2 ++ m1 :: l3).
        exists (fst
          (nth_split n
             match n with
             | 0 =>
                 match l with
                 | [] => []
                 | B0 :: tl => if eq_dec_form (m1 → m2) B0 then tl else B0 :: tl
                 end
             | S _ => match l with
                      | [] => []
                      | B0 :: tl => B0 :: remove_nth n (m1 → m2) tl
                      end
             end) ++
        m2
        :: snd
             (nth_split n
                match n with
                | 0 =>
                    match l with
                    | [] => []
                    | B0 :: tl => if eq_dec_form (m1 → m2) B0 then tl else B0 :: tl
                    end
                | S _ => match l with
                         | [] => []
                         | B0 :: tl => B0 :: remove_nth n (m1 → m2) tl
                         end
                end), l0).
        exists m1. exists m2. exists (fst (nth_split n (remove_nth (S n) (m1 → m2) l))).
        exists (snd (nth_split n (remove_nth (S n) (m1 → m2) l))).
        exists l2. exists l3. simpl (snd (l, l0)). simpl (fst (l, l0)).
        repeat split ; try auto. apply in_eq. simpl. assert (l2 ++ l3 = l0). rewrite i1. apply InT_In.
        assumption. rewrite <- H. reflexivity. rewrite i1. apply InT_In. assumption. subst. inversion H0. }
      { pose (IHl1 i). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
        exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
        repeat split ; try auto. apply in_cons. assumption. }
  * simpl in X. destruct n.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try auto. apply in_cons. assumption.
    + pose (IHl1 X). repeat destruct s. repeat destruct p. exists x. exists x0. exists x1.
      exists x2. exists x3. exists x4. exists x5. exists x6. exists x7.
      repeat split ; try auto. apply in_cons. assumption.
Qed.

Lemma ImpL_help1 : forall prems s, InT prems (prems_Imp_L (pos_top_imps (fst s)) s) ->
                                         ImpLRule prems s.
Proof.
intros. pose (@ImpL_help01 _ _ _ X). repeat destruct s0. destruct s. simpl in X.
repeat destruct p. subst. simpl in e1. simpl in i. subst. simpl (fst (l, x6 ++ x7)).
simpl (fst (l, x6 ++ x7)) in X. apply In_pos_top_imps_split_l in i.
destruct i. destruct s. repeat destruct p.
subst. rewrite <- e. rewrite <- e0. apply ImpLRule_I.
Qed.

Lemma finite_ImpL_premises_of_S : forall (s : rel (list (MPropF V))), existsT2 listImpLprems,
              (forall prems, ((ImpLRule prems s) -> (InT prems listImpLprems)) *
                             ((InT prems listImpLprems) -> (ImpLRule prems s))).
Proof.
intros. destruct s.
exists (prems_Imp_L (pos_top_imps l) (l,l0)).
intros. split ; intro.
- inversion H. subst.
  pose (@ImpL_help2 (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)). apply i.
  assumption.
- pose (@ImpL_help1 prems (l, l0)). apply i. assumption.
Qed.




(* Now let's tackle the GLR rule. *)

Fixpoint prems_Box_R (l : list (MPropF V)) (s : rel (list (MPropF V))) : list (list (rel (list (MPropF V)))) :=
match l with
  | nil => nil
  | h :: t => match h with
              | Box A => [((XBoxed_list (top_boxes (fst s))) ++ [Box A], [A])] :: (prems_Box_R t s)
              | _ => prems_Box_R t s
              end
end.

 Lemma GLR_help01 : forall prems s (l : list (MPropF V)), InT prems (prems_Box_R l s) ->
                  (existsT2 (A : MPropF V),
                        (In (Box A) l) *
                        (prems = [(XBoxed_list (top_boxes (fst s)) ++ [Box A], [A])])).
Proof.
intros prems s. destruct s. induction l1 ; intros.
- simpl in X. inversion X.
- simpl in X. destruct a.
  * apply IHl1 in X. destruct X. repeat destruct s. repeat destruct p. subst.
    exists x. repeat split ; try auto ; try apply in_cons ; try assumption.
  * apply IHl1 in X. destruct X. repeat destruct s. repeat destruct p. subst.
    exists x. repeat split ; try auto ; try apply in_cons ; try assumption.
  * apply IHl1 in X. destruct X. repeat destruct s. repeat destruct p. subst.
    exists x. repeat split ; try auto ; try apply in_cons ; try assumption.
  * inversion X.
    + subst. exists a. repeat split ; try auto ; try apply in_eq.
    + apply IHl1 in X0. destruct X0. repeat destruct s. repeat destruct p. subst.
      exists x. repeat split ; try auto ; try apply in_cons ; try assumption.
Qed.

Lemma GLR_help1 : forall prems s, InT prems (prems_Box_R (top_boxes (snd s)) s) ->
                                         GLRRule prems s.
Proof.
intros. pose (@GLR_help01 _ _ _ X). repeat destruct s0. destruct s. simpl in X.
repeat destruct p. subst. simpl in i. assert (In (Box x) l0). apply top_boxes_incl_list.
assumption. apply in_splitT in H. destruct H. repeat destruct s.
rewrite e. apply GLRRule_I. intro. intros. apply in_top_boxes in H.
destruct H. repeat destruct s. repeat destruct p. exists x2. assumption.
simpl. apply top_boxes_nobox_gen_ext.
Qed.

Lemma GLR_help02 : forall Γ Δ0 Δ1 BΓ A l, GLRRule [(XBoxed_list BΓ ++ [Box A], [A])] (Γ, Δ0 ++ Box A :: Δ1) ->
                                             (is_Boxed_list BΓ) ->
                                             (nobox_gen_ext BΓ Γ) ->
                                             (In (Box A) l) ->
                                             InT [(XBoxed_list BΓ ++ [Box A], [A])] (prems_Box_R l (Γ, Δ0 ++ Box A :: Δ1)).
Proof.
induction l ; intros.
- inversion H0.
- simpl. destruct a.
  * assert (InT (Box A) (# v :: l)). apply in_splitT in H0. destruct H0. destruct s. rewrite e.
    apply InT_or_app. right. apply InT_eq. inversion H1. inversion H3. apply InT_In in H3.
    pose (IHl X H X0 H3). assumption.
  * assert (InT (Box A) (⊥ V :: l)). apply in_splitT in H0. destruct H0. destruct s. rewrite e.
    apply InT_or_app. right. apply InT_eq. inversion H1. inversion H3. apply InT_In in H3.
    pose (IHl X H X0 H3). assumption.
  * assert (InT (Box A) (a1 → a2 :: l)). apply in_splitT in H0. destruct H0. destruct s. rewrite e.
    apply InT_or_app. right. apply InT_eq. inversion H1. inversion H3. apply InT_In in H3.
    pose (IHl X H X0 H3). assumption.
  * assert (InT (Box A) (Box a :: l)). apply in_splitT in H0. destruct H0. destruct s. rewrite e.
    apply InT_or_app. right. apply InT_eq. inversion H1.
    + subst. inversion H3. subst. pose (nobox_gen_ext_top_boxes_identity X0 H). rewrite e.
      apply InT_eq.
    + subst. apply InT_In in H3. pose (IHl X H X0 H3). apply InT_cons. assumption.
Qed.

Lemma GLR_help2 : forall prem s, GLRRule [prem] s ->
                      InT [prem] (prems_Box_R (top_boxes (snd s)) s).
Proof.
intros. inversion X. subst. simpl.
pose (@GLR_help02 Γ0 Δ0 Δ1 BΓ A (top_boxes (Δ0 ++ Box A :: Δ1))). apply i ; try assumption.
rewrite top_boxes_distr_app. simpl. apply in_or_app. right. apply in_eq.
Qed.

Lemma finite_GLR_premises_of_S : forall (s : rel (list (MPropF V))), existsT2 listGLRprems,
              (forall prems, ((GLRRule prems s) -> (InT prems listGLRprems)) *
                             ((InT prems listGLRprems) -> (GLRRule prems s))).
Proof.
intros. destruct s.
exists (prems_Box_R (top_boxes l0) (l,l0)).
intros. split ; intro.
- inversion X. subst.
  pose (@GLR_help2 (XBoxed_list BΓ ++ [Box A], [A]) (l, Δ0 ++ Box A :: Δ1)). apply i.
  assumption.
- pose (@GLR_help1 prems (l, l0)). apply g. assumption.
Qed.

Lemma finite_IdP_premises_of_S : forall (s : rel (list (MPropF V))), existsT2 listIdPprems,
              (forall prems, ((IdPRule prems s) -> (InT prems listIdPprems)) *
                             ((InT prems listIdPprems) -> (IdPRule prems s))).
Proof.
intros. destruct (dec_IdP_rule s).
- exists [[]]. intros. split ; intro.
  * inversion H. subst. apply InT_eq.
  * inversion X. subst. assumption. inversion X0.
- exists []. intros. split ; intro.
  * inversion H. subst. exfalso. apply f. assumption.
  * inversion X.
Qed.

Lemma finite_IdB_premises_of_S : forall (s : rel (list (MPropF V))), existsT2 listIdBprems,
              (forall prems, ((IdBRule prems s) -> (InT prems listIdBprems)) *
                             ((InT prems listIdBprems) -> (IdBRule prems s))).
Proof.
intros. destruct (dec_IdB_rule s).
- exists [[]]. intros. split ; intro.
  * inversion H. subst. apply InT_eq.
  * inversion X. subst. assumption. inversion X0.
- exists []. intros. split ; intro.
  * inversion H. subst. exfalso. apply f. assumption.
  * inversion X.
Qed.

Lemma finite_BotL_premises_of_S : forall (s : rel (list (MPropF V))), existsT2 listBotLprems,
              (forall prems, ((BotLRule prems s) -> (InT prems listBotLprems)) *
                             ((InT prems listBotLprems) -> (BotLRule prems s))).
Proof.
intros. destruct (dec_BotL_rule s).
- exists [[]]. intros. split ; intro.
  * inversion H. subst. apply InT_eq.
  * inversion X. subst. assumption. inversion X0.
- exists []. intros. split ; intro.
  * inversion H. subst. exfalso. apply f. assumption.
  * inversion X.
Qed.

(* Now that we have the list of all premises of a sequent via all rules, we can combine
   them all to obtain the list of all potential premises via the PSGLS calculus. *)

Lemma finite_premises_of_S : forall (s : rel (list (MPropF V))), existsT2 listprems,
              (forall prems, ((PSGLS_rules prems s) -> (InT prems listprems)) *
                             ((InT prems listprems) -> (PSGLS_rules prems s))).
Proof.
intro s.
destruct (dec_PSGLS_rules s).
- exists []. intros. split. intro. exfalso. apply f. exists prems. assumption.
  intro. inversion X.
- destruct (dec_init_rules s).
  + pose (finite_IdP_premises_of_S s). destruct s2.
    pose (finite_IdB_premises_of_S s). destruct s2.
    pose (finite_BotL_premises_of_S s). destruct s2.
    pose (finite_ImpR_premises_of_S s). destruct s2.
    pose (finite_ImpL_premises_of_S s). destruct s2.
    exists (x ++ x0 ++ x1 ++ x2 ++ x3).
    repeat destruct s1.
    * inversion i. subst. split.
      { intro RA. inversion RA.
        - inversion H. subst. pose (p []). destruct p4. apply InT_or_app. auto.
        - inversion H. subst. pose (p0 []). destruct p4. apply InT_or_app. right. apply InT_or_app. auto.
        - inversion H. subst. pose (p1 []). destruct p4. apply InT_or_app. right. apply InT_or_app. right.
          apply InT_or_app. auto.
        - inversion H. subst. pose (p2 [(Γ2 ++ A :: Γ3, Δ2 ++ B :: Δ3)]). destruct p4.
          apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. auto.
        - inversion H. subst. pose (p3 [(Γ2 ++ Γ3, Δ2 ++ A :: Δ3); (Γ2 ++ B :: Γ3, Δ2 ++ Δ3)]).
          destruct p4. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
          apply InT_or_app. right. auto.
        - inversion X. exfalso. firstorder. }
      { intro. apply InT_app_or in X. destruct X.
        - apply p in i0. apply PSIdP ; try intro ; try apply f ; try auto ; try assumption.
        - apply InT_app_or in i0. destruct i0.
          + apply p0 in i0. apply PSIdB ; try intro ; try apply f ; try auto ; try assumption.
          + apply InT_app_or in i0. destruct i0.
            * apply p1 in i0. apply PSBotL ; try intro ; try apply f ; try auto ; try assumption.
            * apply InT_app_or in i0. destruct i0.
              { apply p2 in i0. apply PSImpR ; try intro ; try apply f ; try auto ; try assumption. }
              { apply p3 in i0. apply PSImpL ; try intro ; try apply f ; try auto ; try assumption. } }
    * inversion i. subst. split.
      { intro RA. inversion RA.
        - inversion H. subst. pose (p []). destruct p4. apply InT_or_app. auto.
        - inversion H. subst. pose (p0 []). destruct p4. apply InT_or_app. right. apply InT_or_app. auto.
        - inversion H. subst. pose (p1 []). destruct p4. apply InT_or_app. right. apply InT_or_app. right.
          apply InT_or_app. auto.
        - inversion H. subst. pose (p2 [(Γ2 ++ A0 :: Γ3, Δ2 ++ B :: Δ3)]). destruct p4.
          apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. auto.
        - inversion H. subst. pose (p3 [(Γ2 ++ Γ3, Δ2 ++ A0 :: Δ3); (Γ2 ++ B :: Γ3, Δ2 ++ Δ3)]).
          destruct p4. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
          apply InT_or_app. right. auto.
        - inversion X. exfalso. firstorder. }
      { intro. apply InT_app_or in X. destruct X.
        - apply p in i0. apply PSIdP ; try intro ; try apply f ; try auto ; try assumption.
        - apply InT_app_or in i0. destruct i0.
          + apply p0 in i0. apply PSIdB ; try intro ; try apply f ; try auto ; try assumption.
          + apply InT_app_or in i0. destruct i0.
            * apply p1 in i0. apply PSBotL ; try intro ; try apply f ; try auto ; try assumption.
            * apply InT_app_or in i0. destruct i0.
              { apply p2 in i0. apply PSImpR ; try intro ; try apply f ; try auto ; try assumption. }
              { apply p3 in i0. apply PSImpL ; try intro ; try apply f ; try auto ; try assumption. } }
    * inversion b. subst. split.
      { intro RA. inversion RA.
        - inversion H. subst. pose (p []). destruct p4. apply InT_or_app. auto.
        - inversion H. subst. pose (p0 []). destruct p4. apply InT_or_app. right. apply InT_or_app. auto.
        - inversion H. subst. pose (p1 []). destruct p4. apply InT_or_app. right. apply InT_or_app. right.
          apply InT_or_app. auto.
        - inversion H. subst. pose (p2 [(Γ2 ++ A :: Γ3, Δ0 ++ B :: Δ1)]). destruct p4.
          apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. auto.
        - inversion H. subst. pose (p3 [(Γ2 ++ Γ3, Δ0 ++ A :: Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)]).
          destruct p4. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
          apply InT_or_app. right. auto.
        - inversion X. exfalso. firstorder. }
      { intro. apply InT_app_or in X. destruct X.
        - apply p in i. apply PSIdP ; try intro ; try apply f ; try auto ; try assumption.
        - apply InT_app_or in i. destruct i.
          + apply p0 in i. apply PSIdB ; try intro ; try apply f ; try auto ; try assumption.
          + apply InT_app_or in i. destruct i.
            * apply p1 in i. apply PSBotL ; try intro ; try apply f ; try auto ; try assumption.
            * apply InT_app_or in i. destruct i.
              { apply p2 in i. apply PSImpR ; try intro ; try apply f ; try auto ; try assumption. }
              { apply p3 in i. apply PSImpL ; try intro ; try apply f ; try auto ; try assumption. } }
  + pose (finite_IdP_premises_of_S s). destruct s1.
    pose (finite_IdB_premises_of_S s). destruct s1.
    pose (finite_BotL_premises_of_S s). destruct s1.
    pose (finite_ImpR_premises_of_S s). destruct s1.
    pose (finite_ImpL_premises_of_S s). destruct s1.
    pose (finite_GLR_premises_of_S s). destruct s1.
    exists (x ++ x0 ++ x1 ++ x2 ++ x3 ++ x4).
    split.
    * intro RA. inversion RA.
      { inversion H. subst. pose (p []). destruct p5. apply InT_or_app. auto. }
      { inversion H. subst. pose (p0 []). destruct p5. apply InT_or_app. right. apply InT_or_app. auto. }
      { inversion H. subst. pose (p1 []). destruct p5. apply InT_or_app. right. apply InT_or_app. right.
        apply InT_or_app. auto. }
      { inversion H. subst. pose (p2 [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]). destruct p5.
        apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. auto. }
      { inversion H. subst. pose (p3 [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]).
        destruct p5. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app. right.
        apply InT_or_app. right. apply InT_or_app. auto. }
      { inversion X. subst. pose (p4 [(XBoxed_list BΓ ++ [Box A], [A])]).
        destruct p5. apply InT_or_app. right. apply InT_or_app. right. apply InT_or_app.
        right. apply InT_or_app. right. apply InT_or_app. right. auto. }
    * intro. apply InT_app_or in X. destruct X.
      { apply p in i. apply PSIdP ; try intro ; try apply f ; try auto ; try assumption. }
      { apply InT_app_or in i. destruct i.
        - apply p0 in i. apply PSIdB ; try intro ; try apply f ; try auto ; try assumption.
        - apply InT_app_or in i. destruct i.
          + apply p1 in i. apply PSBotL ; try intro ; try apply f ; try auto ; try assumption.
          + apply InT_app_or in i. destruct i.
            * apply p2 in i. apply PSImpR ; try intro ; try apply f ; try auto ; try assumption.
            * apply InT_app_or in i. destruct i.
              { apply p3 in i. apply PSImpL ; try intro ; try apply f ; try auto ; try assumption. }
              { apply p4 in i. apply PSGLR ; try intro ; try apply f ; try auto ; try assumption. } }
Qed.

(* The next definitions "flattens" a list of lists of premises to a list of premises.*)

Definition list_of_premises (s : rel (list (MPropF V))) : list (rel (list (MPropF V))) :=
         flatten_list (proj1_sigT2 (finite_premises_of_S s)).

Lemma InT_list_of_premises_exists_prems : forall s prem, InT prem (list_of_premises s) ->
            existsT2 prems, (InT prem prems) * (PSGLS_rules prems s).
Proof.
intros. unfold list_of_premises in X.
apply InT_flatten_list_InT_elem in X. destruct X. destruct p.
exists x. split. auto.
destruct (finite_premises_of_S s). pose (p x). destruct p0. apply p0. assumption.
Qed.

Lemma exists_prems_InT_list_of_premises : forall s prem,
            (existsT2 prems, (InT prem prems) * (PSGLS_rules prems s)) ->
            InT prem (list_of_premises s).
Proof.
intros. destruct X. destruct p. unfold list_of_premises. destruct (finite_premises_of_S s).
pose (p0 x). destruct p1. apply InT_trans_flatten_list with (bs:=x). assumption. simpl. apply i0.
assumption.
Qed.

Lemma find_the_max_mhd : forall concl l
      (Prem_mhd : forall prems : list (rel (list (MPropF V))), PSGLS_rules prems concl ->
                  forall prem : rel (list (MPropF V)), InT prem prems ->
                  existsT2 Dprem : derrec PSGLS_rules (fun _ : rel (list (MPropF V)) => True) prem,
                  is_mhd Dprem)
      (H1 : forall prem : rel (list (MPropF V)), InT prem l -> InT prem (list_of_premises concl))
      (H2 : forall (prem : rel (list (MPropF V))) (J : InT prem l), InT prem (proj1_sigT2
            (InT_list_of_premises_exists_prems concl (H1 prem J))))
      (H3 : forall (prem : rel (list (MPropF V))) (J : InT prem l), PSGLS_rules (proj1_sigT2
            (InT_list_of_premises_exists_prems concl (H1 prem J))) concl)
      (NotNil: l <> nil),

existsT2 prem, existsT2 (J0: InT prem l), forall prem' (J1: InT prem' l),
       (derrec_height (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1)))
        (H3 prem' J1)
        prem'
        (H2 prem' J1))))
       <=
       (derrec_height (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J0)))
        (H3 prem J0)
        prem
        (H2 prem J0)))).
Proof.
induction l ; intros.
- exfalso. apply NotNil. reflexivity.
- clear NotNil. destruct l.
  * exists a. assert (InT a [a]). apply InT_eq. exists X. intros. inversion J1. subst.
    destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' X))) (H3 prem' X) prem' (H2 prem' X)).
    destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1))) (H3 prem' J1) prem' (H2 prem' J1)).
    simpl. auto. inversion X0.
  * assert (H1' : forall prem : rel (list (MPropF V)), InT prem (r :: l) -> InT prem (list_of_premises concl)).
    { intros. apply H1. apply InT_cons. assumption. }
    assert (Prem_mhd' : forall prems : list (rel (list (MPropF V))), PSGLS_rules prems concl -> forall prem : rel (list (MPropF V)),
                        InT prem prems -> existsT2 Dprem : derrec PSGLS_rules (fun _ : rel (list (MPropF V)) => True)
                        prem, is_mhd Dprem).
    { intros. apply Prem_mhd with (prems:= prems) ; try assumption. }
    assert (H2' : forall (prem : rel (list (MPropF V))) (J : InT prem (r :: l)), InT prem (proj1_sigT2
                  (InT_list_of_premises_exists_prems concl (H1' prem J)))).
    { intros. assert (InT prem (a :: r :: l)). apply InT_cons. assumption. pose (H2 _ X).
      destruct (InT_list_of_premises_exists_prems concl (H1' prem J)).
      simpl. destruct p. assumption. }
    assert (H3' : forall (prem : rel (list (MPropF V))) (J : InT prem (r :: l)), PSGLS_rules
                (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem J))) concl).
    { intros. destruct (InT_list_of_premises_exists_prems concl (H1' prem J)). simpl. destruct p.
      assumption. }
    assert (r :: l <> []). intro. inversion H.
    pose (IHl Prem_mhd' H1' H2' H3' H). destruct s. destruct s.
    (* I have a max in r :: l: so I simply need to compare it with a. *)
    assert (J2: InT a (a :: r :: l)). apply InT_eq.
    assert (J3: InT x (a :: r :: l)). apply InT_cons. assumption.
    (* The next assert decides on le between mhd of a and mhd of x. *)
    pose (dec_le
      (derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 a J2)))
      (H3 a J2) a (H2 a J2))))
      (derrec_height
       (proj1_sigT2
          (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' x x0))) 
             (H3' x x0) x (H2' x x0))))).
    destruct s.
    + exists x. exists J3. intros. inversion J1. subst.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1))) 
      (H3 prem' J1) prem' (H2 prem' J1)). simpl.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J2))) 
      (H3 prem' J2) prem' (H2 prem' J2)). simpl in l1. unfold is_mhd in i0.
      pose (i0 x1).
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x J3))) (H3 x J3) x (H2 x J3)).
      simpl.
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' x x0))) 
      (H3' x x0) x (H2' x x0)). simpl in l1.
      unfold is_mhd in i1. pose (i1 x4). lia.
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' x x0)))
      (H3' x x0) x (H2' x x0)). simpl in l0.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x J3))) (H3 x J3) x (H2 x J3)).
      simpl.
      destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1)))). simpl.
      assert (derrec_height
     (proj1_sigT2
        (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem' X))) 
           (H3' prem' X) prem' (H2' prem' X))) <= derrec_height x1).
      apply (l0 prem' X). subst.
      unfold is_mhd in i0. pose (i0 x1).
      destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem' X)))
           (H3' prem' X) prem' (H2' prem' X)). simpl in H0. unfold is_mhd in i2. pose (i2 x3). lia.
    + exists a. exists J2. intros. apply le_False_lt in f.
      inversion J1.
      { subst. destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1))) 
        (H3 prem' J1) prem' (H2 prem' J1)). simpl.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J2))) 
        (H3 prem' J2) prem' (H2 prem' J2)).
        simpl. unfold is_mhd in i0. pose (i0 x1). lia. }
      { subst.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 a J2))) (H3 a J2) a (H2 a J2)).
        simpl.
        destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem' J1))) 
        (H3 prem' J1) prem' (H2 prem' J1)). simpl.
        destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' x x0))) 
             (H3' x x0) x (H2' x x0)). simpl in l0.
        assert (derrec_height
       (proj1_sigT2
          (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem' X)))
             (H3' prem' X) prem' (H2' prem' X))) <= derrec_height x3). apply l0.
       destruct (Prem_mhd' (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1' prem' X)))
             (H3' prem' X) prem' (H2' prem' X)). simpl in H0. simpl in f. unfold is_mhd in i2.
       pose (i2 x2). lia. }
Qed.

Lemma term_IH_help : forall concl,
     (existsT2 prems, (PSGLS_rules prems concl) * (prems <> [])) ->
     (forall prems, PSGLS_rules prems concl -> (forall prem, InT prem prems -> (existsT2 Dprem, @is_mhd prem Dprem)))
      ->
     (existsT2 Maxprems Maxprem DMaxprem, (PSGLS_rules Maxprems concl) * (@is_mhd Maxprem DMaxprem) * (InT Maxprem Maxprems) *
        (forall prems prem (Dprem : derrec (@PSGLS_rules V) (fun _ => True) prem), PSGLS_rules prems concl -> InT prem prems ->
            derrec_height Dprem <= derrec_height DMaxprem)).
Proof.
intros concl FAH Prem_mhd.
pose (list_of_premises concl).
assert (H1: forall prem, InT prem l -> InT prem (list_of_premises concl)).
intros. auto.
assert (H2: forall prem (J: InT prem l), InT prem (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J)))).
intros. destruct (InT_list_of_premises_exists_prems concl (H1 prem J)). destruct p. auto.
assert (H3: forall prem (J: InT prem l),
PSGLS_rules (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J))) concl).
intros. destruct (InT_list_of_premises_exists_prems concl (H1 prem J)). destruct p. auto.
assert (H4: forall prem (J: InT prem l), is_mhd (proj1_sigT2 (Prem_mhd
        (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J)))
        (H3 prem J)
        prem
        (H2 prem J)))).
intros. intro. destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J)))
(H3 prem J) prem (H2 prem J)). auto.
assert (l <> []). intro. destruct FAH. destruct p. destruct p.
- inversion i. subst. auto.
- inversion i. subst. auto.
- inversion b. subst. auto.
- inversion i. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1) (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
  assert (InT (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (list_of_premises (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1))). apply i0.
  exists [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]. split. apply InT_eq. apply PSImpR ; assumption.
  assert (InT (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) l). auto. rewrite H in H5. inversion H5.
- inversion i. subst. pose (@exists_prems_InT_list_of_premises (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
  assert (InT (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) (list_of_premises (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1))). apply i0.
  exists [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]. split. apply InT_eq. apply PSImpL ; assumption.
  assert (InT (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) l). auto. rewrite H in H5. inversion H5.
- inversion g. subst. pose (@exists_prems_InT_list_of_premises (Γ0, Δ0 ++ Box A :: Δ1) (XBoxed_list BΓ ++ [Box A], [A])).
  assert (InT (XBoxed_list BΓ ++ [Box A], [A]) (list_of_premises (Γ0, Δ0 ++ Box A :: Δ1))). apply i.
  exists [(XBoxed_list BΓ ++ [Box A], [A])]. split. apply InT_eq. apply PSGLR ; assumption.
  assert (InT (XBoxed_list BΓ ++ [Box A], [A]) l). auto. rewrite H in H6. inversion H6.

- pose (find_the_max_mhd Prem_mhd H1 H2 H3 H).
  destruct s. destruct s. exists (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x x0))).
  exists x. exists (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x x0)))
  (H3 x x0) x (H2 x x0))). repeat split ; try apply H3 ; try apply H4 ; try apply H2.
  intros prems prem Dprem RA IsPrem.
  assert (J3: InT prem l).
  pose (@exists_prems_InT_list_of_premises concl prem). apply i. exists prems. auto.
  assert (E1: derrec_height Dprem <= derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2
  (InT_list_of_premises_exists_prems concl (H1 prem J3))) (H3 prem J3) prem (H2 prem J3)))).
  destruct (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 prem J3)))
  (H3 prem J3) prem (H2 prem J3)). auto.
  assert (E2: derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl
  (H1 prem J3))) (H3 prem J3) prem (H2 prem J3))) <=
  derrec_height (proj1_sigT2 (Prem_mhd (proj1_sigT2 (InT_list_of_premises_exists_prems concl (H1 x x0)))
  (H3 x x0) x (H2 x x0)))). apply l0. lia.
Qed.

Lemma in_drs_concl_in_allT W rules prems ps (cn : W) (drs : dersrec rules prems ps)
  (dtn : derrec rules prems cn) : in_dersrec dtn drs -> InT cn ps.
Proof.
intro ind. induction ind. apply InT_eq.
apply InT_cons. assumption.
Qed.

Lemma dec_non_nil_prems: forall (concl : (rel (list (MPropF V)))), ((existsT2 prems, (PSGLS_rules prems concl) * (prems <> []))) +
                                       ((existsT2 prems, (PSGLS_rules prems concl) * (prems <> [])) -> False).
Proof.
intros. destruct (dec_init_rules concl).
- destruct (dec_GLR_rule concl).
  + destruct s0. destruct (dec_ImpR_rule concl).
    * destruct s0. left. exists [x0]. split. apply PSImpR in i. assumption. intro. inversion H.
    * destruct (dec_ImpL_rule concl).
      { destruct s0. destruct s0. left. exists [x0; x1]. split. apply PSImpL in i. assumption.
        intro. inversion H. }
      { right. intro. destruct X. destruct p. inversion p.
        - subst. inversion H. auto.
        - subst. inversion H. auto.
        - subst. inversion H. auto.
        - subst. inversion H. subst. apply f. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). assumption.
        - subst. inversion H. subst. apply f0. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1).
          exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). assumption.
        - subst. repeat destruct s ; auto. }
  + destruct (dec_ImpR_rule concl).
    * destruct s0. left. exists [x]. split. apply PSImpR in i. assumption. intro. inversion H.
    * destruct (dec_ImpL_rule concl).
      { destruct s0. destruct s0. left. exists [x; x0]. split. apply PSImpL in i. assumption.
        intro. inversion H. }
      { right. intro. destruct X. destruct p. inversion p.
        - subst. inversion H. auto.
        - subst. inversion H. auto.
        - subst. inversion H. auto.
        - subst. inversion H. subst. apply f0. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). assumption.
        - subst. inversion H. subst. apply f1. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1).
          exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). assumption.
        - subst. inversion X. subst. apply f. exists (XBoxed_list BΓ ++ [Box A], [A]). assumption. }
- destruct (dec_GLR_rule concl).
  + destruct s. left. exists [x]. split. apply PSGLR in g ; auto. intro. inversion H.
  + destruct (dec_ImpR_rule concl).
    * destruct s. left. exists [x]. split. apply PSImpR in i. assumption. intro. inversion H.
    * destruct (dec_ImpL_rule concl).
      { destruct s. destruct s. left. exists [x; x0]. split. apply PSImpL in i. assumption.
        intro. inversion H. }
      { right. intro. destruct X. destruct p. inversion p.
        - subst. inversion H. auto.
        - subst. inversion H. auto.
        - subst. inversion H. auto.
        - subst. inversion H. subst. apply f1. exists (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1). assumption.
        - subst. inversion H. subst. apply f2. exists (Γ0 ++ Γ1, Δ0 ++ A :: Δ1).
          exists (Γ0 ++ B :: Γ1, Δ0 ++ Δ1). assumption.
        - subst. inversion X. subst. apply f0. exists (XBoxed_list BΓ ++ [Box A], [A]). assumption. }
Qed.

(* The next theorem claims that every sequent s has a derivation DMax of maximal height. *)

Theorem PSGLS_termin_base : forall n m s, (n = length (usable_boxes s)) -> (m = n_imp_subformS s) ->
   existsT2 (DMax : derrec (@PSGLS_rules V) (fun _ => True) s), (@is_mhd s DMax).
Proof.
(* Setting up the strong inductions on each. *)
pose (strong_inductionT (fun (x:nat) => forall m (s : rel (list (MPropF V))),
x = length (usable_boxes s) -> (m = n_imp_subformS s) ->
(existsT2 DMax : derrec (PSGLS_rules (V:=V))
(fun _ : rel (list (MPropF V)) => True) s, is_mhd DMax))).
apply s. intros n PIH. clear s.
pose (strong_inductionT (fun (x:nat) => forall (s : rel (list (MPropF V))),
n = length (usable_boxes s) -> (x = n_imp_subformS s) ->
(existsT2 DMax : derrec (PSGLS_rules (V:=V))
(fun _ : rel (list (MPropF V)) => True) s, is_mhd DMax))).
apply s. intros m SIH. clear s.

(* Now we can do the pen and paper proof. *)
assert (dersrecnil: dersrec (@PSGLS_rules V) (fun _ => True) nil).
apply dersrec_nil.
intros. pose (dec_PSGLS_rules s). destruct s0.
- assert (forall ps : list (rel (list (MPropF V))), PSGLS_rules ps s -> False).
  intros. apply f. exists ps. assumption. pose (@no_PSGLS_rule_applic s H1).
  pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) s I).
  exists d. unfold is_mhd. intros. simpl. pose (e D1). rewrite e0. auto.
- assert (forall prems, PSGLS_rules prems s -> (forall prem, InT prem prems ->
  (existsT2 Dprem, @is_mhd prem Dprem))).
  { simpl. intros. inversion X.
    - inversion H1. subst. exfalso. inversion X0.
    - inversion H1. subst. exfalso. inversion X0.
    - inversion H1. subst. exfalso. inversion X0.
    - inversion H1. subst. inversion X0. 2: inversion X1. subst.
      pose (@ImpR_applic_less_Imp_same_usable_boxes (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1) H1).
      destruct p. destruct s.
      + pose (PIH (length (usable_boxes (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1))) l0 (n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1))
        (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)). apply s. reflexivity. reflexivity.
      + symmetry in e. assert (n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) = n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
        reflexivity. pose (SIH (n_imp_subformS (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)) l (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1) e H).
        assumption.
    - inversion H1. subst.
      pose (@ImpL_applic_less_Imp_same_usable_boxes (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1) H1).
      repeat destruct p. destruct p0. destruct s.
      + inversion X0.
        * subst. pose (PIH (length (usable_boxes (Γ0 ++ Γ1, Δ0 ++ A :: Δ1))) l1 (n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1))
          (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)). apply s ; reflexivity.
        * inversion X1. 2: inversion X2. subst. destruct s1.
          { pose (PIH (length (usable_boxes (Γ0 ++ B :: Γ1, Δ0 ++ Δ1))) l2 (n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1))
            (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)). apply s ; reflexivity. }
          { symmetry in e. pose (SIH (n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) l0 (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) e).
            apply s ; reflexivity. }
      + inversion X0.
        * subst. symmetry in e. pose (SIH (n_imp_subformS (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) l (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) e).
          apply s ; reflexivity.
        * inversion X1. 2: inversion X2. subst. destruct s1.
          { pose (PIH (length (usable_boxes (Γ0 ++ B :: Γ1, Δ0 ++ Δ1))) l1 (n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1))
            (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)). apply s ; reflexivity. }
          { symmetry in e0. pose (SIH (n_imp_subformS (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)) l0 (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) e0).
            apply s ; reflexivity. }
    - inversion X1. subst. inversion X0. 2: inversion X3. subst. destruct (dec_IdB_rule (Γ0, Δ0 ++ Box A :: Δ1)).
      + inversion i. subst. exfalso. apply H2. rewrite <- H4. apply IdBRule_I.
      + pose (@GLR_applic_less_usable_boxes (XBoxed_list BΓ ++ [Box A], [A]) (Γ0, Δ0 ++ Box A :: Δ1) X1 f).
        pose (PIH (length (usable_boxes (XBoxed_list BΓ ++ [Box A], [A]))) l (n_imp_subformS (XBoxed_list BΓ ++ [Box A], [A]))
        (XBoxed_list BΓ ++ [Box A], [A])). apply s ; reflexivity. }
    destruct (dec_non_nil_prems s).
    + pose (@term_IH_help s s1 X). repeat destruct s2. destruct p. destruct p. destruct p.
      inversion p.
      (* Use PIH and SIH here, depending on the rule applied *)
      * inversion H1. subst. inversion i.
      * inversion H1. subst. inversion i.
      * inversion H1. subst. inversion i.
      * subst. inversion H1. subst. assert (E: x0 = (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
        inversion i. auto. inversion X0. subst.
        pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)] (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil). rewrite Max.max_0_r.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H). lia. }
        { reflexivity. }
      * subst. inversion H1. subst. inversion i.
        { subst. pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) I).
          pose (dlCons d dersrecnil). pose (dlCons x1 d0).
          pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
          (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1) p d1).
          exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil). rewrite Max.max_0_r.
          destruct D1.
          { simpl. lia. }
          { simpl.
            assert (forall p (d : derrec (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) p),
            in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
            pose (in_drs_concl_in_allT X0). subst. pose (l ps p1 d4 p0 i1). assumption.
            pose (dersrec_height_le H). lia. }
          { reflexivity. } }
        { inversion X0. subst. pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) I).
          pose (dlCons x1 dersrecnil). pose (dlCons d d0).
          pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
          (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1) p d1).
          exists d2. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil). rewrite Max.max_0_r.
          destruct D1.
          { simpl. lia. }
          { simpl.
            assert (forall p (d : derrec (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) p),
            in_dersrec d d3 -> derrec_height d <= (derrec_height x1)). intros.
            pose (in_drs_concl_in_allT X1). subst. pose (l ps p1 d4 p0 i1). assumption.
            pose (dersrec_height_le H). lia. }
          { reflexivity. }
          inversion X1. }
      * subst. inversion X0. subst. assert (E: x0 = (XBoxed_list BΓ ++ [Box A], [A])).
        inversion i. auto. inversion X2. subst.
        pose (dlCons x1 dersrecnil).
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(XBoxed_list BΓ ++ [Box A], [A])] (Γ0, Δ0 ++ Box A :: Δ1) p d).
        exists d0. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil). rewrite Max.max_0_r.
        destruct D1.
        { simpl. lia. }
        { simpl.
          assert (forall p (d : derrec (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) p),
          in_dersrec d d1 -> derrec_height d <= (derrec_height x1)). intros.
          pose (in_drs_concl_in_allT X2). subst. pose (l ps p1 d2 p0 i1). assumption.
          pose (dersrec_height_le H0). lia. }
        { reflexivity. }
    + destruct s0. inversion p.
      * inversion H1. subst. pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [] (Γ0 ++ # P :: Γ1, Δ0 ++ # P :: Δ1) p dersrecnil).
        exists d. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil).
        destruct D1.
        { simpl. lia. }
        { simpl. destruct p0.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion b. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ A :: Γ3, Δ2 ++ B :: Δ3)]. split.
            apply PSImpR in i. assumption. intro. inversion H.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ Γ3, Δ2 ++ A :: Δ3); (Γ2 ++ B :: Γ3, Δ2 ++ Δ3)]. split.
            apply PSImpL in i. assumption. intro. inversion H.
          - exfalso. auto. }
        { reflexivity. }
      * inversion H1. subst. pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [] (Γ0 ++ Box A :: Γ1, Δ0 ++ Box A :: Δ1) p dersrecnil).
        exists d. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil).
        destruct D1.
        { simpl. lia. }
        { simpl. destruct p0.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion b. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ A0 :: Γ3, Δ2 ++ B :: Δ3)]. split.
            apply PSImpR in i. assumption. intro. inversion H.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ Γ3, Δ2 ++ A0 :: Δ3); (Γ2 ++ B :: Γ3, Δ2 ++ Δ3)]. split.
            apply PSImpL in i. assumption. intro. inversion H.
          - exfalso. auto. }
        { reflexivity. }
      * inversion H1. subst. pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [] (Γ0 ++ ⊥ V :: Γ1, Δ) p dersrecnil).
        exists d. unfold is_mhd. intros. simpl. rewrite dersrec_height_nil with (ds:=dersrecnil).
        destruct D1.
        { simpl. lia. }
        { simpl. destruct p0.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion i. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion b. subst. rewrite dersrec_height_nil with (ds:=d0). lia. reflexivity.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ A :: Γ3, Δ0 ++ B :: Δ1)]. split.
            apply PSImpR in i. assumption. intro. inversion H.
          - inversion i. subst. exfalso. apply f. exists [(Γ2 ++ Γ3, Δ0 ++ A :: Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)]. split.
            apply PSImpL in i. assumption. intro. inversion H.
          - exfalso. auto. }
        { reflexivity. }
      * inversion H1. subst. exfalso. apply f. exists [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)]. split. assumption. intro.
        inversion H.
      * inversion H1. subst. exfalso. apply f. exists [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]. split. assumption. intro.
        inversion H.
      * inversion X0. subst. exfalso. apply f. exists [(XBoxed_list BΓ ++ [Box A], [A])]. split. assumption. intro.
        inversion H.
Qed.


Theorem PSGLS_termin : forall s, existsT2 (DMax : derrec (@PSGLS_rules V) (fun _ => True) s), (@is_mhd s DMax).
Proof.
intro s. pose (@PSGLS_termin_base (length (usable_boxes s)) (n_imp_subformS s)). apply s0 ; reflexivity.
Qed.

Theorem PSGLS_termin1 : forall (s : rel (list (MPropF V))), exists (DMax : derrec PSGLS_rules (fun _ => True) s), (is_mhd DMax).
Proof.
intro s.
assert (J1: length (usable_boxes s) = length (usable_boxes s)). reflexivity.
assert (J2: n_imp_subformS s = n_imp_subformS s). reflexivity.
pose (@PSGLS_termin_base (length (usable_boxes s)) (n_imp_subformS s) s J1 J2).
destruct s0. exists x. assumption.
Qed.

Theorem PSGLS_termin2 : forall s, exists (DMax : derrec (@PSGLS_rules V) (fun _ => True) s), (is_mhd DMax).
Proof.
intro s.
assert (J1: length (usable_boxes s) = length (usable_boxes s)). reflexivity.
assert (J2: n_imp_subformS s = n_imp_subformS s). reflexivity.
pose (@PSGLS_termin_base (length (usable_boxes s)) (n_imp_subformS s) s J1 J2).
destruct s0. exists x. assumption.
Qed.

Theorem PSGLS_termin3 : forall (s : rel (list (MPropF V))), existsT2 (DMax : derrec PSGLS_rules (fun _ => True) s), (is_mhd DMax).
Proof.
intro s. pose (@PSGLS_termin_base (length (usable_boxes s)) (n_imp_subformS s)). apply s0 ; reflexivity.
Qed.

(* Now we can prove that the maximal height of derivations (mhd) for sequents
   decreases upwards in the applicability of the proofs. In other words, if a sequent s is the
   conclusion of an instance of a rule R of PSGLS with premises in ps, then for any element s0 of
   ps we have that (mhd s0) < (mhd s).

   To do so we first define mhd.*)

Definition mhd (s: rel (list (MPropF V))) : nat := derrec_height (proj1_sigT2 (@PSGLS_termin s)).

Lemma PSGLS_termin_der_is_mhd : forall s, (@is_mhd s (proj1_sigT2 (@PSGLS_termin s))).
Proof.
intro s. destruct PSGLS_termin. auto.
Qed.

Theorem RA_mhd_decreases : forall prems concl, (PSGLS_rules prems concl) ->
                             (forall prem, (In prem prems) -> (mhd prem) < (mhd concl)).
Proof.
intros. inversion X.
- inversion H0. subst. inversion H.
- inversion H0. subst. inversion H.
- inversion H0. subst. inversion H.
- inversion H0. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGLS_termin (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1))).
    pose (proj1_sigT2 (PSGLS_termin (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1))).
    assert (dersrecnil: dersrec (@PSGLS_rules V) (fun _ => True) nil).
    apply dersrec_nil. pose (dlCons d0 dersrecnil).
    pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)] (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1) X d1).
    assert (E1: derrec_height d0 = mhd (Γ0 ++ A :: Γ1, Δ0 ++ B :: Δ1)).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0 ++ Γ1, Δ0 ++ A → B :: Δ1) d). apply PSGLS_termin_der_is_mhd.
    unfold is_mhd in H2. pose (H2 d2). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
  * inversion H1.
- inversion H0. subst. inversion H.
    * subst. apply le_False_lt. intro.
      pose (proj1_sigT2 (PSGLS_termin (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1))).
      pose (proj1_sigT2 (PSGLS_termin (Γ0 ++ Γ1, Δ0 ++ A :: Δ1))).
      assert (dersrecnil: dersrec (@PSGLS_rules V) (fun _ => True) nil).
      apply dersrec_nil.
      pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (Γ0 ++ B :: Γ1, Δ0 ++ Δ1) I).
      pose (dlCons d1 dersrecnil). pose (dlCons d0 d2).
      pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
      (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1) X d3).
      assert (E1: derrec_height d0 = mhd (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)).
      unfold mhd. auto.
      assert (E2: derrec_height d = mhd (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)).
      unfold mhd. auto.
      assert (@is_mhd (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1) d). apply PSGLS_termin_der_is_mhd.
      unfold is_mhd in H2. pose (H2 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
      lia. reflexivity.
    * inversion H1. subst. apply le_False_lt. intro.
      pose (proj1_sigT2 (PSGLS_termin (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1))).
      pose (proj1_sigT2 (PSGLS_termin (Γ0 ++ B :: Γ1, Δ0 ++ Δ1))).
      assert (dersrecnil: dersrec (@PSGLS_rules V) (fun _ => True) nil).
      apply dersrec_nil.
      pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1) I).
      pose (dlCons d0 dersrecnil). pose (dlCons d1 d2).
      pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(Γ0 ++ Γ1, Δ0 ++ A :: Δ1); (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)]
      (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1) X d3).
      assert (E1: derrec_height d0 = mhd (Γ0 ++ B :: Γ1, Δ0 ++ Δ1)).
      unfold mhd. auto.
      assert (E2: derrec_height d = mhd (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1)).
      unfold mhd. auto.
      assert (@is_mhd (Γ0 ++ A → B :: Γ1, Δ0 ++ Δ1) d). apply PSGLS_termin_der_is_mhd.
      unfold is_mhd in H3. pose (H3 d4). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
      simpl in l. lia. reflexivity. inversion H2.
- inversion X0. subst. inversion H.
  * subst. apply le_False_lt. intro.
    pose (proj1_sigT2 (PSGLS_termin (Γ0, Δ0 ++ Box A :: Δ1))).
    pose (proj1_sigT2 (PSGLS_termin (XBoxed_list BΓ ++ [Box A], [A]))).
    assert (dersrecnil: dersrec (@PSGLS_rules V) (fun _ => True) nil).
    apply dersrec_nil. pose (dlCons d0 dersrecnil).
    pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(XBoxed_list BΓ ++ [Box A], [A])] (Γ0, Δ0 ++ Box A :: Δ1) X d1).
    assert (E1: derrec_height d0 = mhd (XBoxed_list BΓ ++ [Box A], [A])).
    unfold mhd. auto.
    assert (E2: derrec_height d = mhd (Γ0, Δ0 ++ Box A :: Δ1)).
    unfold mhd. auto.
    assert (@is_mhd (Γ0, Δ0 ++ Box A :: Δ1) d). apply PSGLS_termin_der_is_mhd.
    unfold is_mhd in H4. pose (H4 d2). simpl in l. rewrite dersrec_height_nil in l. rewrite Max.max_0_r in l.
    lia. reflexivity.
  * inversion H3.
Qed.



Lemma mhd_0_prime_atomic : forall Γ Δ, (mhd (Γ,Δ) = 0) -> (is_Prime Γ) * (is_Atomic Δ).
Proof.
assert (DersNil: dersrec (@PSGLS_rules V) (fun _ => True) nil).
apply dersrec_nil.
intros. unfold mhd in H. remember (Γ,Δ) as s. destruct (PSGLS_termin s).
destruct x.
- split.
  + intro. intros. destruct A.
    * right. left. exists v. reflexivity.
    * exfalso. apply In_split in H0. destruct H0. destruct H0. rewrite H0 in Heqs. subst.
      assert (BotLRule [] (x ++ ⊥ V :: x0, Δ)). apply BotLRule_I. apply PSBotL in H0.
      pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [] (x ++ ⊥ V :: x0, Δ) H0 DersNil).
      unfold is_mhd in i. pose (i d). simpl in l. lia.
    * exfalso. unfold is_mhd in i. apply in_split in H0. destruct H0. destruct H0.
      assert (ImpLRule [(x ++ x0, [] ++ A1 :: Δ) ; (x ++ A2 :: x0, [] ++ Δ)]
      (Γ, Δ)). rewrite H0. apply ImpLRule_I.
      pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (x ++ x0, [] ++ A1 :: Δ) I).
      pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (x ++ A2 :: x0, [] ++ Δ) I).
      pose (dlCons d0 DersNil). pose (dlCons d d1). apply PSImpL in H1.
      pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(x ++ x0, [] ++ A1 :: Δ);
      (x ++ A2 :: x0, [] ++ Δ)] (Γ, Δ) H1 d2).
      unfold is_mhd in i. subst. pose (i d3). simpl in l. lia.
    * left. exists A. reflexivity.
  + intro. intros. destruct A.
    * left. exists v. reflexivity.
    * right. reflexivity.
    * exfalso. unfold is_mhd in i. apply in_split in H0. destruct H0. destruct H0.
      assert (ImpRRule [([] ++ A1 :: Γ, x ++ A2 :: x0)]
      ([] ++ Γ, Δ)). rewrite H0. apply ImpRRule_I.
      pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) ([] ++ A1 :: Γ, x ++ A2 :: x0) I).
      pose (dlCons d DersNil). apply PSImpR in H1.
      pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [([] ++ A1 :: Γ, x ++ A2 :: x0)]
      ([] ++ Γ, Δ) H1 d0).
      unfold is_mhd in i. subst. pose (i d1). simpl in l. lia.
    * exfalso. unfold is_mhd in i. apply In_split in H0. destruct H0. destruct H0. subst.
      destruct (dec_imp_in Γ) ; destruct (dec_imp_in (x ++ Box A :: x0)).
      { repeat destruct s. repeat destruct s0. destruct s. apply in_split in i1. destruct i1.
        destruct H0.
        assert (ImpRRule [([] ++ x3 :: Γ, x5 ++ x4 :: x6)]
        (Γ, x ++ Box A :: x0)). rewrite H0. apply ImpRRule_I.
        pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) ([] ++ x3 :: Γ,
        x5 ++ x4 :: x6) I).
        pose (dlCons d DersNil). apply PSImpR in H1.
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [([] ++ x3 :: Γ,
        x5 ++ x4 :: x6)]
        (Γ, x ++ Box A :: x0) H1 d0).
        unfold is_mhd in i. subst. pose (i d1). simpl in l. lia. }
      { repeat destruct s. apply in_split in i0. destruct i0. destruct H0.
        assert (ImpLRule [(x3 ++ x4, x ++ x1 :: Box A :: x0) ;
        (x3 ++ x2 :: x4, x ++ Box A :: x0)]
        (Γ, x ++ Box A :: x0)). rewrite H0. apply ImpLRule_I.
        pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (x3 ++ x4, x ++ x1 :: Box A :: x0) I).
        pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (x3 ++ x2 :: x4, x ++ Box A :: x0) I).
        pose (dlCons d0 DersNil). pose (dlCons d d1). apply PSImpL in H1.
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(x3 ++ x4, x ++ x1 :: Box A :: x0);
        (x3 ++ x2 :: x4, x ++ Box A :: x0)] (Γ, x ++ Box A :: x0) H1 d2).
        unfold is_mhd in i. subst. pose (i d3). simpl in l. lia. }
      { repeat destruct s. apply in_split in i0. destruct i0. destruct H0.
        assert (ImpRRule [([] ++ x1 :: Γ, x3 ++ x2 :: x4)]
        (Γ, x ++ Box A :: x0)). rewrite H0. apply ImpRRule_I.
        pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) ([] ++ x1 :: Γ,
        x3 ++ x2 :: x4) I).
        pose (dlCons d DersNil). apply PSImpR in H1.
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [([] ++ x1 :: Γ,
        x3 ++ x2 :: x4)]
        (Γ, x ++ Box A :: x0) H1 d0).
        unfold is_mhd in i. subst. pose (i d1). simpl in l. lia. }
      { assert (GLRRule [((XBoxed_list (top_boxes Γ)) ++ [Box A], [A])] (Γ, x ++ Box A :: x0)). apply GLRRule_I.
        intro. intros. apply in_top_boxes in H0. destruct H0. destruct s. destruct s. destruct p. exists x1.
        auto. apply top_boxes_nobox_gen_ext.
        pose (dpI (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) (XBoxed_list (top_boxes Γ) ++ [Box A], [A]) I).
        pose (dlCons d DersNil). apply PSGLR in X.
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [(XBoxed_list (top_boxes Γ) ++ [Box A], [A])]
        (Γ, x ++ Box A :: x0) X d0).
        unfold is_mhd in i. subst. pose (i d1). simpl in l. lia.
        intro. apply PSIdP in H0.
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [] (Γ, x ++ Box A :: x0) H0 DersNil). subst.
        pose (i d1). simpl in l. lia.
        intro. apply PSIdB in H0.
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [] (Γ, x ++ Box A :: x0) H0 DersNil). subst.
        pose (i d1). simpl in l. lia.
        intro. apply PSBotL in H0.
        pose (@derI _ _ (fun _ : rel (list (MPropF V)) => True) [] (Γ, x ++ Box A :: x0) H0 DersNil). subst.
        pose (i d1). simpl in l. lia. }
- exfalso. simpl in H. lia.
Qed.
