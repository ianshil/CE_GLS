Add LoadPath "../general".

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
Require Import GLS_exch.
Require Import GLS_wkn.
Require Import GLS_PSGLS_remove_list.
Require Import GLS_PSGLS_dec.
Require Import Lia.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Lemma remove_rest_gen_ext : forall l A, rest_gen_ext [A] (remove eq_dec_form A l) l.
Proof.
induction l ; intros.
- simpl. apply univ_gen_ext_nil.
- simpl. destruct (eq_dec_form A a).
  * subst. apply univ_gen_ext_extra. apply InT_eq. apply IHl.
  * apply univ_gen_ext_cons. apply IHl.
Qed.

Theorem derrec_height_False_ge_1 : forall s, forall (D : derrec (@GLS_rules V) (fun _ => False) s), 1 <= derrec_height D.
Proof.
intros s D.
induction D.
- destruct p.
- simpl. lia.
Qed.

Lemma rest_nobox_gen_ext_trans : forall (A B : MPropF V) l0 l1 l2, ((In (Imp A B) l0) -> False) ->
                                                    (nobox_gen_ext l0 l1) ->
                                                    (rest_gen_ext [Imp A B] l2 l1) ->
                                                    (nobox_gen_ext l0 l2).
Proof.
intros A B l0 l1 l2 H1 H2. generalize dependent l2.
induction H2.
- intros. inversion X. apply univ_gen_ext_nil.
- intros. inversion X.
  * subst. apply univ_gen_ext_cons. apply IHuniv_gen_ext. intro. apply H1.
    apply in_cons. assumption. assumption.
  * subst. inversion H3. subst. exfalso. apply H1. apply in_eq.
    inversion H0.
- intros. inversion X.
  * subst. apply univ_gen_ext_extra. assumption. apply IHuniv_gen_ext ; assumption.
  * subst. apply IHuniv_gen_ext ; assumption.
Qed.

Theorem ImpR_ImpL_hpinv : forall (k : nat) concl
        (D0 : derrec (@GLS_rules V) (fun _ => False) concl),
        k = (derrec_height D0) ->
          ((forall prem, ((ImpRRule [prem] concl) ->
          existsT2 (D1 : derrec (@GLS_rules V) (fun _ => False) prem),
          derrec_height D1 <= k))) *
          ((forall prem1 prem2, ((ImpLRule [prem1; prem2] concl) ->
          existsT2 (D1 : derrec (@GLS_rules V) (fun _ => False) prem1)
                   (D2 : derrec (@GLS_rules V) (fun _ => False) prem2),
          (derrec_height D1 <= k) * (derrec_height D2 <= k)))).
Proof.
assert (DersNilF: dersrec (GLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => False) []).
apply dersrec_nil.
(* Setting up the strong induction on the height. *)
pose (strong_inductionT (fun (x:nat) => forall (concl : rel (list (MPropF V)))
  (D0 : derrec (GLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => False) concl),
x = derrec_height D0 ->
((forall prem, ((ImpRRule [prem] concl) ->
          existsT2 (D1 : derrec (@GLS_rules V) (fun _ => False) prem),
          derrec_height D1 <= x))) *
          ((forall prem1 prem2, ((ImpLRule [prem1; prem2] concl) ->
          existsT2 (D1 : derrec (@GLS_rules V) (fun _ => False) prem1)
                   (D2 : derrec (@GLS_rules V) (fun _ => False) prem2),
          (derrec_height D1 <= x) * (derrec_height D2 <= x)))))).
apply p. intros n IH. clear p.
(* Now we do the actual proof-theoretical work. *)
intros s D0. remember D0 as D0'. destruct D0.
(* D0 is a leaf *)
- destruct f.
(* D0 is ends with an application of rule *)
- intros hei. split.
{ intros prem RA. inversion RA. subst.
  inversion g ; subst.
  * inversion H. subst. assert (InT # P (??0 ++ ??1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT # P (??0 ++ A :: ??1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. assumption. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (InT # P (??0 ++ B :: ??1)). assert (InT # P (??2 ++ # P :: ??3)).
    apply InT_or_app. right. apply InT_eq. rewrite H3 in H1. apply InT_app_or in H1.
    destruct H1. apply InT_or_app. auto. inversion i. inversion H4. apply InT_or_app. right.
    apply InT_cons. assumption. apply InT_split in H1. destruct H1. destruct s.
    rewrite e0. assert (IdPRule [] (x ++ # P :: x0, x1 ++ # P :: x2)).
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[]) (x ++ # P :: x0, x1 ++ # P :: x2) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  * inversion H. subst. assert (InT (Bot V) (??0 ++ ??1)).
    rewrite <- H2. apply InT_or_app. right. apply InT_eq. assert (InT (Bot V) (??0 ++ A :: ??1)).
    apply InT_app_or in H0. destruct H0. apply InT_or_app. auto. apply InT_or_app. right.
    apply InT_cons. assumption. apply InT_split in H1. destruct H1. destruct s. rewrite e.
    assert (BotLRule [] (x ++ ??? V :: x0, ??0 ++ B :: ??1)).
    apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[]) (x ++ ??? V :: x0, ??0 ++ B :: ??1) H1 DersNilF). exists d0.
    simpl. rewrite dersrec_height_nil. lia. reflexivity.
  * inversion H. subst. apply app2_find_hole in H3. destruct H3. repeat destruct s ; destruct p ; subst.
    + inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
      assert (J1: list_exch_L (??2 ++ A0 :: ??3, ??2 ++ B0 :: ??3) (A0 :: ??0 ++ ??1, ??2 ++ B0 :: ??3)).
      assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
      rewrite H0. clear H0.
      assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). simpl. rewrite H2. reflexivity.
      rewrite H0. clear H0. apply list_exch_LI.
      assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
      pose (GLS_hpadm_list_exch_L x0 J20 J1). destruct s.
      assert (J2: list_exch_L (A0 :: ??0 ++ ??1, ??2 ++ B0 :: ??3) (??0 ++ A0 :: ??1, ??2 ++ B0 :: ??3)).
      assert ((A0 :: ??0 ++ ??1, ??2 ++ B0 :: ??3) = ([] ++ [A0] ++ ??0 ++ [] ++ ??1, ??2 ++ B0 :: ??3)).
      reflexivity. assert ((??0 ++ A0 :: ??1, ??2 ++ B0 :: ??3) = ([] ++ [] ++ ??0 ++ [A0] ++ ??1, ??2 ++ B0 :: ??3)).
      reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_LI.
      assert (J21: derrec_height x1 = derrec_height x1). reflexivity.
      pose (GLS_hpadm_list_exch_L x1 J21 J2). destruct s. exists x2.
      simpl. lia.
    + destruct x.
      { simpl in e0. inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J1: list_exch_L (??2 ++ A :: ??3, ??2 ++ B :: ??1) (A :: ??0 ++ ??1, ??2 ++ B :: ??1)).
        assert (??2 ++ A :: ??3 = [] ++ [] ++ ??2 ++ [A] ++ ??3). reflexivity.
        rewrite H0. clear H0.
        assert (A :: ??0 ++ ??1 = [] ++ [A] ++ ??2 ++ [] ++ ??3). simpl. rewrite H2. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI.
        assert (J20: derrec_height x = derrec_height x). reflexivity.
        pose (GLS_hpadm_list_exch_L x J20 J1). destruct s.
        assert (J2: list_exch_L (A :: ??0 ++ ??1, ??2 ++ B :: ??1) (??0 ++ A :: ??1, (??2 ++ []) ++ B :: ??1)).
        assert ((A :: ??0 ++ ??1, ??2 ++ B :: ??1) = ([] ++ [A] ++ ??0 ++ [] ++ ??1, ??2 ++ B :: ??1)).
        reflexivity. assert ((??0 ++ A :: ??1, (??2 ++ []) ++ B :: ??1) = ([] ++ [] ++ ??0 ++ [A] ++ ??1, ??2 ++ B :: ??1)).
        rewrite app_nil_r. reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_LI.
        assert (J21: derrec_height x0 = derrec_height x0). reflexivity.
        pose (GLS_hpadm_list_exch_L x0 J21 J2). destruct s. exists x1.
        simpl. lia. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J1: list_exch_L (??2 ++ A0 :: ??3, ??2 ++ B0 :: x ++ A ??? B :: ??1) (A0 :: ??0 ++ ??1, ??2 ++ B0 :: x ++ A ??? B :: ??1)).
        assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). simpl. rewrite H2. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI.
        assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
        pose (GLS_hpadm_list_exch_L x0 J20 J1). destruct s. simpl in IH. simpl.
        assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
        assert (J4: ImpRRule [(A0 :: ??0 ++ A :: ??1, ??2 ++ B0 :: x ++ B :: ??1)] (A0 :: ??0 ++ ??1, ??2 ++ B0 :: x ++ A ??? B :: ??1)).
        assert (A0 :: ??0 ++ A :: ??1 = (A0 :: ??0) ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = (A0 :: ??0) ++ ??1). reflexivity. rewrite H0. clear H0.
        assert (??2 ++ B0 :: x ++ B :: ??1 = (??2 ++ B0 :: x) ++ B :: ??1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (??2 ++ B0 :: x ++ A ??? B :: ??1 = (??2 ++ B0 :: x) ++ A ??? B :: ??1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpRRule_I.
        pose (IH _ J2 _ _ J3). destruct p. pose (s _ J4). clear s0. destruct s1. clear s.
        assert (existsT2 (x3 : derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
        (??0 ++ A :: ??1, (??2 ++ A0 ??? B0 :: x) ++ B :: ??1)), derrec_height x3 <= S (dersrec_height d)).
        assert (ImpRRule [(A0 :: ??0 ++ A :: ??1, ??2 ++ B0 :: x ++ B :: ??1)] (??0 ++ A :: ??1, (??2 ++ A0 ??? B0 :: x) ++ B :: ??1)).
        assert (A0 :: ??0 ++ A :: ??1 = [] ++ A0 :: ??0 ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (??0 ++ A :: ??1 = [] ++ ??0 ++ A :: ??1). reflexivity. rewrite H0. clear H0. repeat rewrite <- app_assoc.
        apply ImpRRule_I. apply ImpR in H0 ; try intro ; try apply f0 ; try auto ; try assumption.
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(A0 :: ??0 ++ A :: ??1, ??2 ++ B0 :: x ++ B :: ??1)]) (??0 ++ A :: ??1, (??2 ++ A0 ??? B0 :: x) ++ B :: ??1) H0 d0).
        exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x3. lia. }
    + destruct x.
      { simpl in e0. inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s.
        assert (J1: list_exch_L (??2 ++ A0 :: ??3, (??0 ++ []) ++ B0 :: ??3) (A0 :: ??0 ++ ??1, ??0 ++ B0 :: ??3)).
        rewrite app_nil_r.
        assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). simpl. rewrite H2. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI.
        assert (J20: derrec_height x = derrec_height x). reflexivity.
        pose (GLS_hpadm_list_exch_L x J20 J1). destruct s.
        assert (J2: list_exch_L (A0 :: ??0 ++ ??1, ??0 ++ B0 :: ??3) (??0 ++ A0 :: ??1, ??0 ++ B0 :: ??3)).
        assert ((A0 :: ??0 ++ ??1, ??0 ++ B0 :: ??3) = ([] ++ [A0] ++ ??0 ++ [] ++ ??1, ??0 ++ B0 :: ??3)).
        reflexivity. assert ((??0 ++ A0 :: ??1, ??0 ++ B0 :: ??3) = ([] ++ [] ++ ??0 ++ [A0] ++ ??1, ??0 ++ B0 :: ??3)).
        reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_LI.
        assert (J21: derrec_height x0 = derrec_height x0). reflexivity.
        pose (GLS_hpadm_list_exch_L x0 J21 J2). destruct s. exists x1.
        simpl. lia. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec_height (dersrec_height d) _ _ _ _ d J30). destruct s. simpl.
        assert (J1: list_exch_L (??2 ++ A0 :: ??3, (??0 ++ A ??? B :: x) ++ B0 :: ??3) (A0 :: ??0 ++ ??1, ??0 ++ A ??? B :: x ++ B0 :: ??3)).
        repeat rewrite <- app_assoc.
        assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). simpl. rewrite H2. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI.
        assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
        pose (GLS_hpadm_list_exch_L x0 J20 J1). destruct s. simpl in IH. simpl.
        assert (J2: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J3: derrec_height x1 = derrec_height x1). reflexivity.
        assert (J4: ImpRRule [(A0 :: ??0 ++ A :: ??1, ??0 ++ B :: x ++ B0 :: ??3)] (A0 :: ??0 ++ ??1, ??0 ++ A ??? B :: x ++ B0 :: ??3)).
        assert (A0 :: ??0 ++ A :: ??1 = (A0 :: ??0) ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = (A0 :: ??0) ++ ??1). reflexivity. rewrite H0. clear H0.
        apply ImpRRule_I.
        pose (IH _ J2 _ _ J3). destruct p. pose (s _ J4). clear s0. destruct s1. clear s.
        assert (ImpRRule [(A0 :: ??0 ++ A :: ??1, ??0 ++ B :: x ++ B0 :: ??3)] (??0 ++ A :: ??1, ??0 ++ B :: x ++ A0 ??? B0 :: ??3)).
        assert (A0 :: ??0 ++ A :: ??1 = [] ++ A0 :: ??0 ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (??0 ++ A :: ??1 = [] ++ ??0 ++ A :: ??1). reflexivity. rewrite H0. clear H0. repeat rewrite <- app_assoc.
        assert (??0 ++ B :: x ++ B0 :: ??3 = (??0 ++ B :: x) ++ B0 :: ??3). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0.
        assert (??0 ++ B :: x ++ A0 ??? B0 :: ??3 = (??0 ++ B :: x) ++ A0 ??? B0 :: ??3). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0.
        apply ImpRRule_I. apply ImpR in H0 ; try intro ; try apply f0 ; try auto ; try assumption.
        pose (dlCons x2 DersNilF).
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(A0 :: ??0 ++ A :: ??1, ??0 ++ B :: x ++ B0 :: ??3)]) (??0 ++ A :: ??1, ??0 ++ B :: x ++ A0 ??? B0 :: ??3) H0 d0).
        exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity. }
  * inversion H. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
    pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s. simpl.
    assert (J1: ImpRRule [(A :: ??2 ++ B0 :: ??3, ??0 ++ B :: ??1)] (??2 ++ B0 :: ??3, ??2 ++ ??3)).
    rewrite H3. assert (A :: ??2 ++ B0 :: ??3 = [] ++ A :: ??2 ++ B0 :: ??3). reflexivity.
    rewrite H0. clear H0. assert (??2 ++ B0 :: ??3 = [] ++ ??2 ++ B0 :: ??3). reflexivity.
    rewrite H0. clear H0. apply ImpRRule_I. simpl in IH.
    assert (J2: derrec_height x0 < S (dersrec_height d)). lia.
    assert (J3: derrec_height x0 = derrec_height x0). reflexivity.
    pose (IH _ J2 _ _ J3). destruct p. clear s0. pose (s _ J1). destruct s0. clear s.
    assert (J7: list_exch_R (??2 ++ ??3, ??2 ++ A0 :: ??3) (??2 ++ ??3, A0 :: ??0 ++ A ??? B :: ??1)).
    rewrite <- H3. assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
    rewrite H0. clear H0. assert (A0 :: ??2 ++ ??3 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). reflexivity.
    rewrite H0. clear H0. apply list_exch_RI.
    assert (J8: derrec_height x = derrec_height x). reflexivity.
    pose (GLS_hpadm_list_exch_R x J8 J7). destruct s.
    assert (J4: ImpRRule [(A :: ??2 ++ ??3, A0 :: ??0 ++ B :: ??1)] (??2 ++ ??3, A0 :: ??0 ++ A ??? B :: ??1)).
    assert (A :: ??2 ++ ??3 = [] ++ A :: ??2 ++ ??3). reflexivity.
    rewrite H0. clear H0. assert ((??2 ++ ??3, A0 :: ??0 ++ A ??? B :: ??1) = ([] ++ ??2 ++ ??3, A0 :: ??0 ++ A ??? B :: ??1)). reflexivity.
    rewrite H0. clear H0. assert (A0 :: ??0 ++ B :: ??1 = (A0 :: ??0) ++ B :: ??1). reflexivity.
    rewrite H0. clear H0. assert (A0 :: ??0 ++ A ??? B :: ??1 = (A0 :: ??0) ++ A ??? B :: ??1). reflexivity.
    rewrite H0. clear H0. apply ImpRRule_I. simpl in IH.
    assert (J5: derrec_height x2 < S (dersrec_height d)). lia.
    assert (J6: derrec_height x2 = derrec_height x2). reflexivity.
    pose (IH _ J5 _ _ J6). destruct p. clear s0. pose (s _ J4). destruct s0. clear s.
    assert (ImpLRule [(A :: ??2 ++ ??3, A0 :: ??0 ++ B :: ??1); (A :: ??2 ++ B0 :: ??3, ??0 ++ B :: ??1)]
    (A :: ??2 ++ A0 ??? B0 :: ??3, ??0 ++ B :: ??1)).
    assert (A :: ??2 ++ ??3 = (A :: ??2) ++ ??3). reflexivity. rewrite H0. clear H0.
    assert (A :: ??2 ++ B0 :: ??3 = (A :: ??2) ++ B0 :: ??3). reflexivity. rewrite H0. clear H0.
    assert (A :: ??2 ++ A0 ??? B0 :: ??3 = (A :: ??2) ++ A0 ??? B0 :: ??3). reflexivity. rewrite H0. clear H0.
    assert (??0 ++ B :: ??1 = [] ++ ??0 ++ B :: ??1). reflexivity. rewrite H0. clear H0.
    assert (A0 :: [] ++ ??0 ++ B :: ??1 = [] ++ A0 :: ??0 ++ B :: ??1). reflexivity. rewrite H0. clear H0.
    apply ImpLRule_I. pose (dlCons x1 DersNilF). pose (dlCons x3 d0).
    apply ImpL in H0.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[(A :: ??2 ++ ??3, A0 :: ??0 ++ B :: ??1); (A :: ??2 ++ B0 :: ??3, ??0 ++ B :: ??1)])
    (A :: ??2 ++ A0 ??? B0 :: ??3, ??0 ++ B :: ??1) H0 d1).
    assert (J40: list_exch_L (A :: ??2 ++ A0 ??? B0 :: ??3, ??0 ++ B :: ??1) (??0 ++ A :: ??1, ??0 ++ B :: ??1)).
    rewrite H2. assert (A :: ??0 ++ ??1 = [] ++ [A] ++ ??0 ++ [] ++ ??1). reflexivity. rewrite H1. clear H1.
    assert (??0 ++ A :: ??1 = [] ++ [] ++ ??0 ++ [A] ++ ??1). reflexivity. rewrite H1. clear H1.
    apply list_exch_LI.
    assert (J41: derrec_height d2 = derrec_height d2). reflexivity.
    pose (GLS_hpadm_list_exch_L d2 J41 J40). destruct s. exists x4. simpl in J41.
    simpl in l2. rewrite dersrec_height_nil in l2. lia. reflexivity.
  * inversion X. subst.
    assert (GLRRule [(XBoxed_list B?? ++ [Box A0], [A0])] (??0 ++ ??1, ??0 ++ ??1)).
    assert (In (Box A0) (??0 ++ ??1)).
    assert (InT (Box A0) (??2 ++ Box A0 :: ??3)). apply InT_or_app. right. apply InT_eq.
    rewrite H2 in H. apply InT_app_or in H. apply in_or_app. destruct H. apply InT_In in i. auto.
    inversion i. inversion H0. apply InT_In in H0. auto.
    apply in_splitT in H. destruct H. destruct s. rewrite e. apply GLRRule_I ; try assumption.
    simpl. simpl in IH.
    apply GLR in X1.
    assert (dersrec_height d = dersrec_height d). reflexivity.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[(XBoxed_list B?? ++ [Box A0], [A0])]) (??0 ++ ??1, ??0 ++ ??1) X1 d).
    assert (J1: wkn_L A (??0 ++ ??1, ??0 ++ ??1) (??0 ++ A :: ??1, ??0 ++ ??1)).
    apply wkn_LI.
    assert (J2: derrec_height d0 = derrec_height d0). reflexivity.
    pose (GLS_wkn_L d0 J2 J1). destruct s.
    assert (J3: wkn_R B (??0 ++ A :: ??1, ??0 ++ ??1) (??0 ++ A :: ??1, ??0 ++ B :: ??1)).
    apply wkn_RI.
    assert (J4: derrec_height x = derrec_height x). reflexivity.
    pose (GLS_wkn_R x J4 J3). destruct s. exists x0.
    pose (Nat.le_trans _ _ _ l0 l). simpl in l1. assumption. }
{ intros prem1 prem2 RA. inversion RA. subst.
  inversion g ; subst.
  * inversion H. subst. assert (InT # P (??0 ++ ??1)). assert (InT # P (??2 ++ # P :: ??3)).
    apply InT_or_app. right. apply InT_eq. rewrite H2 in H0. apply InT_or_app.
    apply InT_app_or in H0. destruct H0. auto. inversion i. inversion H1.
    auto. assert (InT # P (??0 ++ B :: ??1)).
    apply InT_app_or in H0. apply InT_or_app. destruct H0. auto. right. apply InT_cons.
    assumption. apply InT_split in H1. destruct H1. destruct s. apply InT_split in H0. destruct H0.
    destruct s. rewrite e0. rewrite e. assert (In # P (??0 ++ A :: ??1)). assert (In # P (??0 ++ ??1)).
    rewrite <- H3. apply in_or_app. right. apply in_eq. apply in_app_or in H0. apply in_or_app.
    destruct H0. auto. right. apply in_cons. assumption. apply in_splitT in H0. destruct H0.
    destruct s. rewrite e1.
    assert (IdPRule [] (x1 ++ # P :: x2, x3 ++ # P :: x4)).
    apply IdPRule_I. apply IdP in H0.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[]) (x1 ++ # P :: x2, x3 ++ # P :: x4) H0 DersNilF). exists d0.
    assert (IdPRule [] (x ++ # P :: x0, ??0 ++ ??1)). rewrite <- H3.
    apply IdPRule_I. apply IdP in H1.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[]) (x ++ # P :: x0, ??0 ++ ??1) H1 DersNilF). exists d1.
    simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
  * inversion H. subst. assert (InT (??? V) (??0 ++ ??1)). assert (InT (??? V) (??2 ++ (??? V) :: ??3)).
    apply InT_or_app. right. apply InT_eq. rewrite H2 in H0. apply InT_app_or in H0.
    apply InT_or_app. destruct H0. auto. inversion i. inversion H1. auto. assert (InT (??? V) (??0 ++ B :: ??1)).
    apply InT_app_or in H0. apply InT_or_app. destruct H0. auto. right. apply InT_cons.
    assumption. apply InT_split in H0. destruct H0. destruct s. apply InT_split in H1. destruct H1.
    destruct s. rewrite e0. rewrite e.
    assert (BotLRule [] (x ++ ??? V :: x0, ??0 ++ A :: ??1)).
    apply BotLRule_I. apply BotL in H0.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[]) (x ++ ??? V :: x0, ??0 ++ A :: ??1) H0 DersNilF). exists d0.
    assert (BotLRule [] (x1 ++ ??? V :: x2, ??0 ++ ??1)).
    apply BotLRule_I. apply BotL in H1.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[]) (x1 ++ ??? V :: x2, ??0 ++ ??1) H1 DersNilF). exists d1.
    simpl. rewrite dersrec_height_nil. split ; lia. reflexivity.
  * inversion H. subst. simpl in IH.
    assert (J0: (dersrec_height d) = (dersrec_height d)). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + assert (ImpLRule [(??2 ++ A0 :: ??1, A :: ??2 ++ B0 :: ??3) ; (??2 ++ A0 :: B :: ??1, ??2 ++ B0 :: ??3)]
      (??2 ++ A0 :: A ??? B :: ??1, ??2 ++ B0 :: ??3)). assert (??2 ++ A0 :: ??1 = (??2 ++ [A0]) ++ ??1).
      rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (??2 ++ A0 :: B :: ??1 = (??2 ++ [A0]) ++ B :: ??1). rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. assert (??2 ++ A0 :: A ??? B :: ??1 = (??2 ++ [A0]) ++ A ??? B :: ??1). rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. assert (??2 ++ B0 :: ??3 = [] ++ ??2 ++ B0 :: ??3).
      reflexivity. rewrite H0. clear H0. assert (A :: [] ++ ??2 ++ B0 :: ??3 = [] ++ A :: ??2 ++ B0 :: ??3).
      reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
      assert (J1: derrec_height x  < S (dersrec_height d)). lia.
      assert (J2: derrec_height x = derrec_height x). reflexivity.
      pose (IH (derrec_height x) J1 _ x J2). destruct p. clear s.
      pose (s0 _ _ H0). repeat destruct s. clear s0. destruct p.
      assert (ImpRRule [(??2 ++ A0 :: ??1, A :: ??2 ++ B0 :: ??3)] (??2 ++ ??1, A :: ??0 ++ ??1)).
      rewrite <- H3. assert (A :: ??2 ++ B0 :: ??3 = (A :: ??2) ++ B0 :: ??3). reflexivity.
      rewrite H1. clear H1. assert (A :: ??2 ++ A0 ??? B0 :: ??3 = (A :: ??2) ++ A0 ??? B0 :: ??3). reflexivity.
      rewrite H1. clear H1. apply ImpRRule_I.
      assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
      (??2 ++ ??1, A :: ??0 ++ ??1)), derrec_height x3 <= S (dersrec_height d)).
      apply ImpR in H1.
      pose (dlCons x1 DersNilF). pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
      (ps:=[(??2 ++ A0 :: ??1, A :: ??2 ++ B0 :: ??3)]) (??2 ++ ??1, A :: ??0 ++ ??1) H1 d0).
      exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
      destruct X.
      assert (J3: derrec_height x3 = derrec_height x3). reflexivity.
      assert (J4: list_exch_R (??2 ++ ??1, A :: ??0 ++ ??1) (??2 ++ ??1, ??0 ++ A :: ??1)).
      assert (A :: ??0 ++ ??1 = [] ++ [A] ++ ??0 ++ [] ++ ??1). reflexivity. rewrite H2. clear H2.
      assert (??0 ++ A :: ??1 = [] ++ [] ++ ??0 ++ [A] ++ ??1). reflexivity. rewrite H2. clear H2.
      apply list_exch_RI. pose (GLS_hpadm_list_exch_R x3 J3 J4). destruct s. exists x4.
      assert (ImpRRule [(??2 ++ A0 :: B :: ??1, ??2 ++ B0 :: ??3)] (??2 ++ B :: ??1, ??0 ++ ??1)).
      rewrite <- H3. apply ImpRRule_I.
      assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
      (??2 ++ B :: ??1, ??0 ++ ??1)), derrec_height x3 <= S (dersrec_height d)).
      apply ImpR in H2.
      pose (dlCons x2 DersNilF). pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
      (ps:=[(??2 ++ A0 :: B :: ??1, ??2 ++ B0 :: ??3)]) (??2 ++ B :: ??1, ??0 ++ ??1) H2 d0).
      exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
      destruct X. exists x5. simpl. split. lia. lia.
    + assert (ImpLRule [(??2 ++ A0 :: x0 ++ ??1, A :: ??2 ++ B0 :: ??3) ; (??2 ++ A0 :: x0 ++ B :: ??1, ??2 ++ B0 :: ??3)]
      (??2 ++ A0 :: x0 ++ A ??? B :: ??1, ??2 ++ B0 :: ??3)). assert (??2 ++ A0 :: x0 ++ ??1 = (??2 ++ A0 :: x0) ++ ??1).
      rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
      assert (??2 ++ A0 :: x0 ++ B :: ??1 = (??2 ++ A0 :: x0) ++ B :: ??1). rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. assert (??2 ++ A0 :: x0 ++ A ??? B :: ??1 = (??2 ++ A0 :: x0) ++ A ??? B :: ??1). rewrite <- app_assoc. reflexivity.
      rewrite H0. clear H0. assert (??2 ++ B0 :: ??3 = [] ++ ??2 ++ B0 :: ??3).
      reflexivity. rewrite H0. clear H0. assert (A :: [] ++ ??2 ++ B0 :: ??3 = [] ++ A :: ??2 ++ B0 :: ??3).
      reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
      assert (J1: derrec_height x  < S (dersrec_height d)). lia.
      assert (J2: derrec_height x = derrec_height x). reflexivity.
      pose (IH (derrec_height x) J1 _ x J2). destruct p. clear s.
      pose (s0 _ _ H0). repeat destruct s. clear s0. destruct p.
      assert (ImpRRule [(??2 ++ A0 :: x0 ++ ??1, A :: ??2 ++ B0 :: ??3)] ((??2 ++ x0) ++ ??1, A :: ??0 ++ ??1)).
      rewrite <- H3. assert (A :: ??2 ++ B0 :: ??3 = (A :: ??2) ++ B0 :: ??3). reflexivity.
      rewrite H1. clear H1. assert (A :: ??2 ++ A0 ??? B0 :: ??3 = (A :: ??2) ++ A0 ??? B0 :: ??3). reflexivity.
      rewrite H1. clear H1. rewrite <- app_assoc. apply ImpRRule_I.
      assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
      ((??2 ++ x0) ++ ??1, A :: ??0 ++ ??1)), derrec_height x3 <= S (dersrec_height d)).
      apply ImpR in H1.
      pose (dlCons x1 DersNilF). pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
      (ps:=[(??2 ++ A0 :: x0 ++ ??1, A :: ??2 ++ B0 :: ??3)]) ((??2 ++ x0) ++ ??1, A :: ??0 ++ ??1) H1 d0).
      exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
      destruct X.
      assert (J3: derrec_height x3 = derrec_height x3). reflexivity.
      assert (J4: list_exch_R ((??2 ++ x0) ++ ??1, A :: ??0 ++ ??1) ((??2 ++ x0) ++ ??1, ??0 ++ A :: ??1)).
      assert (A :: ??0 ++ ??1 = [] ++ [A] ++ ??0 ++ [] ++ ??1). reflexivity. rewrite H2. clear H2.
      assert (??0 ++ A :: ??1 = [] ++ [] ++ ??0 ++ [A] ++ ??1). reflexivity. rewrite H2. clear H2.
      apply list_exch_RI. pose (GLS_hpadm_list_exch_R x3 J3 J4). destruct s. exists x4.
      assert (ImpRRule [(??2 ++ A0 :: x0 ++ B :: ??1, ??2 ++ B0 :: ??3)] ((??2 ++ x0) ++ B :: ??1, ??0 ++ ??1)).
      rewrite <- H3. rewrite <- app_assoc. apply ImpRRule_I.
      assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
      ((??2 ++ x0) ++ B :: ??1, ??0 ++ ??1)), derrec_height x3 <= S (dersrec_height d)).
      apply ImpR in H2.
      pose (dlCons x2 DersNilF). pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
      (ps:=[(??2 ++ A0 :: x0 ++ B :: ??1, ??2 ++ B0 :: ??3)]) ((??2 ++ x0) ++ B :: ??1, ??0 ++ ??1) H2 d0).
      exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
      destruct X. exists x5. simpl. split. lia. lia.
    + destruct x0.
      { simpl in e1. subst. assert (ImpLRule [(??0 ++ A0 :: ??1, A :: ??2 ++ B0 :: ??3) ; (??0 ++ A0 :: B :: ??1, ??2 ++ B0 :: ??3)]
        ((??0 ++ []) ++ A0 :: A ??? B :: ??1, ??2 ++ B0 :: ??3)). rewrite app_nil_r. assert (??0 ++ A0 :: ??1 = (??0 ++ [A0]) ++ ??1).
        rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (??0 ++ A0 :: B :: ??1 = (??0 ++ [A0]) ++ B :: ??1). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0. assert (??0 ++ A0 :: A ??? B :: ??1 = (??0 ++ [A0]) ++ A ??? B :: ??1). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0. assert (??2 ++ B0 :: ??3 = [] ++ ??2 ++ B0 :: ??3).
        reflexivity. rewrite H0. clear H0. assert (A :: [] ++ ??2 ++ B0 :: ??3 = [] ++ A :: ??2 ++ B0 :: ??3).
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        assert (J1: derrec_height x  < S (dersrec_height d)). lia.
        assert (J2: derrec_height x = derrec_height x). reflexivity.
        pose (IH (derrec_height x) J1 _ x J2). destruct p. clear s.
        pose (s0 _ _ H0). repeat destruct s. clear s0. destruct p.
        assert (ImpRRule [(??0 ++ A0 :: ??1, A :: ??2 ++ B0 :: ??3)] (??0 ++ ??1, A :: ??0 ++ ??1)).
        rewrite <- H3. assert (A :: ??2 ++ B0 :: ??3 = (A :: ??2) ++ B0 :: ??3). reflexivity.
        rewrite H1. clear H1. assert (A :: ??2 ++ A0 ??? B0 :: ??3 = (A :: ??2) ++ A0 ??? B0 :: ??3). reflexivity.
        rewrite H1. clear H1. apply ImpRRule_I.
        assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
        (??0 ++ ??1, A :: ??0 ++ ??1)), derrec_height x3 <= S (dersrec_height d)).
        apply ImpR in H1.
        pose (dlCons x0 DersNilF). pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(??0 ++ A0 :: ??1, A :: ??2 ++ B0 :: ??3)]) (??0 ++ ??1, A :: ??0 ++ ??1) H1 d0).
        exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X.
        assert (J3: derrec_height x2 = derrec_height x2). reflexivity.
        assert (J4: list_exch_R (??0 ++ ??1, A :: ??0 ++ ??1) (??0 ++ ??1, ??0 ++ A :: ??1)).
        assert (A :: ??0 ++ ??1 = [] ++ [A] ++ ??0 ++ [] ++ ??1). reflexivity. rewrite H2. clear H2.
        assert (??0 ++ A :: ??1 = [] ++ [] ++ ??0 ++ [A] ++ ??1). reflexivity. rewrite H2. clear H2.
        apply list_exch_RI. pose (GLS_hpadm_list_exch_R x2 J3 J4). destruct s. exists x3.
        assert (ImpRRule [(??0 ++ A0 :: B :: ??1, ??2 ++ B0 :: ??3)] (??0 ++ B :: ??1, ??0 ++ ??1)).
        rewrite <- H3. apply ImpRRule_I.
        assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
        (??0 ++ B :: ??1, ??0 ++ ??1)), derrec_height x3 <= S (dersrec_height d)).
        apply ImpR in H2.
        pose (dlCons x1 DersNilF). pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(??0 ++ A0 :: B :: ??1, ??2 ++ B0 :: ??3)]) (??0 ++ B :: ??1, ??0 ++ ??1) H2 d0).
        exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x4. simpl. split. lia. lia. }
        { inversion e1. subst. assert (ImpLRule [(??0 ++ x0 ++ A0 :: ??3, A :: ??2 ++ B0 :: ??3) ; (??0 ++ B :: x0 ++ A0 :: ??3, ??2 ++ B0 :: ??3)]
          ((??0 ++ A ??? B :: x0) ++ A0 :: ??3, ??2 ++ B0 :: ??3)). rewrite <- app_assoc.
          assert (??2 ++ B0 :: ??3 = [] ++ ??2 ++ B0 :: ??3). reflexivity. rewrite H0. clear H0.
          assert (A :: [] ++ ??2 ++ B0 :: ??3 = [] ++ A :: ??2 ++ B0 :: ??3). reflexivity. rewrite H0.
          clear H0. apply ImpLRule_I.
          assert (J1: derrec_height x  < S (dersrec_height d)). lia.
          assert (J2: derrec_height x = derrec_height x). reflexivity.
          pose (IH (derrec_height x) J1 _ x J2). destruct p. clear s.
          pose (s0 _ _ H0). repeat destruct s. clear s0. destruct p.
          assert (ImpRRule [(??0 ++ x0 ++ A0 :: ??3, A :: ??2 ++ B0 :: ??3)] (??0 ++ x0 ++ ??3, A :: ??0 ++ ??1)).
          rewrite <- H3. assert (A :: ??2 ++ B0 :: ??3 = (A :: ??2) ++ B0 :: ??3). reflexivity.
          rewrite H1. clear H1. assert (A :: ??2 ++ A0 ??? B0 :: ??3 = (A :: ??2) ++ A0 ??? B0 :: ??3). reflexivity.
          rewrite H1. clear H1. assert (??0 ++ x0 ++ A0 :: ??3 = (??0 ++ x0) ++ A0 :: ??3). rewrite <- app_assoc.
          reflexivity. rewrite H1. clear H1. assert (??0 ++ x0 ++ ??3 = (??0 ++ x0) ++ ??3). rewrite <- app_assoc.
          reflexivity. rewrite H1. clear H1. apply ImpRRule_I.
          assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
          (??0 ++ x0 ++ ??3, A :: ??0 ++ ??1)), derrec_height x3 <= S (dersrec_height d)).
          apply ImpR in H1.
          pose (dlCons x1 DersNilF). pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[(??0 ++ x0 ++ A0 :: ??3, A :: ??2 ++ B0 :: ??3)]) (??0 ++ x0 ++ ??3, A :: ??0 ++ ??1) H1 d0).
          exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
          destruct X.
          assert (J3: derrec_height x3 = derrec_height x3). reflexivity.
          assert (J4: list_exch_R (??0 ++ x0 ++ ??3, A :: ??0 ++ ??1) (??0 ++ x0 ++ ??3, ??0 ++ A :: ??1)).
          assert (A :: ??0 ++ ??1 = [] ++ [A] ++ ??0 ++ [] ++ ??1). reflexivity. rewrite H2. clear H2.
          assert (??0 ++ A :: ??1 = [] ++ [] ++ ??0 ++ [A] ++ ??1). reflexivity. rewrite H2. clear H2.
          apply list_exch_RI. pose (GLS_hpadm_list_exch_R x3 J3 J4). destruct s. exists x4.
          assert (ImpRRule [(??0 ++ B :: x0 ++ A0 :: ??3, ??2 ++ B0 :: ??3)] (??0 ++ B :: x0 ++ ??3, ??0 ++ ??1)).
          rewrite <- H3. assert (??0 ++ B :: x0 ++ A0 :: ??3 = (??0 ++ B :: x0) ++ A0 :: ??3). rewrite <- app_assoc.
          reflexivity. rewrite H2. clear H2. assert (??0 ++ B :: x0 ++ ??3 = (??0 ++ B :: x0) ++ ??3). rewrite <- app_assoc.
          reflexivity. rewrite H2. clear H2. apply ImpRRule_I.
          assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
          (??0 ++ B :: x0 ++ ??3, ??0 ++ ??1)), derrec_height x3 <= S (dersrec_height d)).
          apply ImpR in H2.
          pose (dlCons x2 DersNilF). pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[(??0 ++ B :: x0 ++ A0 :: ??3, ??2 ++ B0 :: ??3)]) (??0 ++ B :: x0 ++ ??3, ??0 ++ ??1) H2 d0).
          exists d1. simpl. rewrite dersrec_height_nil. lia. reflexivity.
          destruct X. exists x5. simpl. split. lia. lia. }
  * inversion H. subst.
    apply app2_find_hole in H2. destruct H2. repeat destruct s ; destruct p ; subst.
    + inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
      pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
      assert (J1: list_exch_R (??2 ++ ??3, ??2 ++ A0 :: ??3) (??2 ++ ??3, A0 :: ??0 ++ ??1)).
      assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
      rewrite H0. clear H0.
      assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). simpl. rewrite H3. reflexivity.
      rewrite H0. clear H0. apply list_exch_RI.
      assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
      pose (GLS_hpadm_list_exch_R x0 J20 J1). destruct s.
      assert (J2: list_exch_R (??2 ++ ??3, A0 :: ??0 ++ ??1) (??2 ++ ??3, ??0 ++ A0 :: ??1)).
      assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??0 ++ [] ++ ??1).
      reflexivity. assert (??0 ++ A0 :: ??1 = [] ++ [] ++ ??0 ++ [A0] ++ ??1).
      reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_RI.
      assert (J21: derrec_height x2 = derrec_height x2). reflexivity.
      pose (GLS_hpadm_list_exch_R x2 J21 J2). destruct s. exists x3.
      assert (existsT2 (x4: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False) (??2 ++ B0 :: ??3, ??0 ++ ??1)),
      derrec_height x4 = derrec_height x1). rewrite <- H3. exists x1. reflexivity. destruct X. exists x4. split.
       simpl. lia. simpl. lia.
    + destruct x.
      { simpl in e0. inversion e0. simpl. rewrite app_nil_r. subst.
        assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (J1: list_exch_R (??2 ++ ??1, ??2 ++ A :: ??3) (??2 ++ ??1, A :: ??0 ++ ??1)).
        assert (??2 ++ A :: ??3 = [] ++ [] ++ ??2 ++ [A] ++ ??3). reflexivity.
        rewrite H0. clear H0.
        assert (A :: ??0 ++ ??1 = [] ++ [A] ++ ??2 ++ [] ++ ??3). simpl. rewrite H3. reflexivity.
        rewrite H0. clear H0. apply list_exch_RI.
        assert (J20: derrec_height x = derrec_height x). reflexivity.
        pose (GLS_hpadm_list_exch_R x J20 J1). destruct s.
        assert (J2: list_exch_R (??2 ++ ??1, A :: ??0 ++ ??1) (??2 ++ ??1, ??0 ++ A :: ??1)).
        assert (A :: ??0 ++ ??1 = [] ++ [A] ++ ??0 ++ [] ++ ??1).
        reflexivity. assert (??0 ++ A :: ??1 = [] ++ [] ++ ??0 ++ [A] ++ ??1).
        reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_RI.
        assert (J21: derrec_height x1 = derrec_height x1). reflexivity.
        pose (GLS_hpadm_list_exch_R x1 J21 J2). destruct s. exists x2.
        assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False) (??2 ++ B :: ??1, ??0 ++ ??1)),
        derrec_height x3 = derrec_height x0). rewrite <- H3. exists x0. reflexivity. destruct X. exists x3. split.
        simpl. lia. simpl. lia. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (J1: list_exch_R (??2 ++ x ++ A ??? B :: ??1, ??2 ++ A0 :: ??3) (??2 ++ x ++ A ??? B :: ??1, A0 :: ??0 ++ ??1)).
        assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). simpl. rewrite H3. reflexivity.
        rewrite H0. clear H0. apply list_exch_RI.
        assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
        pose (GLS_hpadm_list_exch_R x0 J20 J1). destruct s. simpl in IH. simpl.
        assert (J2: derrec_height x2 < S (dersrec_height d)). lia.
        assert (J3: derrec_height x2 = derrec_height x2). reflexivity.
        assert (J4: ImpLRule [(??2 ++ x ++ ??1, A0 :: ??0 ++ A :: ??1); (??2 ++ x ++ B :: ??1, A0 :: ??0 ++ ??1)]
        (??2 ++ x ++ A ??? B :: ??1, A0 :: ??0 ++ ??1)).
        assert (A0 :: ??0 ++ A :: ??1 = (A0 :: ??0) ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = (A0 :: ??0) ++ ??1). reflexivity. rewrite H0. clear H0.
        assert (??2 ++ x ++ B :: ??1 = (??2 ++ x) ++ B :: ??1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (??2 ++ x ++ A ??? B :: ??1 = (??2 ++ x) ++ A ??? B :: ??1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (??2 ++ x ++ ??1 = (??2 ++ x) ++ ??1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        pose (IH _ J2 _ _ J3). destruct p. pose (s0 _ _ J4). clear s. destruct s1. clear s0. destruct s.
        destruct p.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        assert (J7: ImpLRule [(??2 ++ B0 :: x ++ ??1, ??0 ++ A :: ??1); (??2 ++ B0 :: x ++ B :: ??1, ??0 ++ ??1)]
        (??2 ++ B0 :: x ++ A ??? B :: ??1, ??2 ++ ??3)). rewrite H3.
        assert (??2 ++ B0 :: x ++ ??1 = (??2 ++ B0 :: x) ++ ??1). rewrite <- app_assoc. reflexivity.
        rewrite H0. clear H0.
        assert (??2 ++ B0 :: x ++ B :: ??1 = (??2 ++ B0 :: x) ++ B :: ??1). rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0.
        assert (??2 ++ B0 :: x ++ A ??? B :: ??1 = (??2 ++ B0 :: x) ++ A ??? B :: ??1). repeat rewrite <- app_assoc.
        reflexivity. rewrite H0. clear H0. apply ImpLRule_I.
        pose (IH _ J5 _ _ J6). destruct p. pose (s0 _ _ J7). clear s. destruct s1. clear s0. destruct s.
        destruct p.
        assert (existsT2 (x7 : derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
        ((??2 ++ A0 ??? B0 :: x) ++ ??1, ??0 ++ A :: ??1)), derrec_height x7 <= S (dersrec_height d)).
        assert (ImpLRule [(??2 ++ x ++ ??1, A0 :: ??0 ++ A :: ??1); (??2 ++ B0 :: x ++ ??1, ??0 ++ A :: ??1)]
        ((??2 ++ A0 ??? B0 :: x) ++ ??1, ??0 ++ A :: ??1)). rewrite <- app_assoc.
        assert (A0 :: ??0 ++ A :: ??1 = [] ++ A0 :: ??0 ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (??0 ++ A :: ??1 = [] ++ ??0 ++ A :: ??1). reflexivity. rewrite H0. clear H0. repeat rewrite <- app_assoc.
        apply ImpLRule_I. apply ImpL in H0.
        pose (dlCons x5 DersNilF). pose (dlCons x3 d0).
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(??2 ++ x ++ ??1, A0 :: ??0 ++ A :: ??1); (??2 ++ B0 :: x ++ ??1, ??0 ++ A :: ??1)])
        ((??2 ++ A0 ??? B0 :: x) ++ ??1, ??0 ++ A :: ??1) H0 d1).
        exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x7.
        assert (existsT2 (x8 : derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
        ((??2 ++ A0 ??? B0 :: x) ++ B :: ??1, ??0 ++ ??1)), derrec_height x8 <= S (dersrec_height d)).
        assert (ImpLRule [(??2 ++ x ++ B :: ??1, A0 :: ??0 ++ ??1); (??2 ++ B0 :: x ++ B :: ??1, ??0 ++ ??1)]
        ((??2 ++ A0 ??? B0 :: x) ++ B :: ??1, ??0 ++ ??1)). rewrite <- app_assoc.
        assert (??0 ++ ??1 = [] ++ ??0 ++ ??1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: [] ++ ??0 ++ ??1 = [] ++ A0 :: ??0 ++ ??1). reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I. apply ImpL in H0.
        pose (dlCons x6 DersNilF). pose (dlCons x4 d0).
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(??2 ++ x ++ B :: ??1, A0 :: ??0 ++ ??1); (??2 ++ B0 :: x ++ B :: ??1, ??0 ++ ??1)])
        ((??2 ++ A0 ??? B0 :: x) ++ B :: ??1, ??0 ++ ??1) H0 d1).
        exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x8. split. lia. lia. }
    + destruct x.
      { simpl in e0. inversion e0. simpl. subst.
        assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (J1: list_exch_R ((??0 ++ []) ++ ??3, ??2 ++ A0 :: ??3) (??0 ++ ??3, A0 :: ??0 ++ ??1)).
        rewrite app_nil_r.
        assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
        rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). simpl. rewrite H3. reflexivity.
        rewrite H0. clear H0. apply list_exch_RI.
        assert (J20: derrec_height x = derrec_height x). reflexivity.
        pose (GLS_hpadm_list_exch_R x J20 J1). destruct s.
        assert (J2: list_exch_R (??0 ++ ??3, A0 :: ??0 ++ ??1) (??0 ++ ??3, ??0 ++ A0 :: ??1)).
        assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??0 ++ [] ++ ??1).
        reflexivity. assert (??0 ++ A0 :: ??1 = [] ++ [] ++ ??0 ++ [A0] ++ ??1).
        reflexivity. rewrite H1. rewrite H0. clear H1. clear H0. apply list_exch_RI.
        assert (J21: derrec_height x1 = derrec_height x1). reflexivity.
        pose (GLS_hpadm_list_exch_R x1 J21 J2). destruct s. exists x2.
        assert (existsT2 (x3: derrec GLS_rules (fun _ : rel (list (MPropF V)) => False) (??0 ++ B0 :: ??3, ??0 ++ ??1)),
        derrec_height x3 = derrec_height x0). rewrite <- H3.
        assert (??0 ++ B0 :: ??3 = (??0 ++ []) ++ B0 :: ??3). rewrite app_nil_r. reflexivity.
        rewrite H0. exists x0. reflexivity. destruct X. exists x3. split.
        simpl. lia. simpl. lia. }
      { inversion e0. subst. assert (J30: dersrec_height d = dersrec_height d). reflexivity.
        pose (@dersrec_derrec2_height (dersrec_height d) _ _ _ _ _ d J30). repeat destruct s.
        assert (J1: list_exch_R ((??0 ++ A ??? B :: x) ++ ??3, ??2 ++ A0 :: ??3) (??0 ++ A ??? B :: x ++ ??3, A0 :: ??0 ++ ??1)).
        assert (??2 ++ A0 :: ??3 = [] ++ [] ++ ??2 ++ [A0] ++ ??3). reflexivity.
        rewrite H0. clear H0. rewrite <- app_assoc.
        assert (A0 :: ??0 ++ ??1 = [] ++ [A0] ++ ??2 ++ [] ++ ??3). simpl. rewrite H3. reflexivity.
        rewrite H0. clear H0. apply list_exch_RI.
        assert (J20: derrec_height x0 = derrec_height x0). reflexivity.
        pose (GLS_hpadm_list_exch_R x0 J20 J1). destruct s. simpl in IH. simpl.
        assert (J2: derrec_height x2 < S (dersrec_height d)). lia.
        assert (J3: derrec_height x2 = derrec_height x2). reflexivity.
        assert (J4: ImpLRule [(??0 ++ x ++ ??3, A0 :: ??0 ++ A :: ??1); (??0 ++ B :: x ++ ??3, A0 :: ??0 ++ ??1)]
        (??0 ++ A ??? B :: x ++ ??3, A0 :: ??0 ++ ??1)).
        assert (A0 :: ??0 ++ A :: ??1 = (A0 :: ??0) ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: ??0 ++ ??1 = (A0 :: ??0) ++ ??1). reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I.
        pose (IH _ J2 _ _ J3). destruct p. pose (s0 _ _ J4). clear s. destruct s1. clear s0. destruct s.
        destruct p.
        assert (J5: derrec_height x1 < S (dersrec_height d)). lia.
        assert (J6: derrec_height x1 = derrec_height x1). reflexivity.
        assert (J7: ImpLRule [(??0 ++ x ++ B0 :: ??3, ??0 ++ A :: ??1); (??0 ++ B :: x ++ B0 :: ??3, ??0 ++ ??1)]
        ((??0 ++ A ??? B :: x) ++ B0 :: ??3, ??2 ++ ??3)). rewrite H3. rewrite <- app_assoc.
        apply ImpLRule_I.  pose (IH _ J5 _ _ J6). destruct p. pose (s0 _ _ J7). clear s.
        destruct s1. clear s0. destruct s. destruct p.
        assert (existsT2 (x7 : derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
        (??0 ++ x ++ A0 ??? B0 :: ??3, ??0 ++ A :: ??1)), derrec_height x7 <= S (dersrec_height d)).
        assert (ImpLRule [(??0 ++ x ++ ??3, A0 :: ??0 ++ A :: ??1); (??0 ++ x ++ B0 :: ??3, ??0 ++ A :: ??1)]
        (??0 ++ x ++ A0 ??? B0 :: ??3, ??0 ++ A :: ??1)).
        assert (A0 :: ??0 ++ A :: ??1 = [] ++ A0 :: ??0 ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (??0 ++ A :: ??1 = [] ++ ??0 ++ A :: ??1). reflexivity. rewrite H0. clear H0.
        assert (??0 ++ x ++ ??3 = (??0 ++ x) ++ ??3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (??0 ++ x ++ B0 :: ??3 = (??0 ++ x) ++ B0 :: ??3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (??0 ++ x ++ A0 ??? B0 :: ??3 = (??0 ++ x) ++ A0 ??? B0 :: ??3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I. apply ImpL in H0.
        pose (dlCons x5 DersNilF). pose (dlCons x3 d0).
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(??0 ++ x ++ ??3, A0 :: ??0 ++ A :: ??1); (??0 ++ x ++ B0 :: ??3, ??0 ++ A :: ??1)])
        (??0 ++ x ++ A0 ??? B0 :: ??3, ??0 ++ A :: ??1) H0 d1).
        exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x7.
        assert (existsT2 (x8 : derrec GLS_rules (fun _ : rel (list (MPropF V)) => False)
        (??0 ++ B :: x ++ A0 ??? B0 :: ??3, ??0 ++ ??1)), derrec_height x8 <= S (dersrec_height d)).
        assert (ImpLRule [(??0 ++ B :: x ++ ??3, A0 :: ??0 ++ ??1); (??0 ++ B :: x ++ B0 :: ??3, ??0 ++ ??1)]
        (??0 ++ B :: x ++ A0 ??? B0 :: ??3, ??0 ++ ??1)).
        assert (??0 ++ ??1 = [] ++ ??0 ++ ??1). reflexivity. rewrite H0. clear H0.
        assert (A0 :: [] ++ ??0 ++ ??1 = [] ++ A0 :: ??0 ++ ??1). reflexivity. rewrite H0. clear H0.
        assert (??0 ++ B :: x ++ ??3 = (??0 ++ B :: x) ++ ??3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (??0 ++ B :: x ++ B0 :: ??3 = (??0 ++ B :: x) ++ B0 :: ??3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        assert (??0 ++ B :: x ++ A0 ??? B0 :: ??3 = (??0 ++ B :: x) ++ A0 ??? B0 :: ??3). rewrite <- app_assoc. reflexivity. rewrite H0. clear H0.
        apply ImpLRule_I. apply ImpL in H0.
        pose (dlCons x6 DersNilF). pose (dlCons x4 d0).
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(??0 ++ B :: x ++ ??3, A0 :: ??0 ++ ??1); (??0 ++ B :: x ++ B0 :: ??3, ??0 ++ ??1)])
        (??0 ++ B :: x ++ A0 ??? B0 :: ??3, ??0 ++ ??1) H0 d1).
        exists d2. simpl. rewrite dersrec_height_nil. lia. reflexivity.
        destruct X. exists x8. split. lia. lia. }
  * inversion X. subst. pose (univ_gen_ext_splitR _ _ X0). repeat destruct s. repeat destruct p. subst.
    assert (J0: dersrec_height d = dersrec_height d). reflexivity.
    pose (dersrec_derrec_height d J0). destruct s.
    assert (GLRRule [(XBoxed_list (x ++ x0) ++ [Box A0], [A0])] (??0 ++ ??1, ??0 ++ ??1)).
    rewrite <- H2. apply GLRRule_I ; try assumption. apply univ_gen_ext_combine.
    assumption. apply univ_gen_ext_not_In_delete with (a:=A ??? B). intro.
    assert (In (A ??? B) (x ++ x0)). apply in_or_app. auto. apply H1 in H0. destruct H0.
    inversion H0. assumption.
    assert (existsT2 (D : derrec GLS_rules (fun _ : rel (list (MPropF V)) => False) (??0 ++ ??1, ??0 ++ ??1)),
    derrec_height D <= S (dersrec_height d)).
    apply GLR in X1.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[(XBoxed_list (x ++ x0) ++ [Box A0], [A0])]) (??0 ++ ??1, ??0 ++ ??1) X1 d).
    exists d0. simpl. lia.
    destruct X2.
    assert (J1: derrec_height x2 = derrec_height x2). reflexivity.
    assert (J2: wkn_L B (??0 ++ ??1, ??0 ++ ??1) (??0 ++ B :: ??1, ??0 ++ ??1)). apply wkn_LI.
    pose (GLS_wkn_L x2 J1 J2). destruct s.
    assert (J3: wkn_R A (??0 ++ ??1, ??0 ++ ??1) (??0 ++ ??1, ??0 ++ A :: ??1)). apply wkn_RI.
    pose (GLS_wkn_R x2 J1 J3). destruct s. exists x4. exists x3. simpl.
    split ; lia. }
Qed.


Theorem ImpR_inv : forall concl prem, (derrec (@GLS_rules V) (fun _ => False) concl) ->
                                      (ImpRRule [prem] concl) ->
                                      (derrec (@GLS_rules V) (fun _ => False) prem).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (ImpR_ImpL_hpinv X J1). destruct p. pose (s _ H). destruct s1. assumption.
Qed.

Theorem ImpL_inv : forall concl prem1 prem2, (derrec (@GLS_rules V) (fun _ => False) concl) ->
                                      (ImpLRule [prem1;prem2] concl) ->
                                      (derrec (@GLS_rules V) (fun _ => False) prem1) *
                                      (derrec (@GLS_rules V) (fun _ => False) prem2).
Proof.
intros.
assert (J1: derrec_height X = derrec_height X). reflexivity.
pose (ImpR_ImpL_hpinv X J1). destruct p. pose (s0 _ _ H). repeat destruct s1. auto.
Qed.
