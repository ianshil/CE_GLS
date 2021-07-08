Require Import GLS_PSGLS_calcs.
Require Import List.
Export ListNotations.

Add LoadPath "../general".

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
Require Import PSGLS_termination.
Require Import GLS_exch.
Require Import GLS_ctr.
Require Import GLS_wkn.
Require Import GLS_PSGLS_remove_list.
Require Import GLS_PSGLS_dec.
Require Import GLS_inv_ImpR_ImpL.
Require Import Lia.

Delimit Scope My_scope with M.
Open Scope My_scope.
Set Implicit Arguments.

Theorem GLS_cut_adm_main : forall n k A s Γ0 Γ1 Δ0 Δ1,
                      (n = size_form A) ->
                      (k = mhd s) ->
                      (s = (Γ0 ++ Γ1, Δ0 ++ Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) s).
Proof.
(* The proof is by induction on, first, size_form of the cut formula and on, second, the mhd
   of the sequent-conclusion. *)
(* We set up the strong induction on n properly first. *)
pose (strong_inductionT (fun (x:nat) => forall k A s Γ0 Γ1 Δ0 Δ1,
                      x = size_form A ->
                      (k = mhd s) ->
                      (s = (Γ0 ++ Γ1, Δ0 ++ Δ1)) ->
                      ((derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) s)))).
apply d. clear d. intros n PIH.
pose (strong_inductionT (fun (x:nat) => forall A s Γ0 Γ1 Δ0 Δ1,
                      n = size_form A ->
                      (x = mhd s) ->
                      (s = (Γ0 ++ Γ1, Δ0 ++ Δ1)) ->
                      ((derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) s)))).
apply d. clear d. intros k SIH.

(* Now we do the actual proof-theoretical work. *)
assert (DersNilF: dersrec (GLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => False) []).
apply dersrec_nil.
assert (DersNilT: dersrec (GLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) []).
apply dersrec_nil.
assert (PSDersNilF: dersrec (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => False) []).
apply dersrec_nil.
assert (PSDersNilT: dersrec (PSGLS_rules (V:=V)) (fun _ : rel (list (MPropF V)) => True) []).
apply dersrec_nil.

intros A s Γ0 Γ1 Δ0 Δ1 size MHD E D0 D1. inversion D0. inversion H.
inversion D1. inversion H0.

inversion X ; subst.

(* Left rule is IdP *)
- inversion H1. subst. apply list_split_form in H3. repeat destruct H3.
  * destruct s.
    + repeat destruct p. subst. inversion X1.
    (* Right rule is IdP *)
    { inversion H. subst. assert (J0 : InT (# P0) (Γ0 ++ # P :: Γ1)). rewrite <- H6. apply InT_or_app.
      right. apply InT_eq. apply InT_app_or in J0. destruct J0.
      - apply InT_split in i. destruct i. destruct s. subst. rewrite H2. repeat rewrite <- app_assoc.
        assert (IdPRule [] (x ++ (# P0 :: x0) ++ Γ1, Δ2 ++ # P0 :: Δ3)). apply IdPRule_I. apply IdP in H0.
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[]) (x ++ (# P0 :: x0) ++ Γ1, Δ2 ++ # P0 :: Δ3) H0 DersNilF). assumption.
      - inversion i.
        + inversion H3. subst.
          assert (IdPRule [] (Γ2 ++ # P0 :: Γ3, Δ2 ++ # P0 :: Δ3)). apply IdPRule_I. apply IdP in H0.
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[]) (Γ2 ++ # P0 :: Γ3, Δ2 ++ # P0 :: Δ3) H0 DersNilF). assumption.
        + apply InT_split in H3. destruct H3. destruct s. subst.
          assert (J0 : InT (# P0) (Γ2 ++ # P :: Γ3)). rewrite H2. apply InT_or_app.
          right. apply InT_or_app. right. apply InT_eq. apply InT_split in J0. destruct J0. destruct  s.
          rewrite e. assert (IdPRule [] (x1 ++ # P0 :: x2, Δ2 ++ # P0 :: Δ3)).
          apply IdPRule_I. apply IdP in H0.
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[]) (x1 ++ # P0 :: x2, Δ2 ++ # P0 :: Δ3) H0 DersNilF). assumption. }
    (* Right rule is BotL *)
    { inversion H. subst. assert (J0 : InT (Bot V) (Γ0 ++ # P :: Γ1)). rewrite <- H6. apply InT_or_app.
      right. apply InT_eq. apply InT_app_or in J0. destruct J0.
      - apply InT_split in i. destruct i. destruct s. subst. rewrite H2. rewrite <- app_assoc.
        assert (BotLRule [] (x ++ (⊥ V :: x0) ++ Γ1, Δ0 ++ Δ1)). apply BotLRule_I. apply BotL in H0.
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[]) (x ++ (⊥ V :: x0) ++ Γ1, Δ0 ++ Δ1) H0 DersNilF). assumption.
      - inversion i.
        + inversion H3.
        + apply InT_split in H3. destruct H3. destruct s. subst. rewrite H2. rewrite app_assoc.
          assert (BotLRule [] ((Γ0 ++ x) ++ ⊥ V :: x0, Δ0 ++ Δ1)). apply BotLRule_I. apply BotL in H0.
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[]) ((Γ0 ++ x) ++ ⊥ V :: x0, Δ0 ++ Δ1) H0 DersNilF). assumption. }
    (* Right rule is ImpR *)
    { inversion H. subst. assert (InT  # P (Γ0 ++ Γ1)). rewrite <- H2. apply InT_or_app.
      right. apply InT_eq. apply InT_app_or in H0. destruct H0.
      - apply InT_split in i. destruct i.
        destruct s. subst. repeat rewrite <- app_assoc in D1. simpl in D1.
        assert (E0: derrec_height D1 = derrec_height D1). reflexivity.
        assert (J0 : ctr_L # P (x ++ # P :: x0 ++ # P :: Γ1, Δ0 ++ Δ1)
        (x ++ # P :: x0 ++ Γ1, Δ0 ++ Δ1)). apply ctr_LI.
        pose (@GLS_hpadm_ctr_L (derrec_height D1) (x ++ # P :: x0 ++ # P :: Γ1, Δ0 ++ Δ1)
        D1 E0 (x ++ # P :: x0 ++ Γ1, Δ0 ++ Δ1) (# P) J0). destruct s. clear l. rewrite H2.
        rewrite <- app_assoc. rewrite H7. assumption.
      - apply InT_split in i. destruct i. destruct s. subst.
        assert (E0: derrec_height D1 = derrec_height D1). reflexivity.
        assert (J0 : ctr_L # P (Γ0 ++ # P :: x ++ # P :: x0, Δ0 ++ Δ1)
        (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1)). apply ctr_LI.
        pose (@GLS_hpadm_ctr_L (derrec_height D1) (Γ0 ++ # P :: x ++ # P :: x0, Δ0 ++ Δ1)
        D1 E0 (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1) (# P) J0). destruct s. clear l. rewrite H2.
        assert (J5 : list_exch_L (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1) (Γ0 ++ x ++ # P :: x0, Δ0 ++ Δ1)).
        assert (Γ0 ++ # P :: x ++ x0 = Γ0 ++ [# P] ++ x ++ [] ++  x0). reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ x ++ # P :: x0 = Γ0 ++ [] ++ x ++ [# P] ++ x0). reflexivity. rewrite H0. clear H0.
        apply list_exch_LI. pose (GLS_adm_list_exch_L x1 J5). rewrite H7. assumption. }
    (* Right rule is ImpL *)
    { inversion H. subst. assert (InT  # P (Γ0 ++ Γ1)). rewrite <- H2. apply InT_or_app.
      right. apply InT_eq. apply InT_app_or in H0. destruct H0.
      - apply InT_split in i. destruct i.
        destruct s. subst. repeat rewrite <- app_assoc in D1. simpl in D1.
        assert (E0: derrec_height D1 = derrec_height D1). reflexivity.
        assert (J0 : ctr_L # P (x ++ # P :: x0 ++ # P :: Γ1, Δ0 ++ Δ1)
        (x ++ # P :: x0 ++ Γ1, Δ0 ++ Δ1)). apply ctr_LI.
        pose (@GLS_hpadm_ctr_L (derrec_height D1) (x ++ # P :: x0 ++ # P :: Γ1, Δ0 ++ Δ1)
        D1 E0 (x ++ # P :: x0 ++ Γ1, Δ0 ++ Δ1) (# P) J0). destruct s. clear l. rewrite H2.
        rewrite <- app_assoc. rewrite H7. assumption.
      - apply InT_split in i. destruct i. destruct s. subst.
        assert (E0: derrec_height D1 = derrec_height D1). reflexivity.
        assert (J0 : ctr_L # P (Γ0 ++ # P :: x ++ # P :: x0, Δ0 ++ Δ1)
        (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1)). apply ctr_LI.
        pose (@GLS_hpadm_ctr_L (derrec_height D1) (Γ0 ++ # P :: x ++ # P :: x0, Δ0 ++ Δ1)
        D1 E0 (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1) (# P) J0). destruct s. clear l. rewrite H2.
        assert (J5 : list_exch_L (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1) (Γ0 ++ x ++ # P :: x0, Δ0 ++ Δ1)).
        assert (Γ0 ++ # P :: x ++ x0 = Γ0 ++ [# P] ++ x ++ [] ++  x0). reflexivity. rewrite H0. clear H0.
        assert (Γ0 ++ x ++ # P :: x0 = Γ0 ++ [] ++ x ++ [# P] ++ x0). reflexivity. rewrite H0. clear H0.
        apply list_exch_LI. pose (GLS_adm_list_exch_L x1 J5). rewrite H7. assumption. }
    (* Right rule is GLR *)
    { inversion X3. subst. assert (InT  # P (Γ0 ++ Γ1)). rewrite <- H2. apply InT_or_app.
      right. apply InT_eq. apply InT_app_or in H. destruct H.
      - apply InT_split in i. destruct i.
        destruct s. subst. repeat rewrite <- app_assoc in D1. simpl in D1.
        assert (E0: derrec_height D1 = derrec_height D1). reflexivity.
        assert (J0 : ctr_L # P (x ++ # P :: x0 ++ # P :: Γ1, Δ0 ++ Δ1)
        (x ++ # P :: x0 ++ Γ1, Δ0 ++ Δ1)). apply ctr_LI.
        pose (@GLS_hpadm_ctr_L (derrec_height D1) (x ++ # P :: x0 ++ # P :: Γ1, Δ0 ++ Δ1)
        D1 E0 (x ++ # P :: x0 ++ Γ1, Δ0 ++ Δ1) (# P) J0). destruct s. clear l. rewrite H2.
        rewrite <- app_assoc. rewrite H6. assumption.
      - apply InT_split in i. destruct i. destruct s. subst.
        assert (E0: derrec_height D1 = derrec_height D1). reflexivity.
        assert (J0 : ctr_L # P (Γ0 ++ # P :: x ++ # P :: x0, Δ0 ++ Δ1)
        (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1)). apply ctr_LI.
        pose (@GLS_hpadm_ctr_L (derrec_height D1) (Γ0 ++ # P :: x ++ # P :: x0, Δ0 ++ Δ1)
        D1 E0 (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1) (# P) J0). destruct s. clear l. rewrite H2.
        assert (J5 : list_exch_L (Γ0 ++ # P :: x ++ x0, Δ0 ++ Δ1) (Γ0 ++ x ++ # P :: x0, Δ0 ++ Δ1)).
        assert (Γ0 ++ # P :: x ++ x0 = Γ0 ++ [# P] ++ x ++ [] ++  x0). reflexivity. rewrite H. clear H.
        assert (Γ0 ++ x ++ # P :: x0 = Γ0 ++ [] ++ x ++ [# P] ++ x0). reflexivity. rewrite H. clear H.
        apply list_exch_LI. pose (GLS_adm_list_exch_L x1 J5). rewrite H6. assumption. }
    + repeat destruct s. repeat destruct p. subst. assert (IdPRule []  (Γ2 ++ # P :: Γ3, (Δ0 ++ x0) ++ # P :: Δ3)).
      apply IdPRule_I. rewrite <- app_assoc in H. apply IdP in H.
      pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
      (ps:=[])  (Γ2 ++ # P :: Γ3, Δ0 ++ x0 ++ # P :: Δ3) H DersNilF). assumption.
  * repeat destruct s. repeat destruct p. subst. assert (IdPRule [] (Γ2 ++ # P :: Γ3, Δ2 ++ # P :: x ++ Δ1)).
    apply IdPRule_I. apply IdP in H. rewrite <- app_assoc.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[]) (Γ2 ++ # P :: Γ3, Δ2 ++ (# P :: x) ++ Δ1) H DersNilF). assumption.

(* Left rule is BotL *)
- inversion H1. subst. assert (BotLRule [] (Γ2 ++ ⊥ V :: Γ3, Δ0 ++ Δ1)).
  apply BotLRule_I. apply BotL in H.
  pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
  (ps:=[]) (Γ2 ++ ⊥ V :: Γ3, Δ0 ++ Δ1) H DersNilF).
  assumption.

(* Left rule is ImpR *)
- inversion H1. subst. apply list_split_form in H3. destruct H3.
  * destruct s.
    + repeat destruct p. subst. inversion X1.
      (* Right rule is IdP *)
      { inversion H. subst. assert (J0 : InT (# P) (Γ0 ++ (A0 → B) :: Γ1)). rewrite <- H6. apply InT_or_app.
        right. apply InT_eq. apply InT_app_or in J0. destruct J0.
        - apply InT_split in i. destruct i. destruct s. subst. rewrite H2. rewrite <- app_assoc.
          assert (IdPRule [] (x ++ (# P :: x0) ++ Γ1, Δ2 ++ # P :: Δ3)). apply IdPRule_I. apply IdP in H0.
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[]) (x ++ (# P :: x0) ++ Γ1, Δ2 ++ # P :: Δ3) H0 DersNilF). assumption.
        - inversion i.
          * inversion H3.
          * apply InT_split in H3. destruct H3. destruct s. subst. rewrite H2. rewrite app_assoc.
            assert (IdPRule [] ((Γ0 ++ x) ++ # P :: x0, Δ2 ++ # P :: Δ3)). apply IdPRule_I. apply IdP in H0.
            pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
            (ps:=[]) ((Γ0 ++ x) ++ # P :: x0, Δ2 ++ # P :: Δ3) H0 DersNilF). assumption. }
      (* Right rule is BotL *)
      { inversion H. subst. rewrite H2. assert (J0 : InT (Bot V) (Γ0 ++ (A0 → B) :: Γ1)). rewrite <- H6. apply InT_or_app.
        right. apply InT_eq. apply InT_app_or in J0. destruct J0.
        - apply InT_split in i. destruct i. destruct s. subst. rewrite <- app_assoc.
          assert (BotLRule [] (x ++ (⊥ V :: x0) ++ Γ1, Δ0 ++ Δ1)). apply BotLRule_I. apply BotL in H0.
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[]) (x ++ (⊥ V :: x0) ++ Γ1, Δ0 ++ Δ1) H0 DersNilF). assumption.
        - inversion i.
          * inversion H3.
          * apply InT_split in H3. destruct H3. destruct s. subst. rewrite app_assoc.
            assert (BotLRule [] ((Γ0 ++ x) ++ ⊥ V :: x0, Δ0 ++ Δ1)). apply BotLRule_I. apply BotL in H0.
            pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
            (ps:=[]) ((Γ0 ++ x) ++ ⊥ V :: x0, Δ0 ++ Δ1) H0 DersNilF). assumption. }
      (* Right rule is ImpR *)
      { inversion H. subst. inversion X0. inversion X2. subst. clear X4. clear X6. rewrite <- H7 in D1.
        assert (J1 : list_exch_L (Γ4 ++ A :: Γ5, Δ2 ++ B0 :: Δ3) (A :: Γ0 ++ A0 → B :: Γ1, Δ2 ++ B0 :: Δ3)).
        assert (Γ4 ++ A :: Γ5 = [] ++ [] ++ Γ4 ++ [A] ++ Γ5). reflexivity. rewrite H0. clear H0.
        assert (A :: Γ0 ++ A0 → B :: Γ1 = [] ++ [A] ++ Γ4 ++ [] ++ Γ5). rewrite <- H6. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI. pose (GLS_adm_list_exch_L X5 J1). rewrite H2.
        assert (ImpRRule [([] ++ A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)] ([] ++ Γ0 ++ Γ1, Δ2 ++ A → B0 :: Δ3)). apply ImpRRule_I.
        simpl in H0.
        assert (J3: PSGLS_rules [(A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)] (Γ0 ++ Γ1, Δ2 ++ A → B0 :: Δ3)).
        apply PSImpR ; try intro ; try apply f ; try rewrite <- H7 ; try auto ; try assumption.
        assert (J31: GLS_rules [(A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)] (Γ0 ++ Γ1, Δ2 ++ A → B0 :: Δ3)).
        apply ImpR ; try assumption.
        assert (J21: In (A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3) [(A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21). rewrite <- H7 in SIH.
        assert (J5: size_form (A0 → B) = size_form (A0 → B)). reflexivity.
        assert (J6: mhd (A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3) = mhd (A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)). reflexivity.
        assert (J7 : (A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3) = ((A :: Γ0) ++ Γ1, [] ++ Δ2 ++ B0 :: Δ3)). reflexivity.
        pose (@SIH (mhd (A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)) l (A0 → B) (A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)
        (A :: Γ0) Γ1 [] (Δ2 ++ B0 :: Δ3) J5 J6 J7). simpl in d0.
        assert (J8 : list_exch_R (Γ0 ++ Γ1, Δ0 ++ A0 → B :: Δ1) (Γ0 ++ Γ1, A0 → B :: Δ2 ++ A → B0 :: Δ3)).
        assert (Δ0 ++ A0 → B :: Δ1 = [] ++ [] ++ Δ0 ++ [A0 → B] ++ Δ1). reflexivity. rewrite H3. clear H3.
        assert (A0 → B :: Δ2 ++ A → B0 :: Δ3 = [] ++ [A0 → B] ++ Δ0 ++ [] ++ Δ1). rewrite H7.
        reflexivity. rewrite H3. clear H3. apply list_exch_RI. pose (GLS_adm_list_exch_R D0 J8).
        assert (ImpRRule [([] ++ A :: Γ0 ++ Γ1, (A0 → B :: Δ2) ++ B0 :: Δ3)] ([] ++ Γ0 ++ Γ1, (A0 → B :: Δ2) ++ A → B0 :: Δ3)).
        apply ImpRRule_I. simpl in H3. pose (ImpR_inv d1 H3). pose (d0 d2 d). pose (dlCons d3 DersNilF).
        apply ImpR in H0 ; try intro ; try apply f ; try rewrite <- H7 ; try auto ; try assumption.
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(A :: Γ0 ++ Γ1, Δ2 ++ B0 :: Δ3)]) (Γ0 ++ Γ1, Δ2 ++ A → B0 :: Δ3) H0 d4). assumption. }
      (* Right rule is ImpL *)
      { inversion H. subst. inversion X0. inversion X2. subst. clear X4. inversion X6. subst. clear X7.
        clear X6. apply list_split_form in H6. destruct H6.
        - destruct s.
          * repeat destruct p. inversion e0. subst. rewrite H2.
            assert (J1 : list_exch_L (Γ2 ++ A0 :: Γ3, Δ0 ++ B :: Δ1) (A0 :: Γ0 ++ Γ1, Δ0 ++ B :: Δ1)).
            assert (Γ2 ++ A0 :: Γ3 = [] ++ [] ++ Γ2 ++ [A0] ++ Γ3). reflexivity. rewrite H0. clear H0.
            assert (A0 :: Γ0 ++ Γ1 = [] ++ [A0] ++ Γ2 ++ [] ++ Γ3). rewrite <- H2. reflexivity.
            rewrite H0. clear H0. apply list_exch_LI. pose (GLS_adm_list_exch_L X3 J1).
            assert (J2 : list_exch_R (A0 :: Γ0 ++ Γ1, Δ0 ++ B :: Δ1) (A0 :: Γ0 ++ Γ1, B :: Δ2 ++ Δ3)).
            assert (Δ0 ++ B :: Δ1 = [] ++ [] ++ Δ0 ++ [B] ++ Δ1). reflexivity. rewrite H0. clear H0.
            assert (B :: Δ2 ++ Δ3 = [] ++ [B] ++ Δ0 ++ [] ++ Δ1). rewrite H7. reflexivity. rewrite H0. clear H0.
            apply list_exch_RI. pose (GLS_adm_list_exch_R d J2).
            assert (J3: size_form A0 < size_form (A0 → B)). simpl. lia.
            assert (J4: size_form A0 = size_form A0). reflexivity.
            assert (J5: mhd (Γ2 ++ Γ3, B :: Δ2 ++ Δ3) = mhd (Γ2 ++ Γ3, B :: Δ2 ++ Δ3)). reflexivity.
            assert (J6: (Γ2 ++ Γ3, B :: Δ2 ++ Δ3) = ([] ++ Γ2 ++ Γ3, (B :: Δ2) ++ Δ3)). reflexivity.
            pose (PIH _ J3 (mhd (Γ2 ++ Γ3, B :: Δ2 ++ Δ3)) A0 (Γ2 ++ Γ3, B :: Δ2 ++ Δ3) [] (Γ2 ++ Γ3)
            (B :: Δ2) Δ3 J4 J5 J6). simpl in d1.
            assert (J7 : wkn_R B (Γ2 ++ Γ3, Δ2 ++ A0 :: Δ3) (Γ2 ++ Γ3, B :: Δ2 ++ A0 :: Δ3)).
            assert ((Γ2 ++ Γ3, Δ2 ++ A0 :: Δ3) = (Γ2 ++ Γ3, [] ++ Δ2 ++ A0 :: Δ3)). reflexivity. rewrite H0. clear H0.
            assert ((Γ2 ++ Γ3, B :: Δ2 ++ A0 :: Δ3) = (Γ2 ++ Γ3, [] ++ B :: Δ2 ++ A0 :: Δ3)).
            reflexivity. rewrite H0. clear H0. apply wkn_RI. rewrite <- H2 in X5.
            assert (J8 : derrec_height X5 = derrec_height X5).
            reflexivity. pose (GLS_wkn_R X5 J8 J7). destruct s. rewrite <- H2 in d0. pose (d1 x d0).
            assert (J9: size_form B < size_form (A0 → B)). simpl. lia.
            assert (J10: size_form B = size_form B). reflexivity.
            assert (J11: mhd (Γ2 ++ Γ3, Δ2 ++ Δ3) = mhd (Γ2 ++ Γ3, Δ2 ++ Δ3)). reflexivity.
            assert (J12: (Γ2 ++ Γ3, Δ2 ++ Δ3) = (Γ2 ++ Γ3, [] ++ Δ2 ++ Δ3)). reflexivity.
            pose (PIH _ J9 (mhd (Γ2 ++ Γ3, Δ2 ++ Δ3)) B (Γ2 ++ Γ3, Δ2 ++ Δ3) Γ2 Γ3
            [] (Δ2 ++ Δ3) J10 J11 J12). simpl in d3.
            assert (J30 : list_exch_L (Γ0 ++ B :: Γ1, Δ2 ++ Δ3) (B :: Γ2 ++ Γ3, Δ2 ++ Δ3)).
            assert (Γ0 ++ B :: Γ1 = [] ++ [] ++ Γ0 ++ [B] ++ Γ1). reflexivity. rewrite H0. clear H0.
            assert (B :: Γ2 ++ Γ3 = [] ++ [B] ++ Γ0 ++ [] ++ Γ1). rewrite H2. reflexivity.
            rewrite H0. clear H0. apply list_exch_LI. pose (GLS_adm_list_exch_L X4 J30).
            assert (J40 : list_exch_L (B :: Γ2 ++ Γ3, Δ2 ++ Δ3) (Γ2 ++ B :: Γ3, Δ2 ++ Δ3)).
            assert (Γ2 ++ B :: Γ3 = [] ++ [] ++ Γ2 ++ [B] ++ Γ3). reflexivity. rewrite H0. clear H0.
            assert (B :: Γ2 ++ Γ3 = [] ++ [B] ++ Γ2 ++ [] ++ Γ3). reflexivity. rewrite H0. clear H0.
            apply list_exch_LI. pose (GLS_adm_list_exch_L d4 J40). pose (d3 d2 d5). rewrite <- H2. assumption.
          * repeat destruct s. repeat destruct p. subst. rewrite H2. repeat rewrite <- app_assoc in X5. repeat rewrite <- app_assoc in X4.
            simpl in X4. simpl in X5.
            assert (J1 : list_exch_R (Γ0 ++ x0 ++ A → B0 :: Γ5, Δ0 ++ A0 → B :: Δ1) (Γ0 ++ x0 ++ A → B0 :: Γ5, A0 → B :: Δ2 ++ Δ3)).
            assert (Δ0 ++ A0 → B :: Δ1 = [] ++ [] ++ Δ0 ++ [A0 → B] ++ Δ1). reflexivity. rewrite H0. clear H0.
            assert (A0 → B :: Δ2 ++ Δ3 = [] ++ [A0 → B] ++ Δ0 ++ [] ++ Δ1). rewrite H7. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
            pose (GLS_adm_list_exch_R D0 J1).
            assert (ImpLRule [((Γ0 ++ x0) ++ Γ5, Δ2 ++ A :: Δ3); ((Γ0 ++ x0) ++ B0 :: Γ5, Δ2 ++ Δ3)] ((Γ0 ++ x0) ++ A → B0 :: Γ5, Δ2 ++ Δ3)).
            apply ImpLRule_I. simpl in H0. repeat rewrite <- app_assoc in H0.
            assert (J3: PSGLS_rules [(Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3)] (Γ0 ++ x0 ++ A → B0 :: Γ5, Δ2 ++ Δ3)).
            apply PSImpL ; try intro ; try apply f ; try rewrite <- H7 ; try repeat rewrite <- app_assoc ; try auto ; try assumption.
            assert (J21: In (Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3) [(Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3)]). apply in_eq.
            pose (RA_mhd_decreases J3 _ J21). rewrite <- H7 in SIH.
            assert (J5: size_form (A0 → B) = size_form (A0 → B)). reflexivity.
            assert (J6: mhd (Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3) = mhd (Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3)). reflexivity.
            assert (J7 : (Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3) = (Γ0 ++ x0 ++ Γ5, [] ++ Δ2 ++ A :: Δ3)). reflexivity.
            pose (@SIH (mhd (Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3)) l (A0 → B) (Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3)
            Γ0 (x0 ++ Γ5) [] (Δ2 ++ A :: Δ3) J5 J6 J7). simpl in d0.
            assert (J22: In (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3) [(Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3)]).
            apply in_cons. apply in_eq. pose (RA_mhd_decreases J3 _ J22).
            assert (J8: size_form (A0 → B) = size_form (A0 → B)). reflexivity.
            assert (J9: mhd (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3) = mhd (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3)). reflexivity.
            assert (J10: (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3) = (Γ0 ++ x0 ++ B0 :: Γ5, [] ++ Δ2 ++ Δ3)). reflexivity.
            pose (@SIH (mhd (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3)) l0 (A0 → B) (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3)
            Γ0 (x0 ++ B0 :: Γ5) [] (Δ2 ++ Δ3) J8 J9 J10). simpl in d1.
            assert (ImpLRule [((Γ0 ++ x0) ++ Γ5, (A0 → B :: Δ2) ++ A :: Δ3); ((Γ0 ++ x0) ++ B0 :: Γ5, (A0 → B :: Δ2) ++ Δ3)] ((Γ0 ++ x0) ++ A → B0 :: Γ5, (A0 → B :: Δ2) ++ Δ3)).
            apply ImpLRule_I. repeat rewrite <- app_assoc in H3. pose (ImpL_inv d H3). destruct p.
            pose (d0 d2 X5). pose (d1 d3 X4). apply ImpL in H0 ; try intro ; try apply f ; try repeat rewrite <- app_assoc ; try rewrite <- H7 ;
            try repeat rewrite app_nil_r ; try auto ; try assumption. pose (dlCons d5 DersNilF). pose (dlCons d4 d6).
            pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
            (ps:=[(Γ0 ++ x0 ++ Γ5, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B0 :: Γ5, Δ2 ++ Δ3)]) (Γ0 ++ x0 ++ A → B0 :: Γ5, Δ2 ++ Δ3) H0 d7).
            assumption.
        - repeat destruct s. repeat destruct p. subst. rewrite H2. rewrite <- app_assoc. rewrite <- app_assoc in D0.
          assert (J1 : list_exch_R (Γ4 ++ (A → B0 :: x) ++ Γ1, Δ0 ++ A0 → B :: Δ1) (Γ4 ++ (A → B0 :: x) ++ Γ1, A0 → B :: Δ2 ++ Δ3)).
          assert (Δ0 ++ A0 → B :: Δ1 = [] ++ [] ++ Δ0 ++ [A0 → B] ++ Δ1). reflexivity. rewrite H0. clear H0.
          assert (A0 → B :: Δ2 ++ Δ3 = [] ++ [A0 → B] ++ Δ0 ++ [] ++ Δ1). rewrite H7. reflexivity. rewrite H0. clear H0. apply list_exch_RI.
          pose (GLS_adm_list_exch_R D0 J1).
          assert (ImpLRule [(Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ4 ++ (B0 :: x) ++ Γ1, Δ2 ++ Δ3)] (Γ4 ++ (A → B0 :: x) ++ Γ1, Δ2 ++ Δ3)).
          apply ImpLRule_I. simpl in H0.
          assert (J3: PSGLS_rules [(Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3)] (Γ4 ++ A → B0 :: x ++ Γ1, Δ2 ++ Δ3)).
          apply PSImpL ; try intro ; try apply f ; try rewrite <- H7 ; try repeat rewrite <- app_assoc ; try auto ; try assumption.
          assert (J21: In (Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3) [(Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3)]). apply in_eq.
          pose (RA_mhd_decreases J3 _ J21). rewrite <- H7 in SIH. rewrite <- app_assoc in SIH.
          assert (J5: size_form (A0 → B) = size_form (A0 → B)). reflexivity.
          assert (J6: mhd (Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3) = mhd (Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3)). reflexivity.
          assert (J7 : (Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3) = ((Γ4 ++ x) ++ Γ1, [] ++ Δ2 ++ A :: Δ3)). rewrite <- app_assoc. reflexivity.
          pose (@SIH (mhd (Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3)) l (A0 → B) (Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3)
          (Γ4 ++ x) Γ1 [] (Δ2 ++ A :: Δ3) J5 J6 J7). simpl in d0. repeat rewrite <- app_assoc in d0.
          assert (J22: In (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3) [(Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3)]).
          apply in_cons. apply in_eq. pose (RA_mhd_decreases J3 _ J22).
          assert (J8: size_form (A0 → B) = size_form (A0 → B)). reflexivity.
          assert (J9: mhd (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3) = mhd (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3)). reflexivity.
          assert (J10: (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3) = ((Γ4 ++ B0 :: x) ++ Γ1, [] ++ Δ2 ++ Δ3)). rewrite <- app_assoc. reflexivity.
          pose (@SIH (mhd (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3)) l0 (A0 → B) (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3)
          (Γ4 ++ B0 :: x) Γ1 [] (Δ2 ++ Δ3) J8 J9 J10). simpl in d1.
          assert (ImpLRule [(Γ4 ++ x ++ Γ1, (A0 → B :: Δ2) ++ A :: Δ3); (Γ4 ++ (B0 :: x) ++ Γ1, (A0 → B :: Δ2) ++ Δ3)] (Γ4 ++ (A → B0 :: x) ++ Γ1, (A0 → B :: Δ2) ++ Δ3)).
          apply ImpLRule_I. repeat rewrite <- app_assoc in H3. pose (ImpL_inv d H3). destruct p.
          pose (d0 d2 X5). repeat rewrite <- app_assoc in d1. pose (d1 d3 X4). apply ImpL in H0 ; try intro ; try apply f ; try repeat rewrite <- app_assoc ; try rewrite <- H7 ;
          try repeat rewrite app_nil_r ; try auto ; try assumption. pose (dlCons d5 DersNilF). pose (dlCons d4 d6).
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[(Γ4 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ4 ++ B0 :: x ++ Γ1, Δ2 ++ Δ3)]) (Γ4 ++ (A → B0 :: x) ++ Γ1, Δ2 ++ Δ3) H0 d7).
          assumption. }
      (* Right rule is GLR *)
      { inversion X3. subst. rewrite H2.
        assert (GLRRule [(XBoxed_list BΓ ++ [Box A], [A])] (Γ0 ++ Γ1, Δ2 ++ Box A :: Δ3)).
        apply GLRRule_I ; try assumption.
        apply univ_gen_ext_splitR in X4. destruct X4. destruct s. repeat destruct p. subst.
        apply univ_gen_ext_combine. assumption. apply univ_gen_ext_not_In_delete in u0. assumption.
        intro. assert (In (A0 → B) (x ++ x0)). apply in_or_app. auto. apply H5 in H0. destruct H0.
        inversion H0. apply GLR in X5.
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(XBoxed_list BΓ ++ [Box A], [A])]) (Γ0 ++ Γ1, Δ2 ++ Box A :: Δ3) X5 X2).
        assumption. }
    + repeat destruct s. repeat destruct p. subst.
      assert (J5 : list_exch_L (Γ0 ++ A :: Γ1, Δ0 ++ x0 ++ A0 → B :: Δ3) (A :: Γ2 ++ Γ3, Δ0 ++ x0 ++ A0 → B :: Δ3)).
      rewrite H2. assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
      assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
      apply list_exch_LI. pose (GLS_adm_list_exch_L D1 J5).
      assert (ImpRRule [((A :: Γ2) ++ A0 :: Γ3, (Δ0 ++ x0) ++ B :: Δ3)] ((A :: Γ2) ++ Γ3, (Δ0 ++ x0) ++ A0 → B :: Δ3)).
      apply ImpRRule_I. repeat rewrite <- app_assoc in H. pose (ImpR_inv d H).
      assert (ImpRRule [(Γ2 ++ A0 :: Γ3, (Δ0 ++ x0) ++ B :: Δ3)] (Γ2 ++ Γ3, (Δ0 ++ x0) ++ A0 → B :: Δ3)).
      apply ImpRRule_I. repeat rewrite <- app_assoc in H0.
      assert (PSGLS_rules [(Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3)] (Γ2 ++ Γ3, Δ0 ++ x0 ++ A0 → B :: Δ3)).
      apply PSImpR ; try intro ; try apply f ; try rewrite <- H2 ; try rewrite <- app_assoc ; try auto ; try assumption.
      assert (GLS_rules [(Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3)] (Γ2 ++ Γ3, Δ0 ++ x0 ++ A0 → B :: Δ3)).
      apply ImpR. assumption.
      assert (J21: In (Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3) [(Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3)]). apply in_eq.
      pose (RA_mhd_decreases X3 (Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3) J21).
      assert (J2 : mhd (Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3) = mhd (Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3)). reflexivity.
      assert (J3 : size_form A = size_form A). reflexivity.
      assert (J4 : (Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3) = ([] ++ Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3)).
      repeat rewrite <- app_assoc. reflexivity. rewrite <- H2 in SIH.
      pose (@SIH (mhd (Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3)) l A (Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3)
      [] (Γ2 ++ A0 :: Γ3) Δ0 (x0 ++ B :: Δ3) J3 J2 J4). repeat rewrite <- app_assoc in d1. simpl in d1.
      inversion X0. subst. clear X6. repeat rewrite <- app_assoc in X5. pose (d1 X5 d0). pose (dlCons d2 DersNilF).
      pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
      (ps:=[(Γ2 ++ A0 :: Γ3, Δ0 ++ x0 ++ B :: Δ3)]) (Γ2 ++ Γ3, Δ0 ++ x0 ++ A0 → B :: Δ3) X4 d3). assumption.
  * repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc. repeat rewrite <- app_assoc in D1.
    assert (J5 : list_exch_L (Γ0 ++ A :: Γ1, Δ2 ++ (A0 → B :: x) ++ Δ1) (A :: Γ2 ++ Γ3, Δ2 ++ (A0 → B :: x) ++ Δ1)).
    assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1). reflexivity. rewrite H. clear H.
    assert (A :: Γ2 ++ Γ3 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). rewrite H2. reflexivity. rewrite H. clear H.
    apply list_exch_LI. pose (GLS_adm_list_exch_L D1 J5).
    assert (ImpRRule [((A :: Γ2) ++ A0 :: Γ3, Δ2 ++ B :: x ++ Δ1)] ((A :: Γ2) ++ Γ3, Δ2 ++ (A0 → B :: x) ++ Δ1)).
    apply ImpRRule_I. repeat rewrite <- app_assoc in H. pose (ImpR_inv d H).
    assert (ImpRRule [(Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1)] (Γ2 ++ Γ3, Δ2 ++ (A0 → B :: x) ++ Δ1)).
    apply ImpRRule_I.
    assert (PSGLS_rules [(Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1)] (Γ2 ++ Γ3, Δ2 ++ (A0 → B :: x) ++ Δ1)).
    apply PSImpR ; try intro ; try apply f ; try repeat rewrite <- app_assoc ; try rewrite <- H2 ; try auto ; try assumption.
    assert (GLS_rules [(Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1)] (Γ2 ++ Γ3, Δ2 ++ (A0 → B :: x) ++ Δ1)).
    apply ImpR ; try assumption.
    assert (J21: In (Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1) [(Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1)]). apply in_eq.
    pose (RA_mhd_decreases X3 (Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1) J21). rewrite <- H2 in SIH.
    assert (J2 : mhd (Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1) = mhd (Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1)).
    repeat rewrite <- app_assoc. reflexivity.
    assert (J3 : size_form A = size_form A). reflexivity.
    assert (J4 : (Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1) = ([] ++ Γ2 ++ A0 :: Γ3, (Δ2 ++ B :: x) ++ Δ1)).
    repeat rewrite <- app_assoc. reflexivity. repeat rewrite <- app_assoc in SIH.
    pose (@SIH (mhd (Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1)) l A (Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1)
    [] (Γ2 ++ A0 :: Γ3) (Δ2 ++ (B :: x)) Δ1 J3 J2 J4). simpl in d1. repeat rewrite <- app_assoc in d1.
    inversion X0. subst. pose (d1 X5 d0). pose (dlCons d2 DersNilF).
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[(Γ2 ++ A0 :: Γ3, Δ2 ++ (B :: x) ++ Δ1)]) (Γ2 ++ Γ3, Δ2 ++ (A0 → B :: x) ++ Δ1) X4 d3). assumption.

(* Left rule is ImpL *)
- inversion H1. subst. inversion X0. inversion X4. subst. clear X6. clear X4.
  assert (J5 : list_exch_L (Γ0 ++ A :: Γ1, Δ0 ++ Δ1) (A :: Γ2 ++ A0 → B :: Γ3, Δ0 ++ Δ1)).
  rewrite H2. assert (Γ0 ++ A :: Γ1 = [] ++ [] ++ Γ0 ++ [A] ++ Γ1).
  reflexivity. rewrite H. clear H.
  assert (A :: Γ0 ++ Γ1 = [] ++ [A] ++ Γ0 ++ [] ++ Γ1). reflexivity. rewrite H. clear H.
  apply list_exch_LI. pose (GLS_adm_list_exch_L D1 J5). rewrite H3 in X5.
  assert (J40 : list_exch_R (Γ2 ++ Γ3, Δ2 ++ A0 :: Δ3) (Γ2 ++ Γ3, A0 :: Δ0 ++ A :: Δ1)).
  rewrite <- H3. assert (Δ2 ++ A0 :: Δ3 = [] ++ [] ++ Δ2 ++ [A0] ++ Δ3).
  reflexivity. rewrite H. clear H.
  assert (A0 :: Δ2 ++ Δ3 = [] ++ [A0] ++ Δ2 ++ [] ++ Δ3). reflexivity. rewrite H. clear H.
  apply list_exch_RI. pose (GLS_adm_list_exch_R X3 J40).
  assert (ImpLRule [(A :: Γ2 ++ Γ3, [] ++ A0 :: Δ0 ++ Δ1); (A :: Γ2 ++ B :: Γ3, [] ++ Δ0 ++ Δ1)] (A :: Γ2 ++ A0 → B :: Γ3, [] ++ Δ0 ++ Δ1)).
  assert ((A :: Γ2 ++ A0 → B :: Γ3, [] ++ Δ0 ++ Δ1) = ((A :: Γ2) ++ A0 → B :: Γ3, [] ++ Δ0 ++ Δ1)). reflexivity.
  rewrite H. clear H.
  assert ((A :: Γ2 ++ Γ3, [] ++ A0 :: Δ0 ++ Δ1) = ((A :: Γ2) ++ Γ3, [] ++ A0 :: Δ0 ++ Δ1)). reflexivity.
  rewrite H. clear H.
  assert ((A :: Γ2 ++ B :: Γ3, [] ++ Δ0 ++ Δ1) = ((A :: Γ2) ++ B :: Γ3, [] ++ Δ0 ++ Δ1)). reflexivity.
  rewrite H. clear H. apply ImpLRule_I. simpl in H. pose (ImpL_inv d H). destruct p.
  assert (ImpLRule [(Γ2 ++ Γ3, [] ++ A0 :: Δ0 ++ Δ1); (Γ2 ++ B :: Γ3, [] ++ Δ0 ++ Δ1)] (Γ2 ++ A0 → B :: Γ3, [] ++ Δ0 ++ Δ1)).
  apply ImpLRule_I. simpl in H0.
  assert (PSGLS_rules [(Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)] (Γ2 ++ A0 → B :: Γ3, Δ0 ++ Δ1)).
  apply PSImpL ; try intro ; try apply f ; try rewrite <- H2 ; try rewrite <- app_assoc ; try auto ; try assumption.
  assert (GLS_rules [(Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)] (Γ2 ++ A0 → B :: Γ3, Δ0 ++ Δ1)).
  apply ImpL. assumption.
  assert (J21: In (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1) [(Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)]).
  apply in_eq. pose (RA_mhd_decreases X4 (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1) J21).
  assert (J2 : mhd (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1) = mhd (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1)). reflexivity.
  assert (J3 : size_form A = size_form A). reflexivity.
  assert (J4 : (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1) = ([] ++ Γ2 ++ Γ3, (A0 :: Δ0) ++ Δ1)).
  repeat rewrite <- app_assoc. reflexivity. rewrite <- H2 in SIH.
  pose (@SIH (mhd (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1)) l A (Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1)
  [] (Γ2 ++ Γ3) (A0 :: Δ0) Δ1 J3 J2 J4). repeat rewrite <- app_assoc in d3. simpl in d3.
  pose (d3 d0 d1).
  assert (J31: In (Γ2 ++ B :: Γ3, Δ0 ++ Δ1) [(Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)]).
  apply in_cons. apply in_eq. pose (RA_mhd_decreases X4 (Γ2 ++ B :: Γ3, Δ0 ++ Δ1) J31).
  assert (J32 : mhd (Γ2 ++ B :: Γ3, Δ0 ++ Δ1) = mhd (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)). reflexivity.
  assert (J33 : size_form A = size_form A). reflexivity.
  assert (J34 : (Γ2 ++ B :: Γ3, Δ0 ++ Δ1) = ([] ++ Γ2 ++ B :: Γ3, Δ0 ++ Δ1)).
  repeat rewrite <- app_assoc. reflexivity.
  pose (@SIH (mhd (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)) l0 A (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)
  [] (Γ2 ++ B :: Γ3) Δ0 Δ1 J33 J32 J34). repeat rewrite <- app_assoc in d5. simpl in d5.
  pose (d5 X5 d2). pose (dlCons d6 DersNilF). pose (dlCons d4 d7).
  pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
  (ps:=[(Γ2 ++ Γ3, A0 :: Δ0 ++ Δ1); (Γ2 ++ B :: Γ3, Δ0 ++ Δ1)]) (Γ2 ++ A0 → B :: Γ3, Δ0 ++ Δ1) X6 d8). assumption.

(* Left rule is GLR *)
- inversion X3. subst. apply list_split_form in H2. destruct H2.
  * destruct s.
    + repeat destruct p. subst. inversion X1.
      (* Right rule is IdP *)
      { inversion H. subst. assert (J0 : InT (# P) (Γ0 ++ Box A0 :: Γ1)). rewrite <- H5. apply InT_or_app.
        right. apply InT_eq. apply InT_app_or in J0. destruct J0.
        - apply InT_split in i. destruct i. destruct s. subst. rewrite <- app_assoc.
          assert (IdPRule [] (x ++ (# P :: x0) ++ Γ1, Δ2 ++ # P :: Δ3)). apply IdPRule_I. apply IdP in H0.
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[]) (x ++ (# P :: x0) ++ Γ1, Δ2 ++ # P :: Δ3) H0 DersNilF). assumption.
        - inversion i.
          * inversion H2.
          * apply InT_split in H2. destruct H2. destruct s. subst. rewrite app_assoc.
            assert (IdPRule [] ((Γ0 ++ x) ++ # P :: x0, Δ2 ++ # P :: Δ3)). apply IdPRule_I. apply IdP in H0.
            pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
            (ps:=[]) ((Γ0 ++ x) ++ # P :: x0, Δ2 ++ # P :: Δ3) H0 DersNilF). assumption. }
      (* Right rule is BotL *)
      { inversion H. subst. assert (J0 : InT (Bot V) (Γ0 ++ Box A0 :: Γ1)). rewrite <- H5. apply InT_or_app.
        right. apply InT_eq. apply InT_app_or in J0. destruct J0.
        - apply InT_split in i. destruct i. destruct s. subst. rewrite <- app_assoc.
          assert (BotLRule [] (x ++ (⊥ V :: x0) ++ Γ1, Δ0 ++ Δ1)). apply BotLRule_I. apply BotL in H0.
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[]) (x ++ (⊥ V :: x0) ++ Γ1, Δ0 ++ Δ1) H0 DersNilF). assumption.
        - inversion i.
          * inversion H2.
          * apply InT_split in H2. destruct H2. destruct s. subst. rewrite app_assoc.
            assert (BotLRule [] ((Γ0 ++ x) ++ ⊥ V :: x0, Δ0 ++ Δ1)). apply BotLRule_I. apply BotL in H0.
            pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
            (ps:=[]) ((Γ0 ++ x) ++ ⊥ V :: x0, Δ0 ++ Δ1) H0 DersNilF). assumption. }
      (* Right rule is ImpR *)
      { inversion H. subst. inversion X2. subst. clear X6. rewrite <- H6 in D1.
        assert (J1 : list_exch_L (Γ2 ++ A :: Γ3, Δ2 ++ B :: Δ3) (A :: Γ0 ++ Box A0 :: Γ1, Δ2 ++ B :: Δ3)).
        assert (Γ2 ++ A :: Γ3 = [] ++ [] ++ Γ2 ++ [A] ++ Γ3). reflexivity. rewrite H0. clear H0.
        assert (A :: Γ0 ++ Box A0 :: Γ1 = [] ++ [A] ++ Γ2 ++ [] ++ Γ3). rewrite <- H5. reflexivity.
        rewrite H0. clear H0. apply list_exch_LI. pose (GLS_adm_list_exch_L X5 J1).
        assert (ImpRRule [([] ++ A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)] ([] ++ Γ0 ++ Γ1, Δ2 ++ A → B :: Δ3)). apply ImpRRule_I.
        simpl in H0.
        assert (J3: PSGLS_rules [(A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)] (Γ0 ++ Γ1, Δ2 ++ A → B :: Δ3)).
        apply PSImpR ; try intro ; try apply f ; try rewrite <- H6 ; try auto ; try assumption.
        assert (J31: GLS_rules [(A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)] (Γ0 ++ Γ1, Δ2 ++ A → B :: Δ3)).
        apply ImpR ; try assumption.
        assert (J21: In (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3) [(A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)]). apply in_eq.
        pose (RA_mhd_decreases J3 _ J21). rewrite <- H6 in SIH.
        assert (J5: size_form (Box A0) = size_form (Box A0)). reflexivity.
        assert (J6: mhd (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3) = mhd (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)). reflexivity.
        assert (J7 : (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3) = ((A :: Γ0) ++ Γ1, [] ++ Δ2 ++ B :: Δ3)). reflexivity.
        pose (@SIH (mhd (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)) l (Box A0) (A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)
        (A :: Γ0) Γ1 [] (Δ2 ++ B :: Δ3) J5 J6 J7). simpl in d0.
        assert (J8 : list_exch_R (Γ0 ++ Γ1, Δ0 ++ Box A0 :: Δ1) (Γ0 ++ Γ1, Box A0 :: Δ2 ++ A → B :: Δ3)).
        assert (Δ0 ++ Box A0 :: Δ1 = [] ++ [] ++ Δ0 ++ [Box A0] ++ Δ1). reflexivity. rewrite H2. clear H2.
        assert (Box A0 :: Δ2 ++ A → B :: Δ3 = [] ++ [Box A0] ++ Δ0 ++ [] ++ Δ1). rewrite H6.
        reflexivity. rewrite H2. clear H2. apply list_exch_RI. pose (GLS_adm_list_exch_R D0 J8).
        assert (ImpRRule [([] ++ A ::Γ0 ++ Γ1, (Box A0 :: Δ2) ++ B :: Δ3)] ([] ++ Γ0 ++ Γ1, (Box A0 :: Δ2) ++ A → B :: Δ3)).
        apply ImpRRule_I. simpl in H2. pose (ImpR_inv d1 H2). pose (d0 d2 d). pose (dlCons d3 DersNilF).
        apply ImpR in H0 ; try intro ; try apply f ; try rewrite <- H7 ; try auto ; try assumption.
        pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
        (ps:=[(A :: Γ0 ++ Γ1, Δ2 ++ B :: Δ3)]) (Γ0 ++ Γ1, Δ2 ++ A → B :: Δ3) H0 d4). assumption. }
      (* Right rule is ImpL *)
      { inversion H. subst. apply list_split_form in H5. destruct H5.
        - destruct s.
          + repeat destruct p. inversion e0.
          + repeat destruct s. repeat destruct p. subst. repeat rewrite <- app_assoc in H. repeat rewrite <- app_assoc in X2.
            assert (J2: list_exch_R (Γ0 ++ x0 ++ A → B :: Γ3, Δ0 ++ Box A0 :: Δ1) (Γ0 ++ x0 ++ A → B :: Γ3, Box A0 :: Δ2 ++ Δ3)).
            assert (Δ0 ++ Box A0 :: Δ1 = [] ++ [] ++ Δ0 ++ [Box A0] ++ Δ1). reflexivity. rewrite H0. clear H0.
            assert (Box A0 :: Δ2 ++ Δ3 = [] ++ [Box A0] ++ Δ0 ++ [] ++ Δ1). rewrite H6. reflexivity. rewrite H0. clear H0.
            apply list_exch_RI. pose (GLS_adm_list_exch_R D0 J2).
            assert (ImpLRule [((Γ0 ++ x0) ++ Γ3, (Box A0 :: Δ2) ++ A :: Δ3); ((Γ0 ++ x0) ++ B :: Γ3, (Box A0 :: Δ2) ++ Δ3)]
            ((Γ0 ++ x0) ++ A → B :: Γ3, (Box A0 :: Δ2) ++ Δ3)). apply ImpLRule_I. simpl in H.
            repeat rewrite <- app_assoc in H0. pose (ImpL_inv d H0). destruct p.
            assert (ImpLRule [((Γ0 ++ x0) ++ Γ3, Δ2 ++ A :: Δ3); ((Γ0 ++ x0) ++ B :: Γ3, Δ2 ++ Δ3)]
            ((Γ0 ++ x0) ++ A → B :: Γ3, Δ2 ++ Δ3)). apply ImpLRule_I. repeat rewrite <- app_assoc in H0.
            repeat rewrite <- app_assoc in H2.
            assert (J3: PSGLS_rules [(Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3)]
            (Γ0 ++ x0 ++ A → B :: Γ3, Δ2 ++ Δ3)).
            apply PSImpL ; try intro ; try apply f ; try rewrite <- app_assoc ;
            try rewrite <- H6 ; try auto ; try assumption.
            assert (J30: GLS_rules [(Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3)]
            (Γ0 ++ x0 ++ A → B :: Γ3, Δ2 ++ Δ3)). apply ImpL ; try assumption.
            assert (J5: In (Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3) [(Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3)]).
            apply in_eq.
            assert (J9: In (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3) [(Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3)]).
            apply in_cons. apply in_eq.
            pose (RA_mhd_decreases J3 _ J5). pose (RA_mhd_decreases J3 _ J9). repeat rewrite <- app_assoc in SIH. rewrite <- H6 in SIH.
            assert (J6: size_form (Box A0) = size_form (Box A0)). reflexivity.
            assert (J7: mhd (Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3) = mhd (Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3)). reflexivity.
            assert (J8: (Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3) = (Γ0 ++ x0 ++ Γ3, [] ++ Δ2 ++ A :: Δ3)). reflexivity.
            pose (@SIH (mhd (Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3)) l (Box A0) (Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3)
            Γ0 (x0 ++ Γ3) [] (Δ2 ++ A :: Δ3) J6 J7 J8). simpl in d2. inversion X2. subst. inversion X6. clear X6.
            clear X8. subst. pose (d2 d0 X5).
            assert (J10: mhd (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3) = mhd (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3)). reflexivity.
            assert (J11: (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3) = (Γ0 ++ x0 ++ B :: Γ3, [] ++ Δ2 ++ Δ3)). reflexivity.
            pose (@SIH (mhd (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3)) l0 (Box A0) (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3)
            Γ0 (x0 ++ B :: Γ3) [] (Δ2 ++ Δ3) J6 J10 J11). simpl in d4. pose (d4 d1 X7).
            pose (dlCons d5 DersNilF). pose (dlCons d3 d6).
            pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
            (ps:=[(Γ0 ++ x0 ++ Γ3, Δ2 ++ A :: Δ3); (Γ0 ++ x0 ++ B :: Γ3, Δ2 ++ Δ3)]) (Γ0 ++ x0 ++ A → B :: Γ3, Δ2 ++ Δ3) J30 d7).
            assumption.
        - repeat destruct s. repeat destruct p. subst. rewrite <- app_assoc in D0.
          assert (J2: list_exch_R (Γ2 ++ (A → B :: x) ++ Γ1, Δ0 ++ Box A0 :: Δ1) (Γ2 ++ (A → B :: x) ++ Γ1, Box A0 :: Δ2 ++ Δ3)).
          assert (Δ0 ++ Box A0 :: Δ1 = [] ++ [] ++ Δ0 ++ [Box A0] ++ Δ1). reflexivity. rewrite H0. clear H0.
          assert (Box A0 :: Δ2 ++ Δ3 = [] ++ [Box A0] ++ Δ0 ++ [] ++ Δ1). rewrite H6. reflexivity. rewrite H0. clear H0.
          apply list_exch_RI. pose (GLS_adm_list_exch_R D0 J2).
          assert (ImpLRule [(Γ2 ++ x ++ Γ1, (Box A0 :: Δ2) ++ A :: Δ3); (Γ2 ++ B :: x ++ Γ1, (Box A0 :: Δ2) ++ Δ3)]
          (Γ2 ++ (A → B :: x) ++ Γ1, (Box A0 :: Δ2) ++ Δ3)). apply ImpLRule_I. repeat rewrite <- app_assoc in H0.
          pose (ImpL_inv d H0). destruct p. rewrite <- app_assoc.
          assert (ImpLRule [(Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)]
          (Γ2 ++ (A → B :: x) ++ Γ1, Δ2 ++ Δ3)). apply ImpLRule_I.
          assert (J3: PSGLS_rules [(Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)]
          (Γ2 ++ (A → B :: x) ++ Γ1, Δ2 ++ Δ3)).
          apply PSImpL ; try intro ; try apply f ; try rewrite <- app_assoc ;
          try rewrite <- H6 ; try auto ; try assumption.
          assert (J30: GLS_rules [(Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)]
          (Γ2 ++ (A → B :: x) ++ Γ1, Δ2 ++ Δ3)). apply ImpL ; try assumption.
          assert (J5: In (Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3) [(Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)]).
          apply in_eq.
          assert (J9: In (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3) [(Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)]).
          apply in_cons. apply in_eq.
          pose (RA_mhd_decreases J3 _ J5). pose (RA_mhd_decreases J3 _ J9). repeat rewrite <- app_assoc in SIH. rewrite <- H6 in SIH.
          assert (J6: size_form (Box A0) = size_form (Box A0)). reflexivity.
          assert (J7: mhd (Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3) = mhd (Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3)). reflexivity.
          assert (J8: (Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3) = ((Γ2 ++ x) ++ Γ1, [] ++ Δ2 ++ A :: Δ3)). rewrite <- app_assoc. reflexivity.
          pose (@SIH (mhd (Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3)) l (Box A0) (Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3)
          (Γ2 ++ x) Γ1 [] (Δ2 ++ A :: Δ3) J6 J7 J8). simpl in d2. inversion X2. subst. inversion X6. clear X6.
          clear X8. subst. repeat rewrite <- app_assoc in d2. pose (d2 d0 X5).
          assert (J10: mhd (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3) = mhd (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)). reflexivity.
          assert (J11: (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3) = ((Γ2 ++ B :: x) ++ Γ1, [] ++ Δ2 ++ Δ3)). rewrite <- app_assoc. reflexivity.
          pose (@SIH (mhd (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)) l0 (Box A0) (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)
          (Γ2 ++ B :: x) Γ1 [] (Δ2 ++ Δ3) J6 J10 J11). simpl in d4. repeat rewrite <- app_assoc in d4. pose (d4 d1 X7).
          pose (dlCons d5 DersNilF). pose (dlCons d3 d6).
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[(Γ2 ++ x ++ Γ1, Δ2 ++ A :: Δ3); (Γ2 ++ B :: x ++ Γ1, Δ2 ++ Δ3)]) (Γ2 ++ (A → B :: x) ++ Γ1, Δ2 ++ Δ3) J30 d7).
          assumption. }
      (* Right rule is GLR *)
      { inversion X5. subst. inversion X0. subst. clear X8. inversion X2. subst. clear X9.
        pose (univ_gen_ext_splitR _ _ X4). repeat destruct s. repeat destruct p.
        pose (univ_gen_ext_splitR _ _ X6). repeat destruct s. repeat destruct p. subst. inversion u2.
        - subst.
          assert ((XBoxed_list (x ++ x0) ++ [Box A0], [A0]) = ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ [], [] ++ [A0])).
          repeat rewrite <- app_assoc. reflexivity.
          assert (X7': derrec GLS_rules (fun _ : rel (list (MPropF V)) => False) ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ [], [] ++ [A0])).
          rewrite <- H. assumption.
          assert (J1: wkn_L (Box A) ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ [], [] ++ [A0]) ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ (Box A) :: [], [] ++ [A0])).
          apply wkn_LI. assert (J2: derrec_height X7' = derrec_height X7'). reflexivity.
          pose (GLS_wkn_L _ J2 J1). destruct s. clear l0. clear J2. clear X7'. clear J1.
          assert (J3: wkn_R A ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ [Box A], [] ++ [A0]) ((XBoxed_list (x ++ x0) ++ [Box A0]) ++ [Box A], [] ++ A :: [A0])).
          apply wkn_RI. assert (J4: derrec_height x2 = derrec_height x2). reflexivity.
          pose (GLS_wkn_R _ J4 J3). destruct s. clear l0. clear J4. clear J3. clear x2. clear H. simpl in x3.
          rewrite XBox_app_distrib in x3. repeat rewrite <- app_assoc in x3.
          rewrite XBox_app_distrib in X8. repeat rewrite <- app_assoc in X8. simpl in X8.
          assert ((XBoxed_list x1 ++ A0 :: Box A0 :: XBoxed_list l ++ [Box A], [A]) =
          (XBoxed_list x1 ++ (A0 :: [Box A0]) ++ [] ++ XBoxed_list l ++ [Box A], [A])).
          reflexivity. rewrite H in X8. clear H.
          assert (J5: list_exch_L (XBoxed_list x1 ++ [A0; Box A0] ++ [] ++ XBoxed_list l ++ [Box A], [A])
          (XBoxed_list x1 ++ XBoxed_list l ++ [] ++ [A0; Box A0] ++ [Box A], [A])).
          apply list_exch_LI.
          pose (GLS_adm_list_exch_L X8 J5). simpl in d. rewrite app_assoc in d.
          rewrite <- XBox_app_distrib in d. assert (x1 ++ l = x ++ x0).
          apply nobox_gen_ext_injective with (l:=(Γ0 ++ Γ1)) ; try assumption.
          intro. intros. apply H4. apply in_or_app. apply in_app_or in H. destruct H.
          auto. right. apply in_cons. assumption. apply univ_gen_ext_combine ; assumption.
          rewrite H in d. clear J5. clear X8. simpl in x3. rewrite app_assoc in x3.
          rewrite <- XBox_app_distrib in x3.
          assert (J6: size_form A0 < size_form (Box A0)). simpl. lia.
          assert (J7: size_form A0 = size_form A0). reflexivity.
          assert (J8: mhd (XBoxed_list (x ++ x0) ++ [Box A0; Box A], [A]) =
          mhd (XBoxed_list (x ++ x0) ++ [Box A0; Box A], [A])). reflexivity.
          assert (J9: (XBoxed_list (x ++ x0) ++ [Box A0; Box A], [A]) =
          (XBoxed_list (x ++ x0) ++ [Box A0; Box A], [A] ++ [])). rewrite app_nil_r. reflexivity.
          pose (@PIH (size_form A0) J6 (mhd (XBoxed_list (x ++ x0) ++ [Box A0; Box A], [A]))
          A0 (XBoxed_list (x ++ x0) ++ [Box A0; Box A], [A]) (XBoxed_list (x ++ x0)) (Box A0 :: [Box A])
          [A] [] J7 J8 J9). rewrite app_nil_r in d0. pose (d0 x3 d).
          assert (GLRRule [(XBoxed_list (x ++ x0) ++ [Box A0], [A0])] (x ++ x0, [Box A0])).
          assert ((x ++ x0, [Box A0]) = (x ++ x0, [] ++ Box A0 :: [])). reflexivity. rewrite H0. clear H0.
          apply GLRRule_I.
          assumption. apply univ_gen_ext_refl.
          assert (GLS_rules [(XBoxed_list (x ++ x0) ++ [Box A0], [A0])] (x ++ x0, [Box A0])).
          apply GLR. assumption.
          pose (dlCons X7 DersNilF).
          pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
          (ps:=[(XBoxed_list (x ++ x0) ++ [Box A0], [A0])]) (x ++ x0, [Box A0]) X10 d2).
          assert ([Box A0] = [Box A0] ++ []). reflexivity. rewrite H0 in d3.
          assert (wkn_R A (x ++ x0, [Box A0] ++ []) (x ++ x0, [Box A0] ++ A :: [])). apply wkn_RI.
          assert (J10: derrec_height d3 = derrec_height d3). reflexivity.
          pose (GLS_wkn_R _ J10 H2). destruct s. clear l0. clear J10. clear H0. clear d3.
          clear d2. clear X10. clear X8. clear J6. clear J8. clear J9.
          assert (J20: derrec_height x2 = derrec_height x2). reflexivity.
          pose (@GLS_XBoxed_list_wkn_L (derrec_height x2) (x ++ x0) [] [] ([Box A0] ++ [A])).
          repeat rewrite app_nil_r in s. repeat rewrite app_nil_l in s. pose (s x2 J20).
          destruct s0. clear l0. clear J20. clear s. clear x2.
          assert (XBoxed_list (x ++ x0) = XBoxed_list (x ++ x0) ++ []). rewrite app_nil_r. reflexivity.
          rewrite H0 in x4. clear H0.
          assert (wkn_L (Box A) (XBoxed_list (x ++ x0) ++ [], [Box A0] ++ [A]) (XBoxed_list (x ++ x0) ++ (Box A) :: [], [Box A0] ++ [A])).
          apply wkn_LI.
          assert (J10: derrec_height x4 = derrec_height x4). reflexivity.
          pose (GLS_wkn_L _ J10 H0). destruct s. clear l0. clear J10. clear x4. clear H0.
          assert (GLRRule [(XBoxed_list (x ++ x0) ++ [Box A], [A])] (Γ0 ++ Γ1, Δ0 ++ Δ1)).
          rewrite <- H5. apply GLRRule_I ; try assumption.
          destruct (dec_init_rules (Γ0 ++ Γ1, Δ2 ++ Box A :: Δ3)).
          + repeat destruct s.
            * apply IdP in i. pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
              (ps:=[]) (Γ0 ++ Γ1, Δ2 ++ Box A :: Δ3) i DersNilF). assumption.
            * inversion i. apply Id_all_form.
            * apply BotL in b. pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
              (ps:=[]) (Γ0 ++ Γ1, Δ2 ++ Box A :: Δ3) b DersNilF). assumption.
          + assert (PSGLS_rules [(XBoxed_list (x ++ x0) ++ [Box A], [A])] (Γ0 ++ Γ1, Δ0 ++ Δ1)).
            apply PSGLR ; try intro ; try apply f ; try rewrite H5 ; try auto ; try assumption.
            assert (J40: GLS_rules [(XBoxed_list (x ++ x0) ++ [Box A], [A])] (Γ0 ++ Γ1, Δ0 ++ Δ1)).
            apply GLR ; try assumption.
            assert (l0: mhd (XBoxed_list (x ++ x0) ++ [Box A], [A]) < mhd (Γ0 ++ Γ1, Δ0 ++ Δ1)).
            assert (J30 : In (XBoxed_list (x ++ x0) ++ [Box A], [A]) [(XBoxed_list (x ++ x0) ++ [Box A], [A])]).
            apply in_eq. pose (RA_mhd_decreases X10 _ J30). assumption.
            assert (J10: size_form (Box A0) = size_form (Box A0)). reflexivity.
            assert (J11: mhd (XBoxed_list (x ++ x0) ++ [Box A], [A]) = mhd (XBoxed_list (x ++ x0) ++ [Box A], [A])). reflexivity.
            assert (J12: (XBoxed_list (x ++ x0) ++ [Box A], [A]) = (XBoxed_list (x ++ x0) ++ [Box A], [] ++ [A]) ). reflexivity.
            pose (@SIH (mhd (XBoxed_list (x ++ x0) ++ [Box A], [A])) l0 (Box A0) (XBoxed_list (x ++ x0) ++ [Box A], [A])
            (XBoxed_list (x ++ x0)) [Box A] [] [A] J10 J11 J12). simpl in d2. pose (d2 x2 d1). pose (dlCons d3 DersNilF).
            pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
            (ps:=[(XBoxed_list (x ++ x0) ++ [Box A], [A])]) (Γ0 ++ Γ1, Δ0 ++ Δ1) J40 d4).
            rewrite H5. assumption.
        - exfalso. apply H2. exists A0. reflexivity. }
    + repeat destruct s. repeat destruct p. subst.
      assert (GLRRule [(XBoxed_list BΓ ++ [Box A0], [A0])] (Γ0 ++ Γ1, (Δ0 ++ x0) ++ Box A0 :: Δ3)).
      apply GLRRule_I ; try assumption. repeat rewrite <- app_assoc in X5.
      assert (GLS_rules [(XBoxed_list BΓ ++ [Box A0], [A0])] (Γ0 ++ Γ1, Δ0 ++ x0 ++ Box A0 :: Δ3)).
      apply GLR. assumption.
      pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
      (ps:=[(XBoxed_list BΓ ++ [Box A0], [A0])]) (Γ0 ++ Γ1, Δ0 ++ x0 ++ Box A0 :: Δ3) X6 X0). assumption.
  * repeat destruct s. repeat destruct p. subst. rewrite <- app_assoc.
    assert (GLRRule [(XBoxed_list BΓ ++ [Box A0], [A0])] (Γ0 ++ Γ1, Δ2 ++ (Box A0 :: x) ++ Δ1)).
    apply GLRRule_I ; try assumption.
    assert (GLS_rules [(XBoxed_list BΓ ++ [Box A0], [A0])] (Γ0 ++ Γ1, Δ2 ++ (Box A0 :: x) ++ Δ1)).
    apply GLR. assumption.
    pose (derI (rules:=GLS_rules (V:=V)) (prems:=fun _ : rel (list (MPropF V)) => False)
    (ps:=[(XBoxed_list BΓ ++ [Box A0], [A0])]) (Γ0 ++ Γ1, Δ2 ++ (Box A0 :: x) ++ Δ1) X6 X0). assumption.
Qed.

Theorem GLS_cut_adm : forall A Γ0 Γ1 Δ0 Δ1,
                      (derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ Γ1, Δ0 ++ A :: Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ A :: Γ1, Δ0 ++ Δ1)) ->
                      (derrec (@GLS_rules V) (fun _ => False) (Γ0 ++ Γ1, Δ0 ++ Δ1)).
Proof.
intros.
assert (J1: size_form A = size_form A). reflexivity.
assert (J2: mhd (Γ0 ++ Γ1, Δ0 ++ Δ1) = mhd (Γ0 ++ Γ1, Δ0 ++ Δ1)). reflexivity.
assert (J3: (Γ0 ++ Γ1, Δ0 ++ Δ1) = (Γ0 ++ Γ1, Δ0 ++ Δ1)). reflexivity.
pose (@GLS_cut_adm_main (size_form A) (mhd (Γ0 ++ Γ1, Δ0 ++ Δ1)) A
(Γ0 ++ Γ1, Δ0 ++ Δ1) Γ0 Γ1 Δ0 Δ1 J1 J2 J3). auto.
Qed.


