Require Import Program.Equality.
Require Import LibTactics.
Require Import Metalib.Metatheory. 

Require Import Language 
               Infra
               SubDis
               Determinism.


Lemma toplike_sub: forall A B,
  toplike A -> sub A B -> toplike B.
Proof.
  introv TL S.
  induction S; inverts* TL.
Qed.

Lemma genv_tl_tl: forall A v,
  toplike A ->
  genv A v ->
  toplike (principal_type v).
Proof.
  introv Ht Hg. inductions Hg; simpl; eauto.
  - inverts* Ht.
  - inverts* Ht.
Qed.

Lemma genv_cast_toplike: forall A,
  toplike A -> forall v,
  genv A v -> forall B v',
  casting v B v' ->
  toplike B.
Proof.
  introv TL. inductions TL; introv Hg R.
  - inverts* Hg. inductions R; try solve [eauto].
  - inverts* Hg. inductions R; try solve [eauto].
  - inverts* Hg. inductions R; try solve [eauto].
    exfalso. eapply H0. eapply toplike_sub; eauto.
  - inverts* Hg. inductions R; try solve [eauto].
Qed.

Lemma genv_ptype_sub: forall A,
  toplike A -> forall v,
  value v ->
  genv A v ->
  sub A (principal_type v).
Proof.
  introv Ht. inductions Ht; introv Val Hg.
  - inverts* Hg.
  - inverts Hg. inverts Val. simpl. 
    forwards* : IHHt1 H2 H1.
  - inverts* Hg. 
  - inverts Hg. inverts* Val. 
Qed.

Lemma genv_value: forall A v,
  genv A v ->
  value v.
Proof.
  introv H. inductions H; eauto.
Qed.

Lemma casting_value : forall v A v', casting v A v' -> value v -> value v'.
Proof.
  induction 1; intros; eauto; try solve [inverts* H1].
  - inverts* H0.
  - eapply genv_value. eauto.
Qed.

Lemma casting_trans : forall v v1 v2 A B,
  value v -> 
  casting v A v1 -> 
  casting v1 B v2 -> 
  casting v B v2.
Proof.
  introv Val Red1 Red2.
  gen B v2.
  inductions Red1;
    introv Red2.
  - (* top *)
    inductions Red2; try solve [eauto].
  - inductions Red2; try solve [eauto].
  - (* mergel *)
    inverts* Val.
    inductions Red2; try solve [eauto].
  - (* merger *)
    inverts* Val.
    inductions Red2; try solve [eauto].
  - (* and *)
    gen v0.
    inductions B0; introv Red2; try solve [inverts* Red2].
  - (* rcd *)
    inverts* Val.
    inductions Red2; try solve [eauto].
  - (* lam *) 
    inductions Red2; try solve [constructor*].
    + eauto.
    + eauto.
  - inverts H1. 
    + inductions Red2; try solve [inverts* H4]. 
      * inverts H4. inverts H6.
        forwards~: toplike_sub H0 H8. contradiction.
      * inverts H4. inverts H6. eauto. 
    + inductions Red2; try solve [inverts* H4]. 
      * inverts H4. inverts H6.
        forwards~: toplike_sub H0 H8. contradiction.
      * inverts H4. inverts H6. eauto.
Qed.

Lemma consistent_after_casting: forall v G A B C v1 v2, 
  value v -> 
  has_type G v inf C -> 
  casting v A v1 -> 
  casting v B v2 -> 
  consistencySpec v1 v2.
Proof.
  intros v G A B C v1 v2 Val Typ Red1 Red2.
  unfold consistencySpec.
  intros D v1' v2' Red1' Red2'.
  forwards*: casting_trans Red1 Red1'.
  forwards*: casting_trans Red2 Red2'.
  forwards*: casting_unique H H0.
Qed.

Lemma casting_weakenr : forall v A v', casting v A v' -> forall v1, exists v'', casting (merge v1 v) A v''.
  induction 1; eauto; intros.
Proof.
  - destruct (IHcasting1 v0).
    destruct (IHcasting2 v0).
    exists (merge x x0).
    apply cast_and; eauto.
Qed.

Lemma casting_weakenl : forall v A v', casting v A v' -> forall v1, exists v'', casting (merge v v1) A v''.
Proof.
  induction 1; eauto; intros.
  - destruct (IHcasting1 v0).
    destruct (IHcasting2 v0).
    exists (merge x x0).
    apply cast_and; eauto.
Qed.

Lemma toplike_decidable : forall A,
  toplike A \/ ~toplike A.
Proof.
  intros.
  induction~ A;
    try solve [ right; intros HF; inverts~ HF ].
  - destruct IHA1; destruct IHA2; eauto;
      try solve [ right; intros HF; inverts~ HF ].
  - destruct IHA; eauto;
      try solve [ right; intros HF; inverts~ HF ].
  - destruct IHA1; destruct IHA2; eauto;
      try solve [ right; intros HF; inverts~ HF ].
Qed.

Lemma casting_sub : forall A B, 
  sub A B -> forall v v', 
  casting v A v' -> exists v'', 
  casting v B v''.
Proof.
  induction 1; intros; eauto.
  - destruct (IHsub1 _ _ H1).
    destruct (IHsub2 _ _ H1).
    exists (merge x x0); eauto.
  - dependent destruction H0; try solve [inverts H0].
    + inverts* H1.
    + inverts* H1.
    + eauto.
  - dependent destruction H0; try solve [inverts H0].
    + inverts* H1.
    + inverts* H1.
    + eauto.
  - dependent induction H0; eauto.
    + eapply IHcasting in H; eauto.
      destruct H.
      exists x0.
      apply cast_mrgl; eauto.
    + eapply IHcasting in H; eauto.
      destruct H.
      exists x0.
      apply cast_mrgr; eauto.
    + destruct (IHsub _ _ H0).
      destruct* (toplike_decidable B).
  - dependent induction H1; eauto.
    + destruct (IHcasting _ _ H H0 IHsub1 IHsub2 eq_refl).
      apply casting_weakenl with (v1 := v2) in H3.
      destruct H3; eauto.
    + destruct (IHcasting _ _ H H0 IHsub1 IHsub2 eq_refl).
      apply casting_weakenr with (v1 := v1) in H3.
      destruct H3; eauto.
    + destruct* (toplike_decidable D). 
      assert (toplike (arr C D)) by eauto.
      forwards~ (?&?): genv_progress H6. exists*.
    + destruct* (toplike_decidable D). 

      assert (toplike (arr C D)) by eauto.
      forwards~ (?&?): genv_progress H7. exists*.
Qed.

  
Lemma casting_progress : forall G A v m, 
  has_type G v m A -> 
  value v -> exists v', 
  casting v A v'.
Proof.  
  induction 1; intros.
  - exists (lit i); eauto.
  - exists unit; eauto.
  - inverts* H.
  - inverts* H3.
    forwards~ (v1&Red1): IHhas_type1 H6.
    forwards~ (v2&Red2): IHhas_type2 H7.
    apply casting_weakenl with (v1 := e2) in Red1; eauto.
    apply casting_weakenr with (v1 := e1) in Red2; eauto.
    destruct Red1. destruct Red2.
    exists* (merge x x0).
  - inverts* H4.
    forwards~ (v3&Red1): IHhas_type1 H7.
    forwards~ (v4&Red2): IHhas_type2 H8.
    apply casting_weakenl with (v1 := v2) in Red1; eauto.
    apply casting_weakenr with (v1 := v1) in Red2; eauto.
    destruct Red1. destruct Red2.
    exists* (merge x x0).
  - dependent destruction H0.
  - inverts* H3.
  - inverts* H1.
  - inverts* H1.
    + inverts* H0. inverts H4. inverts H0.
      destruct* (toplike_decidable B0).
      assert (toplike (arr C B0)) by eauto.
      forwards~ (?&?): genv_progress H1. exists*.
    + inverts* H0. inverts H4. inverts H0.
      destruct* (toplike_decidable B0).
      assert (toplike (arr C B0)) by eauto.
      forwards~ (?&?): genv_progress H1. exists*.
  - destruct (IHhas_type H1).
    eapply casting_sub; eauto.
  - (* rec *)
    dependent destruction H0.
    destruct* (IHhas_type H0).
  - (* proj *)
    inverts* H0.
Qed.

Lemma arr_decidalbe: forall A,
  (exists B C, A = arr B C) \/ 
  ~ (exists B C, A = arr B C).
Proof.
  intros A. destruct* A.
  - right. introv Bot. inverts* Bot. inverts* H. inverts* H0.
  - right. introv Bot. inverts* Bot. inverts* H. inverts* H0.
  - right. introv Bot. inverts* Bot. inverts* H. inverts* H0.
  - right. introv Bot. inverts* Bot. inverts* H. inverts* H0.
Qed.

Lemma rcd_decidalbe: forall A,
  (exists B l, A = rcd l B) \/ 
  ~ (exists B l, A = rcd l B).
Proof.
  intros A. destruct* A.
  - right. introv Bot. inverts* Bot. inverts* H. inverts* H0.
  - right. introv Bot. inverts* Bot. inverts* H. inverts* H0.
  - right. introv Bot. inverts* Bot. inverts* H. inverts* H0.
  - right. introv Bot. inverts* Bot. inverts* H. inverts* H0.
Qed.

Lemma value_decidable: forall e,
  value e \/ ~ value e.
Proof.
  intros e. inductions e; try solve [left; eauto].
  - right. introv Bot. inverts* Bot.
  - inverts* IHe1; inverts* IHe2.
    + right. introv Bot. inverts* Bot.
    + right. introv Bot. inverts* Bot.
    + right. introv Bot. inverts* Bot.
  - right. introv Bot. inverts* Bot.
  - inverts* IHe. right. introv Bot. inverts* Bot.
  - right. introv Bot. inverts* Bot.
  - right. introv Bot. inverts* Bot.
  - right. introv Bot. inverts* Bot.
  - destruct* IHe1; try solve [right; introv Bot; inverts* Bot].
    destruct* e2; try solve [right; introv Bot; inverts* Bot].
    destruct* e2; try solve [right; introv Bot; inverts* Bot].
    destruct* f.
    + destruct* (arr_decidalbe t). 
      * left. destruct H0. destruct H0. subst*. 
      * right; introv Bot; inverts* Bot.
    + destruct* (arr_decidalbe t). 
      * destruct H0. destruct H0. subst*.
        destruct* (rcd_decidalbe x).
        left. destruct H0. destruct H0. subst*.
        right; introv Bot; inverts* Bot.
      * right; introv Bot; inverts* Bot.
Qed.

Lemma toplike_dis: forall A,
  toplike A -> forall B,
  disjoint A B.
Proof.
  introv TL. intros B. 
  lets TL': TL.
  inductions TL; eauto.
  - unfold disjoint. eapply costs_top_any.
  - forwards~: IHTL1 B0 TL1.
    forwards~: IHTL2 B0 TL2.
    forwards~: dis_to_inter H H0.
  - inductions B0.
    + unfold disjoint. intros Hc. 
      eapply costs_sym in Hc. eapply costs_int_arr. eauto.
    + eapply dis_sym. unfold disjoint. eapply costs_top_any.
    + forwards~: IHB0_1 TL'.
      forwards~: IHB0_2 TL'.
      eapply dis_sym in H.
      eapply dis_sym in H0.
      forwards~: dis_to_inter H H0.
      eapply dis_sym. eauto. 
    + unfold disjoint. intros Hc.
      eapply costs_sym in Hc. eapply costs_arr_rcd. eauto. 
    + forwards~: IHTL B0_2 TL.
      eapply disjoint_arr_build. eauto.
  - inductions B0.
    + unfold disjoint. intros Hc. 
      eapply costs_sym in Hc. eapply costs_int_rcd. eauto.
    + eapply dis_sym. unfold disjoint. eapply costs_top_any.
    + forwards~: IHB0_1 TL'.
      forwards~: IHB0_2 TL'.
      eapply dis_sym in H.
      eapply dis_sym in H0.
      forwards~: dis_to_inter H H0.
      eapply dis_sym. eauto.
    + destruct* (x == n).
      
      subst*.
      forwards~: IHTL B0 TL.
      eapply disjoint_rcd_build; eauto.

      unfold disjoint. intros Hc. 
      eapply costs_rcd_rcd_neq; eauto.
    + unfold disjoint. intros Hc.
      eapply costs_arr_rcd. eauto. 
Qed.

Lemma genv_infer: forall A v G,
  genv A v ->
  toplike A -> 
  has_type G v inf A.
Proof.
  introv Hg. inductions Hg; intros TL; try solve [simpl; eauto].
  - inverts* TL.
    forwards~: IHHg H0.
    econstructor; eauto. eapply tlam; eauto.
    unfold disjoint. eapply costs_top_any. 
    forwards~: genv_value Hg.
    eapply value_closed; eauto.
  - inverts* TL.
    forwards~: genv_value Hg1.
    forwards~: genv_value Hg2.
    forwards~: IHHg1 H1. forwards~: IHHg2 H2.
    econstructor; eauto.

    eapply value_closed; eauto.

    eapply dis_sym.
    eapply toplike_dis. eauto.

    eapply dis_sym.
    eapply toplike_dis. eauto.
  - inverts* TL.
Qed.

Lemma casting_preservation: forall v v' A,
  value v -> 
  casting v A v'-> forall G B,
  has_type G v inf B -> 
  has_type G v' inf A.
Proof with auto.
  introv Val Red.
  inductions Red; introv Typ; try solve [inverts* Typ].
  - inverts* Val. inverts* Typ.
  - inverts* Val. inverts* Typ.
    eapply IHRed; eauto.
    eapply value_closed; eauto.
  - forwards~ : IHRed1 Val Typ. 
    forwards~ : IHRed2 Val Typ.
    lets Con: consistent_after_casting Val Typ Red1 Red2.
    applys* tcon; try eapply casting_value; try eassumption. 
  - inverts* Val. inverts* Typ. 
  - inverts H1.
    + inverts* Val. inverts* Typ. inverts H8. 
      * inverts* H6. inverts* H1. 
      * inverts H12. eapply tbox.
        eauto.  
        eapply tlam; eauto. 
        eapply check_sub; eauto.
    + inverts* Val. inverts* Typ. inverts H8. 
      * inverts* H6. inverts* H1. 
      * inverts H12. eapply tbox.
        eauto.  
        eapply tlam; eauto. 
        eapply check_sub; eauto.
  - eapply genv_infer; eauto.
Qed.

Lemma gen_progress : forall e m A G, 
  has_type G e m A -> 
  (value e) \/ 
  (forall v, has_type top v inf G -> 
  value v -> 
  exists e', step v e e').
Proof.
  intros.
  induction H; eauto.
  - destruct IHhas_type1; destruct IHhas_type2.
    + left; eauto.
    + right; intros.
      assert (has_type top (merge v e1) inf (and G A)) as Typm. {
        constructor; eauto.
        eapply value_closed; eauto.
        unfold disjoint. eapply costs_top_any.
      }
      forwards~ (e'&?): H4 Typm. exists* (merge e1 e').
    + right; intros.
      apply H3 in H5; eauto.
      destruct H5.
      exists (merge x e2).
      apply step_mrgl; eauto.
    + right; intros.
      apply H3 in H5; eauto.
      destruct H5.
      exists (merge x e2).
      apply step_mrgl; eauto.
  - right; intros.      
    destruct* IHhas_type.
    + apply casting_progress in H; eauto.
      destruct* H.
    + forwards~: H2 H0. inverts* H3.
  - right; intros.
    destruct IHhas_type1; destruct IHhas_type2.
    + dependent destruction H; try (inversion H4; fail); try solve [inverts* H0]; try solve [inverts* H3].
      inverts* H3. 
      * inverts H0. inverts H10. inverts H0. inverts H14.
        inverts* H1.
        assert (has_type G e2 chk A'). {
          econstructor; eauto.
        }
        apply casting_progress in H1; eauto.
        destruct H1.
        exists*. 
      * inverts H0. inverts H10. inverts H0. inverts H14.
        inverts* H1.
        assert (has_type G e2 chk A'). {
          econstructor; eauto.
        }
        apply casting_progress in H1; eauto.
        destruct H1.
        exists*. 
    + apply H4 in H2; eauto. destruct H2.
      exists (app e1 x); eauto.
    + apply H3 in H2; eauto.
      destruct H2.
      exists (app x e2); eauto.
    + apply H3 in H2; eauto.
      destruct H2.
      exists (app x e2); eauto.
  - destruct* IHhas_type1.
    + destruct* IHhas_type2.
      destruct* (value_decidable (box e1 e2)).
      right. intros.
      forwards~: value_closed H top.  
      apply H2 in H6; eauto.
      destruct* H6.
    + right. intros. forwards*: H1 H2 H3. destruct* H4.
  - (* record *)
    destruct IHhas_type.
    + left. eauto.
    + right; intros.
      apply H0 in H1; eauto.
      destruct H1.
      exists (rec x x0).
      econstructor; eauto.
  - (* proj *)
    right; intros.
    destruct IHhas_type.
    + dependent destruction H2; try solve [inverts* H; inverts* H0].
      * inverts* H. inverts H7.
      * inverts* H. inverts H7.
    + apply H2 in H1; eauto.
      destruct H1.
      exists (proj x0 x).
      econstructor; eauto.
Qed.


Lemma gen_preservation: forall e m A G,
  has_type G e m A -> forall v e',
  has_type top v inf G ->
  step v e e' ->
  has_type G e' m A.
Proof.
  introv Typ.
  lets Typ' : Typ. 
  inductions Typ; introv Typv Red.
  - inverts* Red.
  - inverts* Red.
  - inverts* Red. 
    eapply value_closed; eauto.
  - (* merge *)
    inverts* Red.
    assert (has_type top (merge v e1) inf (and G A)) as Typm. {
      eapply tmrg; try eassumption; try eauto.
      try eapply value_closed; try eassumption; try eauto. 
      unfold disjoint. eapply costs_top_any.
    }
    forwards~ : IHTyp2 Typm H4.
  - (* mergev *)
    inverts Red.
    + forwards~: step_not_value H5. contradiction.
    + forwards~: step_not_value H6. contradiction.
  - inverts* Red.
    + forwards~: val_chk_inf_sub Typ. destruct* H. destruct* H. 
      forwards*: casting_preservation H3 H.
    + inverts* Typ. inverts* H.
  - (* closure *)
    inverts* Red.
    + inverts* H8.
    + inverts* H6.
    + econstructor; eauto.
      eapply value_closed; eauto.
  - (* typing_app *)
    inverts* Red.
    + inverts H1.
      * forwards~: casting_value H2.
        inverts Typ1. inverts H8.
        inverts H9. inverts H10. inverts H0. inverts H14.
        forwards~: val_chk_inf_sub Typ2. destruct* H0. destruct* H0.
        forwards~: casting_preservation H2 H0.
        econstructor; eauto.
        eapply tcon; eauto.
        eapply disjoint_val_consistent; eauto.
      * forwards~: casting_value H2.
        inverts Typ1. inverts H8.
        inverts H9. inverts H10. inverts H0. inverts H14.
        forwards~: val_chk_inf_sub Typ2. destruct* H0. destruct* H0.
        forwards~: casting_preservation H2 H0.
        econstructor; eauto.
        eapply tcon; eauto.
        eapply disjoint_val_consistent; eauto.
  - (* box *)
    inverts* Red.
    + eapply value_closed; try eassumption.
    + econstructor; try eassumption.
      eapply IHTyp2; try eassumption.
      eapply value_closed; eauto.
      eapply step_env; eauto.
  - forwards*: IHTyp Typ Typv Red.
  - inverts* Red.
  - (* proj *)
    inverts* Red.
    inverts* Typ.
Qed.


Lemma progress : forall e m A, 
  has_type top e m A -> 
  (value e) \/ (exists e', step unit e e').
Proof.
  introv Typ.
  forwards~: gen_progress Typ. inverts* H.
Qed.

Lemma preservation: forall e m A,
  has_type top e m A -> forall e',
  step unit e e' ->
  has_type top e' m A.
Proof.
  introv Typ Red.
  forwards~: gen_preservation Typ Red.
Qed.


Notation "v |- e ->* e'" := ((star exp (step v)) e e') (at level 68).

Theorem gen_type_safety : forall G e m A,
  has_type G e m A -> forall v e',
  value v ->
  has_type top v inf G ->
  v |- e ->* e' ->
  value e' \/ 
  (exists e'', step v e' e'').
Proof.
  introv Typ Val Typv Red. gen A m.
  induction Red; intros.
  - forwards*: gen_progress Typ.
  - lets*: gen_preservation Typ H.
Qed. 

Theorem type_safety: forall e e' m A,
  has_type top e m A -> 
  unit |- e ->* e' ->
  value e' \/ 
  (exists e'', step unit e' e'').
Proof.
  introv Typ Red.
  eapply gen_type_safety; eauto.
Qed. 
