Require Import Program.Equality.
Require Import LibTactics.
Require Import Metalib.Metatheory. 
Require Import Lia.
Require Import Language.

(* ---------------------------------------------------------------------- *)
(* Definitions of size for types and terms. Use them when we want to do induction by size. *)
Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | int => 1
    | top => 1
    | arr A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | rcd l1 A2 => 1 + (size_typ A2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | unit => 1
    | lit i1 => 1
    | ctx => 1
    | merge e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | ann e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | rec l1 e2 => 1 + (size_exp e2)
    | proj e2 l1 => 1 + (size_exp e2)
    | lam fm e2 => 1 + (size_exp e2)
    | app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | box e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | fixp A e2 => 1 + (size_typ A) + (size_exp e2)
  end.

Ltac indTypSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : typ |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

Ltac indExpSize s :=
  assert (SizeInd: exists i, s < i) by eauto;
  destruct SizeInd as [i SizeInd];
  repeat match goal with | [ h : exp |- _ ] => (gen h) end;
  induction i as [|i IH]; [
      intros; match goal with | [ H : _ < 0 |- _ ] => inverts H end
    | intros ].

(* Some simple lemmas for size *)
Lemma size_typ_min_me: forall A, 
  1 <= size_typ A.
Proof.
  intros. inductions A; eauto.
  - simpl. lia.
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma and_decrease_left: forall B C,
  size_typ B < size_typ (and B C).
Proof with (pose proof (size_typ_min_me); simpl in *; try lia).
  intros. simpl. lia.
Qed.

Lemma and_decrease_right: forall B C,
  size_typ C < size_typ (and B C).
Proof with (pose proof (size_typ_min_me); simpl in *; try lia).
  intros. simpl. lia.
Qed.

Lemma arrow_decrease_left: forall B C,
  size_typ B < size_typ (arr B C).
Proof with (pose proof (size_typ_min_me); simpl in *; try lia).
  intros. simpl. lia.
Qed.

Lemma arrow_decrease_right: forall B C,
  size_typ C < size_typ (arr B C).
Proof with (pose proof (size_typ_min_me); simpl in *; try lia).
  intros. simpl. lia.
Qed.

(* a simple tactic for reasoning about sizes *)
Ltac elia :=
  try solve [pose proof (size_typ_min_me);
             simpl in *;
             try lia].

(* multi-step *)
Definition relation (X:Type) := X -> X -> Prop.

Section Star.

Variable A : Type.
Variable R : relation A.

Inductive star: relation A:=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall a b, R a b -> star a b.
Proof.
  eauto using star.
Qed.

Lemma star_trans:
  forall a b, star a b -> forall c, star b c -> star a c.
Proof.
  induction 1; eauto using star.
Qed.

Hypothesis R_functional:
  forall a b c, R a b -> R a c -> b = c.

Lemma star_star_inv:
  forall a b, star a b -> forall c, star a c -> star b c \/ star c b.
Proof.
  induction 1; intros.
  - auto.
  - inversion H1; subst.
    + right. eauto using star.
    + assert (b = b0) by (eapply R_functional; eauto). subst b0.
      apply IHstar; auto.
Qed.

Definition irred a : Prop := forall b, ~(R a b).

Lemma finseq_unique:
  forall a b b',
    star a b -> irred b ->
    star a b' -> irred b' ->
    b = b'.
Proof.
  intros. destruct (star_star_inv _ _ H _ H1).
  - inversion H3; subst. auto. elim (H0 _ H4).
  - inversion H3; subst. auto. elim (H2 _ H4).
Qed.

End Star.

#[export]
Hint Constructors star : core.

#[export]
Hint Resolve star_trans star_one : core.

(* Regularity of relations *)
Lemma step_not_value: forall v,
  value v -> forall v',
  irred exp (step v') v.
Proof.
  introv.
  unfold irred.
  induction v; introv H; inverts* H; unfold not; intros; try inverts* H.
Qed.

Lemma step_env : forall v e e', step v e e' -> value v.
  induction 1; eauto.
  - dependent destruction IHstep; eauto.
Defined.
             