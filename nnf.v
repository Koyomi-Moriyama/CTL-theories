Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import String.
Open Scope string_scope.


Set Implicit Arguments.

Inductive nnf : Type :=
  | var (p : string)
  | neg (p : string)
  | and (phi psi : nnf)
  | or (phi psi : nnf)
  | ebef (phi psi : nnf)
  | eunt (phi psi : nnf)
  | abef (phi psi : nnf)
  | aunt (phi psi : nnf)
  | enext (phi : nnf)
  | anext (phi : nnf).


Definition nnf_true  := or (var "") (neg "").
Definition nnf_false := and (var "") (neg "").

Definition nnf_eqdec (phi psi : nnf) : {phi = psi} + {phi <> psi}.
Proof. decide equality; apply string_dec. Defined.

Definition erase_nnf := set_remove nnf_eqdec.
Definition inter_nnf := set_inter nnf_eqdec.
Definition remove_nnf := remove nnf_eqdec.

Fixpoint neg_nnf (xi : nnf) : nnf :=
  match xi with
  | var p       => neg p
  | neg p       => var p
  | and phi psi => or (neg_nnf phi) (neg_nnf psi)
  | or phi psi  => and (neg_nnf phi) (neg_nnf psi)
  | ebef phi psi => aunt (neg_nnf phi) psi
  | eunt phi psi => abef (neg_nnf phi) psi
  | abef phi psi => eunt (neg_nnf phi) psi
  | aunt phi psi => ebef (neg_nnf phi) psi
  | enext phi    => anext (neg_nnf phi)
  | anext phi    => enext (neg_nnf phi)
  end.

Definition nnf_isalpha (phi : nnf) : Prop :=
  match phi with
  | and _ _ => True
  | abef _ _ => True
  | ebef _ _ => True
  (*edit mark*)
  | _       => False
  end.

Definition nnf_isalpha_dec (phi : nnf) :
  {nnf_isalpha phi} + {~ nnf_isalpha phi}.
Proof. destruct phi; ((now left)||(now right)). Defined.

Definition get_alpha : forall G : list nnf,
  {phi : nnf | In phi G /\ nnf_isalpha phi} +
  {forall phi, In phi G -> ~ nnf_isalpha phi}.
Proof.
induction G as [|phi G'].
- right. simpl. tauto.
- destruct IHG' as [Hl|Hr].
  + left. destruct Hl as [psi Hin]. exists psi. simpl. tauto.
  + destruct (nnf_isalpha_dec phi) as [Halpha|Hnalpha].
    * left. exists phi. split; [now left|assumption].
    * right. intros psi H. destruct H as [H|H];
      [rewrite <- H|apply Hr]; assumption.
Defined.

Definition df_nnf : nnf := var "". (* an arbitrary default formula *)

Definition nnf_alpha1 (xi : nnf) : nnf :=
  match xi with
  | and phi psi => phi
  | ebef phi psi => neg_nnf psi
  | abef phi psi => neg_nnf psi
  | _       => df_nnf
  end.

Definition nnf_alpha2 (xi : nnf) : nnf :=
  match xi with
  | and phi psi => psi
  | ebef phi psi => or phi (enext (ebef phi psi))
  | abef phi psi => or phi (anext (abef phi psi))
  | _       => df_nnf
  end.

Definition nnf_isbeta (phi : nnf) : Prop :=
  match phi with
  | or _ _  => True
  | eunt _ _ => True
  | aunt _ _ => True
  | _       => False
  end.

Definition nnf_isbeta_dec (phi : nnf) :
  {nnf_isbeta phi} + {~ nnf_isbeta phi}.
Proof. destruct phi; ((now left)||(now right)). Defined.

Definition get_beta : forall G : list nnf,
  {phi : nnf | In phi G /\ nnf_isbeta phi} +
  {forall phi, In phi G -> ~ nnf_isbeta phi}.
Proof.
induction G as [|phi G'].
- right. simpl. tauto.
- destruct IHG' as [Hl|Hr].
  + left. destruct Hl as [psi Hin]. exists psi. simpl. tauto.
  + destruct (nnf_isbeta_dec phi) as [Hbeta|Hnbeta].
    * left. exists phi. split; [now left|assumption].
    * right. intros psi H. destruct H as [H|H];
      [rewrite <- H|apply Hr]; assumption.
Defined.

Definition nnf_beta1 (xi : nnf) : nnf :=
  match xi with
  | or phi psi  => phi
  | eunt phi psi => psi
  | aunt phi psi => psi
  | _       => df_nnf
  end.

Definition nnf_beta2 (xi : nnf) : nnf :=
  match xi with
  | or phi psi  => psi
  | eunt phi psi => and phi (enext (eunt phi psi))
  | aunt phi psi => and phi (anext (aunt phi psi))
  | _       => df_nnf
  end.

Lemma beta_not_alpha [phi] : nnf_isbeta phi -> ~ nnf_isalpha phi.
Proof. destruct phi; simpl; tauto. Qed.
