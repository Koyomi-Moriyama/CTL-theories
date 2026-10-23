Require Import utils.
Require Import nnf.
(*Require Import seqt.*)
Require Import semantics.

Require Import List.
Import ListNotations.
Require Import String.
Open Scope string_scope.

Require Import Classical.


Inductive fml :=
  | varf (p : string)
  | negf (phi : fml)
  | andf (phi psi : fml)
  | orf (phi psi : fml)
  | implf (phi psi : fml)
  | ebeff (phi psi : fml)
  | euntf (phi psi : fml)
  | abeff (phi psi : fml)
  | auntf (phi psi : fml)
  | enextf (phi : fml)
  | anextf (phi : fml).


Fixpoint fml_force (M : kripke) (w : world M) (xi : fml) : Prop :=
  match xi with
  | varf p        => val M w p
  | negf phi      => ~ fml_force M w phi
  | andf phi psi  => fml_force M w phi /\ fml_force M w psi
  | orf phi psi   => fml_force M w phi \/ fml_force M w psi
  | implf phi psi => fml_force M w phi -> fml_force M w psi
  | euntf phi psi => exists si, path_reachable si w /\ 
    exists k,fml_force M (si k) psi /\ forall i, i < k ->fml_force M (si i) phi
  | ebeff phi psi => exists si, path_reachable si w /\
    forall k,fml_force M (si k) psi -> exists i, i < k /\fml_force M (si i) phi
  | auntf phi psi => forall si, path_reachable si w ->
    exists k,fml_force M (si k) psi /\ forall i, i < k ->fml_force M (si i) phi
  | abeff phi psi => forall si, path_reachable si w ->
    forall k,fml_force M (si k) psi -> exists i, i < k /\fml_force M (si i) phi
  | enextf phi    => exists w', kseq M w w' /\ fml_force M w' phi
  | anextf phi    => forall w', kseq M w w' -> fml_force M w' phi
  end.

Definition fml_sat (M : kripke) (w : world M) (G : list fml) : Prop :=
  forall phi, In phi G -> fml_force M w phi.

Definition fml_satable (G : list fml) : Prop := exists M w, fml_sat M w G.


Fixpoint to_nnf (xi : fml) : nnf :=
  match xi with
  | varf p        => var p
  | negf phi      => neg_nnf (to_nnf phi)
  | andf phi psi  => and (to_nnf phi) (to_nnf psi)
  | orf phi psi   => or (to_nnf phi) (to_nnf psi)
  | implf phi psi => or (neg_nnf (to_nnf phi)) (to_nnf psi)
  | ebeff phi psi  => ebef (to_nnf phi) (to_nnf psi)
  | euntf phi psi  => eunt (to_nnf phi) (to_nnf psi)
  | abeff phi psi  => abef (to_nnf phi) (to_nnf psi)
  | auntf phi psi  => aunt (to_nnf phi) (to_nnf psi)
  | enextf phi     => enext (to_nnf phi)
  | anextf phi     => anext (to_nnf phi)
  end.


(* The rest requires XM *)

Theorem force_fml_nnf_iff : forall M phi w,
  fml_force M w phi <-> force M w (to_nnf phi).
Proof.
  intros M phi. induction phi.
  - simpl. tauto.
  - simpl. setoid_rewrite IHphi.
    setoid_rewrite force_neg_not_iff. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2.
    setoid_rewrite force_neg_not_iff. intro i. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi1.
    setoid_rewrite IHphi2. tauto.
  - simpl. setoid_rewrite IHphi. tauto.
  - simpl. setoid_rewrite IHphi. tauto.
Qed.

Theorem sat_fml_nnf_iff : forall M G i,
  fml_sat M i G <-> sat M i (map to_nnf G).
Proof.
  intros M G. induction G as [|phi G].
  - intro i. split.
    + intro H. intros phi Hphi. contradict Hphi.
    + intro H. intros phi Hphi. contradict Hphi.
  - intro i. split.
    + intro H. intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * rewrite <- Hpsi. apply force_fml_nnf_iff.
        apply H. now left.
      * apply IHG; try assumption.
        intros xi Hxi. apply H. now right.
    + intro H. intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
      * rewrite <- Hpsi. apply force_fml_nnf_iff.
        apply H. now left.
      * apply IHG; try assumption.
        intros xi Hxi. apply H. now right.
Qed.
