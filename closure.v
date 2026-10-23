Require Import nnf.

Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Recdef.



Fixpoint nnf_size (xi : nnf) : nat :=
  match xi with
  | var n       => 0
  | neg n       => 0
  | and phi psi => 1 + nnf_size phi + nnf_size psi
  | or phi psi  => 1 + nnf_size phi + nnf_size psi
  | ebef phi psi => 1 + nnf_size phi + nnf_size psi
  | eunt phi psi => 1 + nnf_size phi + nnf_size psi
  | abef phi psi => 1 + nnf_size phi + nnf_size psi
  | aunt phi psi => 1 + nnf_size phi + nnf_size psi
  | enext phi    => 1 + nnf_size phi
  | anext phi    => 1 + nnf_size phi
  end. 

Theorem size_neg_eq_size {phi} : nnf_size (neg_nnf phi) = nnf_size phi.
Proof. induction phi; try (simpl; lia). Qed.

Function cl (xi : nnf) {measure nnf_size xi} : list nnf :=
  xi ::
  match xi with
  | var n       => []
  | neg n       => []
  | and phi psi => cl phi ++ cl psi
  | or phi psi  => cl phi ++ cl psi
  | ebef phi psi => enext (ebef phi psi) :: or phi (enext (ebef phi psi)) ::
      (cl phi ++ cl psi ++ cl (neg_nnf psi))  
  | abef phi psi => anext (abef phi psi) :: or phi (anext (abef phi psi)) ::
      (cl phi ++ cl psi ++ cl (neg_nnf psi))
  | eunt phi psi => enext (eunt phi psi) :: and phi (enext (eunt phi psi)) ::
      (cl phi ++ cl psi)  
  | aunt phi psi => anext (aunt phi psi) :: and phi (anext (aunt phi psi)) ::
      (cl phi ++ cl psi)
  | enext phi    => cl phi
  | anext phi    => cl phi
  end.
Proof.
all: intros; try (rewrite size_neg_eq_size); simpl; lia.
Defined.

Lemma in_cl_self : forall phi, In phi (cl phi).
Proof. induction phi; rewrite cl_equation; now left. Qed.

Lemma in_cl_alpha [phi psi] :
  nnf_isalpha phi ->
  In phi (cl psi) ->
    In (nnf_alpha1 phi) (cl psi) /\
    In (nnf_alpha2 phi) (cl psi).
Proof.
intro Hphi. destruct phi; try contradiction.
- intro H. functional induction (cl psi); try
  (simpl in H; destruct H; [discriminate|tauto]);
  destruct H as [H|H]; try discriminate; try
  (apply in_app_iff in H; destruct H as [H|H];
    [(specialize (IHl H); split; right;
      apply in_app_iff; left; tauto)|
    (specialize (IHl0 H); split; right;
      apply in_app_iff; right; tauto)]).
  + injection H. intros Heq2 Heq1. rewrite Heq1, Heq2.
    simpl. split; right; apply in_app_iff;
    [left|right]; apply in_cl_self.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
    + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    * injection H. intros Heq2 Heq1. simpl.
      rewrite <- Heq1, <- Heq2. split; right; [idtac|now left].
      right. right. apply in_app_iff.
      left. apply in_cl_self.
    * apply in_app_iff in H; destruct H as [H|H].
     -- specialize (IHl H); split; repeat right;
        apply in_app_iff; left; tauto.
     -- specialize (IHl0 H); split; repeat right;
        apply in_app_iff; right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    * injection H. intros Heq2 Heq1. simpl.
      rewrite <- Heq1, <- Heq2. split; right; [idtac|now left].
      right. right. apply in_app_iff.
      left. apply in_cl_self.
    * apply in_app_iff in H; destruct H as [H|H].
     -- specialize (IHl H); split; repeat right;
        apply in_app_iff; left; tauto.
     -- specialize (IHl0 H); split; repeat right;
        apply in_app_iff; right; tauto.
  + specialize (IHl H). split; right; tauto.
  + specialize (IHl H). split; right; tauto.
(*edit mark*)
- intro H. functional induction (cl psi);
  try (simpl in H; destruct H; [discriminate|tauto]);
  destruct H as [H|H]; try discriminate; try
  (apply in_app_iff in H; destruct H as [H|H];
    [(specialize (IHl H); split; right;
      apply in_app_iff; left; tauto)|
    (specialize (IHl0 H); split; right;
      apply in_app_iff; right; tauto)]).
  + injection H. intros Heq2 Heq1.
    simpl nnf_alpha1. simpl nnf_alpha2. 
    rewrite Heq1, Heq2. split.
    * repeat right. repeat (apply in_app_iff; right).
      apply in_cl_self.
    * right. right. now left.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + specialize (IHl H). split; right; tauto.
  + specialize (IHl H). split; right; tauto.
- intro H. functional induction (cl psi);
  try (simpl in H; destruct H; [discriminate|tauto]);
  destruct H as [H|H]; try discriminate; try
  (apply in_app_iff in H; destruct H as [H|H];
    [(specialize (IHl H); split; right;
      apply in_app_iff; left; tauto)|
    (specialize (IHl0 H); split; right;
      apply in_app_iff; right; tauto)]).
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + injection H. intros Heq2 Heq1.
    simpl nnf_alpha1. simpl nnf_alpha2. 
    rewrite Heq1, Heq2. split.
    * repeat right. repeat (apply in_app_iff; right).
      apply in_cl_self.
    * right. right. now left.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + specialize (IHl H). split; right; tauto.
  + specialize (IHl H). split; right; tauto.
Qed.

Lemma in_cl_beta [phi psi] :
  nnf_isbeta phi ->
  In phi (cl psi) ->
    In (nnf_beta1 phi) (cl psi) /\
    In (nnf_beta2 phi) (cl psi).
Proof.
intro Hphi. destruct phi; try contradiction.
- intro H. functional induction (cl psi);
  try (simpl in H; destruct H; [discriminate|tauto]);
  destruct H as [H|H]; try discriminate; try
  (apply in_app_iff in H; destruct H as [H|H];
    [(specialize (IHl H); split; right;
      apply in_app_iff; left; tauto)|
    (specialize (IHl0 H); split; right;
      apply in_app_iff; right; tauto)]).
  + injection H. intros Heq2 Heq1. rewrite Heq1, Heq2.
    simpl. split; right; apply in_app_iff;
    [left|right]; apply in_cl_self.
  + repeat (destruct H as [H|H]; try discriminate).
    * injection H. intros Heq2 Heq1. simpl.
      rewrite <- Heq1, <- Heq2. split; right; [idtac|now left].
      right. right. apply in_app_iff.
      left. apply in_cl_self.
    * apply in_app_iff in H; destruct H as [H|H].
     -- specialize (IHl H). split; repeat right;
        apply in_app_iff; left; tauto.
     -- apply in_app_iff in H. destruct H as [H|H].
        { specialize (IHl0 H). split; repeat right;
          apply in_app_iff; right; apply in_app_iff;
          left; tauto. }
        specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    * injection H. intros Heq2 Heq1. simpl.
      rewrite <- Heq1, <- Heq2. split; right; [idtac|now left].
      right. right. apply in_app_iff.
      left. apply in_cl_self.
    * apply in_app_iff in H; destruct H as [H|H].
     -- specialize (IHl H). split; repeat right;
        apply in_app_iff; left; tauto.
     -- apply in_app_iff in H. destruct H as [H|H].
        { specialize (IHl0 H). split; repeat right;
          apply in_app_iff; right; apply in_app_iff;
          left; tauto. }
        specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + specialize (IHl H). split; right; tauto.
  + specialize (IHl H). split; right; tauto.
- intro H. functional induction (cl psi);
  try (simpl in H; destruct H; [discriminate|tauto]);
  destruct H as [H|H]; try discriminate; try
  (apply in_app_iff in H; destruct H as [H|H];
    [(specialize (IHl H); split; right;
      apply in_app_iff; left; tauto)|
    (specialize (IHl0 H); split; right;
      apply in_app_iff; right; tauto)]).
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + injection H. intros Heq2 Heq1.
    simpl nnf_alpha1. simpl nnf_alpha2.
    rewrite Heq1, Heq2. split.
    * repeat right. repeat (apply in_app_iff; right).
      apply in_cl_self.
    * right. right. now left.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + specialize (IHl H). split; right; tauto.
  + specialize (IHl H). split; right; tauto.
- intro H. functional induction (cl psi);
  try (simpl in H; destruct H; [discriminate|tauto]);
  destruct H as [H|H]; try discriminate; try
  (apply in_app_iff in H; destruct H as [H|H];
    [(specialize (IHl H); split; right;
      apply in_app_iff; left; tauto)|
    (specialize (IHl0 H); split; right;
      apply in_app_iff; right; tauto)]).
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * apply in_app_iff in H. destruct H as [H|H].
     -- specialize (IHl0 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        left; tauto.
     -- specialize (IHl1 H). split; repeat right;
        apply in_app_iff; right; apply in_app_iff;
        right; tauto.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + injection H. intros Heq2 Heq1.
    simpl nnf_alpha1. simpl nnf_alpha2.
    rewrite Heq1, Heq2. split.
    * repeat right. repeat (apply in_app_iff; right).
      apply in_cl_self.
    * right. right. now left.
  + repeat (destruct H as [H|H]; try discriminate).
    apply in_app_iff in H. destruct H as [H|H].
    * specialize (IHl H). split; repeat right;
      apply in_app_iff; left; tauto.
    * specialize (IHl0 H). split; repeat right;
      apply in_app_iff; right; tauto.
  + specialize (IHl H). split; right; tauto.
  + specialize (IHl H). split; right; tauto.
Qed.

Lemma in_cl_enext [phi psi] :
  In (enext phi) (cl psi) -> In phi (cl psi).
Proof.
intro H. functional induction (cl psi);
try (simpl in H; destruct H; [discriminate|tauto]);
destruct H as [H|H]; try discriminate;
try (apply in_app_iff in H; destruct H as [H|H];
  [(specialize (IHl H); right; apply in_app_iff; left; tauto)|
  (specialize (IHl0 H); right; apply in_app_iff; right; tauto)]).
- destruct H as [H|H].
  + injection H. intro Heq. rewrite <- Heq. now left.
  + destruct H as [H|H]; try discriminate.
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl H). repeat right. apply in_app_iff. now left. }
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl0 H). repeat right. apply in_app_iff. right.
      apply in_app_iff. now left. }
    { specialize (IHl1 H). repeat right. repeat (apply in_app_iff; right).
    assumption. }
- destruct H as [H|H].
  + discriminate H.
  + destruct H as [H|H]; try discriminate.
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl H). repeat right. apply in_app_iff. now left. }
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl0 H). repeat right. apply in_app_iff. right.
      apply in_app_iff. now left. }
    { specialize (IHl1 H). repeat right. repeat (apply in_app_iff; right).
    assumption. }
- destruct H as [H|H].
  + injection H. intro Heq. rewrite <- Heq. now left.
  + destruct H as [H|H]; try discriminate.
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl H). repeat right. apply in_app_iff. now left. }
    { specialize (IHl0 H). repeat right. apply in_app_iff. now right. }
- destruct H as [H|H].
  + discriminate H.
  + destruct H as [H|H]; try discriminate.
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl H). repeat right. apply in_app_iff. now left. }
    { specialize (IHl0 H). repeat right. apply in_app_iff. now right. }
- injection H. intro Heq. rewrite Heq. right. apply in_cl_self.
- right. apply IHl. assumption.
- right. apply IHl. assumption.
Qed.
Lemma in_cl_anext [phi psi] :
  In (anext phi) (cl psi) -> In phi (cl psi).
Proof.
intro H. functional induction (cl psi);
try (simpl in H; destruct H; [discriminate|tauto]);
destruct H as [H|H]; try discriminate;
try (apply in_app_iff in H; destruct H as [H|H];
  [(specialize (IHl H); right; apply in_app_iff; left; tauto)|
  (specialize (IHl0 H); right; apply in_app_iff; right; tauto)]).
- destruct H as [H|H].
  + discriminate H.
  + destruct H as [H|H]; try discriminate.
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl H). repeat right. apply in_app_iff. now left. }
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl0 H). repeat right. apply in_app_iff. right.
      apply in_app_iff. now left. }
    { specialize (IHl1 H). repeat right. repeat (apply in_app_iff; right).
    assumption. }
- destruct H as [H|H].
  + injection H. intro Heq. rewrite <- Heq. now left.
  + destruct H as [H|H]; try discriminate.
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl H). repeat right. apply in_app_iff. now left. }
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl0 H). repeat right. apply in_app_iff. right.
      apply in_app_iff. now left. }
    { specialize (IHl1 H). repeat right. repeat (apply in_app_iff; right).
    assumption. }
- destruct H as [H|H].
  + discriminate H.
  + destruct H as [H|H]; try discriminate.
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl H). repeat right. apply in_app_iff. now left. }
    { specialize (IHl0 H). repeat right. apply in_app_iff. now right. }
- destruct H as [H|H].
  + injection H. intro Heq. rewrite <- Heq. now left.
  + destruct H as [H|H]; try discriminate.
    apply in_app_iff in H. destruct H as [H|H].
    { specialize (IHl H). repeat right. apply in_app_iff. now left. }
    { specialize (IHl0 H). repeat right. apply in_app_iff. now right. }
- right. apply IHl. assumption.
- injection H. intro Heq. rewrite Heq. right. apply in_cl_self.
- right. apply IHl. assumption.
Qed.
Definition cl_list := fold_right (fun phi l => cl phi ++ l) [].

Fixpoint cl_list' (G : list nnf) :=
  match G with
  | []         => []
  | phi :: Gtl => cl phi ++ cl_list' Gtl
  end.

Theorem incl_cl_list_self (G : list nnf) : incl G (cl_list G).
Proof.
induction G as [|phi Gtl].
- unfold incl. simpl. tauto.
- intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
  + rewrite Hpsi. simpl. apply in_app_iff. left.
    apply in_cl_self.
  + simpl. apply in_app_iff. right. apply IHGtl.
    assumption.
Qed.

Theorem in_cl_list_alpha [phi G] :
  nnf_isalpha phi ->
  In phi (cl_list G) ->
    In (nnf_alpha1 phi) (cl_list G) /\
    In (nnf_alpha2 phi) (cl_list G).
Proof.
intro Hphi. induction G as [|psi Gtl].
- tauto.
- intro H0. simpl in H0. apply in_app_iff in H0.
  destruct H0 as [H0|H0].
  + simpl. split; apply in_app_iff; left;
    apply in_cl_alpha; assumption.
  + specialize (IHGtl H0). simpl. split;
    apply in_app_iff; now right.
Qed.

Theorem in_cl_list_beta [phi G] :
  nnf_isbeta phi ->
  In phi (cl_list G) ->
    In (nnf_beta1 phi) (cl_list G) /\
    In (nnf_beta2 phi) (cl_list G).
Proof.
intro Hphi. induction G as [|psi Gtl].
- tauto.
- intro H0. simpl in H0. apply in_app_iff in H0.
  destruct H0 as [H0|H0].
  + simpl. split; apply in_app_iff; left;
    apply in_cl_beta; assumption.
  + specialize (IHGtl H0). simpl. split;
    apply in_app_iff; now right.
Qed.

Theorem in_cl_list_enext [phi G] :
  In (enext phi) (cl_list G) -> In phi (cl_list G).
Proof.
induction G as [|psi Gtl].
- tauto.
- intro H. simpl in H. apply in_app_iff in H.
  destruct H as [H|H].
  + simpl. apply in_app_iff; left;
    apply in_cl_enext; assumption.
  + specialize (IHGtl H). simpl.
    apply in_app_iff; now right.
Qed.
Theorem in_cl_list_anext [phi G] :
  In (anext phi) (cl_list G) -> In phi (cl_list G).
Proof.
induction G as [|psi Gtl].
- tauto.
- intro H. simpl in H. apply in_app_iff in H.
  destruct H as [H|H].
  + simpl. apply in_app_iff; left;
    apply in_cl_anext; assumption.
  + specialize (IHGtl H). simpl.
    apply in_app_iff; now right.
Qed.
(*edit mark*)