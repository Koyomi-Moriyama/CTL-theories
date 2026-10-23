Require Import utils.
Require Import nnf.
Require Import closure.
Require Import seqt.

Require Import Arith.
Require Import List.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Wellfounded.
Require Import Lia.
Require Import Program.



Definition lexnat2 : nat * nat  -> nat * nat -> Prop :=
  slexprod _ _ lt lt.

Theorem lexnat2_wf [alpha] (f : alpha -> nat * nat) :
  well_founded (MR lexnat2 f).
Proof.
unfold lexnat2. unfold MR.
apply wf_inverse_image. apply wf_slexprod; apply lt_wf.
Qed.

Fixpoint red_size (xi : nnf) : nat :=
  match xi with
  | var n       => 1
  | neg n       => 1
  | and phi psi => 1 + red_size phi + red_size psi
  | or phi psi  => 1 + red_size phi + red_size psi
  | ebef phi psi => 2 + red_size phi + red_size psi
  | eunt phi psi => 2 + red_size phi + red_size psi
  | abef phi psi => 2 + red_size phi + red_size psi
  | aunt phi psi => 2 + red_size phi + red_size psi
  | enext phi    => 0
  | anext phi    => 0
  end.

Lemma red_size_neg_eq {phi} : red_size (neg_nnf phi) = red_size phi.
Proof. induction phi; try (simpl; lia). Qed.

Lemma red_size_alpha1_lt {phi} :
  nnf_isalpha phi -> red_size (nnf_alpha1 phi) < red_size phi.
Proof.
intro H. destruct phi; try contradiction; simpl; try lia;
try(rewrite red_size_neg_eq; lia).
Qed.
Search S(_ + 0).
Lemma red_size_alpha2_lt {phi} :
  nnf_isalpha phi -> red_size (nnf_alpha2 phi) < red_size phi.
Proof.
intro H. destruct phi; try contradiction; simpl; try lia.
Qed.

Lemma red_size_beta1_lt {phi} :
  nnf_isbeta phi -> red_size (nnf_beta1 phi) < red_size phi.
Proof.
intro H. destruct phi; try contradiction; simpl; try lia.
Qed.

Lemma red_size_beta2_lt {phi} :
  nnf_isbeta phi -> red_size (nnf_beta2 phi) < red_size phi.
Proof.
intro H. destruct phi; try contradiction; simpl; try lia.
Qed.

Definition red_size_list := fold_right (fun phi n => red_size phi + n) 0.

Lemma red_size_list_mono : forall phi G,
  red_size_list (remove_nnf phi G) <= red_size_list G.
Proof.
intros phi G. induction G as [|psi].
- simpl. apply le_n.
- simpl. destruct (nnf_eqdec phi psi); simpl; lia.
Qed.

Definition seqt_size (s : doseqt) : nat * nat :=
  (length (power_set (cl_list (s_R s))) - length (s_H s),
   red_size_list (s_G s)).


Lemma size_remove_add_le_size_sum [phi G] : In phi G ->
red_size_list (remove_nnf phi G) + red_size phi <= red_size_list G.
Proof.
induction G as [|psi G'].
- simpl. contradiction.
- intro H. simpl in H. destruct H as [H|H].
  + rewrite H. simpl. destruct (nnf_eqdec phi phi); try contradiction.
    rewrite Nat.add_comm. apply add_le_mono_l_proj_l2r.
    apply red_size_list_mono.
  + simpl. destruct (nnf_eqdec phi psi) as [Heq|Hneq].
    * rewrite Heq. rewrite Nat.add_comm.
      apply add_le_mono_l_proj_l2r. apply red_size_list_mono.
    * simpl. rewrite <- (Nat.add_assoc). apply add_le_mono_l_proj_l2r.
      apply IHG'. assumption.
Qed.

Theorem alpha_child_decr_size [phi s] :
  nnf_isalpha phi -> In phi (s_G s) -> MR lexnat2 seqt_size (alpha_child phi s) s.
Proof.
intros Hphi Hin. simpl in Hin. constructor 2.
pose proof (size_remove_add_le_size_sum Hin) as H.
destruct phi; try contradiction.
- simpl. simpl in H. lia.
- simpl. simpl in H. rewrite (red_size_neg_eq). lia.
- simpl. simpl in H. rewrite (red_size_neg_eq). lia.
Qed.

Theorem beta1_child_decr_size [phi s] :
  nnf_isbeta phi -> In phi (s_G s) -> MR lexnat2 seqt_size (beta1_child phi s) s.
Proof.
intros Hphi Hin. simpl in Hin. constructor 2. 
pose proof (size_remove_add_le_size_sum Hin) as H.
destruct phi; try contradiction; simpl; simpl in H; lia. 
Qed.

Theorem beta2_child_decr_size [phi s] :
  nnf_isbeta phi -> In phi (s_G s) -> MR lexnat2 seqt_size (beta2_child phi s) s.
Proof.
intros Hphi Hin. simpl in Hin. constructor 2. 
pose proof (size_remove_add_le_size_sum Hin) as H.
destruct phi; try contradiction; simpl; simpl in H; lia.
Qed.
(*
Theorem jump_child_branch_decr_size {ss : rdoseqt} (sc : state_conditions (`ss))
:
  forall br, In br (jump_child (`ss)) -> MR lexnat2 seqt_size br (`ss).
Proof.
constructor 1. simpl.
pose proof (jump_child_pseqt ss sc nb parent_not_in_H ) as psec.
set (sec := jump_child (`ss)). 
rewrite Forall_forall in psec.
pose proof (psec br H) as Hbr_reg.
pose proof (nodup_H Hbr_reg) as ND.
unfold jump_child in H.
destruct (unenext (s_G (`ss))) as [| n l] eqn:Hunen.
- simpl in H. destruct H as [breq | contra].
 + 
symmetry in breq.
subst br.
simpl.
destruct Hbr_reg as [NDbr Gincbr Hincbr].
simpl in NDbr.
simpl in Gincbr.
simpl in Hincbr.
assert
  (HincA :
    inclA (eqset (A:=nnf)) (s_G (` ss) :: s_H (` ss))  (power_set (cl_list (s_R (` ss))))).
{
  intros G HG.
  apply InA_alt in HG.
  destruct HG as [G0 [HeqG HG0]].
  apply incl_inset_power_set.
  exact nnf_eqdec.
  intros phi Hphi.
    assert (HinG0 : In phi G0).
    {
      unfold eqset in HeqG.
      destruct HeqG as [HG_to_G0 _].
      apply HG_to_G0.
      exact Hphi.
    }

    apply Hincbr with (G := G0).
    + exact HG0.
    + exact HinG0.
}
pose proof
  (@NoDupA_set_incl_length nnf nnf_eqdec
     (s_G (` ss) :: s_H (` ss)) (power_set (cl_list (s_R (` ss))))
     NDbr HincA) as Hbound.
simpl in Hbound.
lia.
+ try contradiction.
- simpl in H.
  destruct H as [breq | H].
+ symmetry in breq.
  subst br.
  simpl in *.
  destruct Hbr_reg as [NDbr Gincbr Hincbr].
  simpl in NDbr.
  simpl in Hincbr.
  assert
  (HincA :
    inclA (eqset (A:=nnf))
      (s_G (` ss) :: s_H (` ss))
      (power_set (cl_list (s_R (` ss))))).
{
  intros G HG.
  apply InA_alt in HG.
  destruct HG as [G0 [HeqG HG0]].

  apply incl_inset_power_set.
  - exact nnf_eqdec.
  - intros a Ha.
    destruct HeqG as [HG_to_G0 _].
    apply Hincbr with (G := G0).
    + exact HG0.
    + apply HG_to_G0.
      exact Ha.
}

pose proof
  (@NoDupA_set_incl_length
     nnf
     nnf_eqdec
     (s_G (` ss) :: s_H (` ss))
     (power_set (cl_list (s_R (` ss))))
     NDbr
     HincA) as Hbound.

simpl in Hbound.
lia.
+ apply in_map_iff in H.
  destruct H as [phi [breq Hphi]].
  symmetry in breq.
  subst br.
  simpl in *.
  destruct Hbr_reg as [NDbr Gincbr Hincbr].
  simpl in NDbr.
  simpl in Hincbr.
  assert
  (HincA :
    inclA (eqset (A:=nnf))
      (s_G (` ss) :: s_H (` ss))
      (power_set (cl_list (s_R (` ss))))).
{
  intros G HG.
  apply InA_alt in HG.
  destruct HG as [G0 [HeqG HG0]].

  apply incl_inset_power_set.
  - exact nnf_eqdec.
  - intros a Ha.
    destruct HeqG as [HG_to_G0 _].
    apply Hincbr with (G := G0).
    + exact HG0.
    + apply HG_to_G0.
      exact Ha.
}

pose proof
  (@NoDupA_set_incl_length
     nnf
     nnf_eqdec
     (s_G (` ss) :: s_H (` ss))
     (power_set (cl_list (s_R (` ss))))
     NDbr
     HincA) as Hbound.

simpl in Hbound.
lia.
Qed.
*)

Lemma D_rule_red_size :
  forall s,
    red_size_list (s_G (D_rule s)) =
    red_size_list (s_G s).
Proof.
  intros s.
  unfold D_rule.
  destruct (unenext (s_G s)) as [| phi L] eqn:Hun.
   - reflexivity.
   - simpl.
    reflexivity.
Qed.

Theorem D_rule_size : forall s,
 seqt_size (D_rule s) = seqt_size s.
Proof.
  intros s.
  unfold seqt_size.
  f_equal.
Qed.

Theorem jump_child_branch_decr_size
  {ss : rdoseqt} :
  forall br,
    In br (jump_child (`ss)) ->
    MR lexnat2 seqt_size br (`ss).
Proof.
  intros br Hbr.
  constructor 1.
  simpl.
  pose proof
    (jump_child_regular ss)
    as Hchildren_regular.

  rewrite Forall_forall in Hchildren_regular.

  pose proof
    (Hchildren_regular br Hbr)
    as Hbr_reg.

  destruct ss as [ss rs].
  pose proof
    (jump_child_in_temporary_and_nodup_H rs br Hbr)
    as Htemporary.
  destruct Htemporary as [Htemporary Hnodup].
  assert
  (Hshape :
     s_R br = s_R ss /\
     s_H br =
       (s_G br, S (length (s_H ss))) :: s_H ss).
{
  split.
  - apply temporary_jump_child_R with (parent := ss) (child := br).
    exact Htemporary.
  - apply temporary_jump_child_history_shape with (parent := ss) (child := br).
    exact Htemporary.
}
destruct Hbr_reg as [NDbr Gincbr Hincbr].
destruct Hshape as [HR HH].
rewrite HR in Gincbr.
rewrite HH in NDbr.
simpl in NDbr.
rewrite HH in Hincbr.
rewrite HR in Hincbr.
simpl in Hincbr.
assert
  (HincA :
     inclA
       (@eqset nnf)
       (s_G br :: map fst (s_H ss))
       (power_set (cl_list (s_R ss)))).
{
  unfold inclA.
  intros G HG.
  apply InA_alt in HG.
  destruct HG as [G' [Heq Hin]].
  destruct Heq as [Hin_G_G' Hin_G'_G].
  simpl in Hin.
  destruct Hin as [HG' | HG'].
  - subst G'.
    apply incl_inset_power_set.
    apply nnf_eqdec.
    (* The newly inserted history entry is the generated child Gamma. *)
    eapply incl_tran.
    + exact Hin_G_G'.
    + exact Gincbr.
  - apply in_map_iff in HG'.
    destruct HG' as [[G0 n] [HG' HinH]].
    simpl in HG'.
    subst G'.
    apply incl_inset_power_set.
    apply nnf_eqdec.
    eapply incl_tran.
    + exact Hin_G_G'.
    + specialize (Hincbr (G0, n) (or_intror HinH)).
      simpl in Hincbr.
      exact Hincbr.
  }
pose proof
  (@NoDupA_set_incl_length
     nnf
     nnf_eqdec
     (s_G br :: map fst (s_H ss))
     (power_set (cl_list (s_R ss)))
     NDbr
     HincA)
  as Hbound.
rewrite HR.
rewrite HH.
simpl.
simpl in Hbound.
rewrite map_length in Hbound.
lia.
Qed.

(* The decrease argument depends only on regularity and on the fact that the
   current state has not already occurred in its history.  It applies to
   every member of the jump list, including lists of arbitrary length. *)
Corollary jump_children_decr_size (ss : rdoseqt) :
  Forall (fun child => MR lexnat2 seqt_size child (`ss))
         (jump_child (`ss)).
Proof.
  apply Forall_forall. intros child Hin.
  apply jump_child_branch_decr_size. exact Hin.
Qed.
