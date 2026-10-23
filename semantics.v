Require Import utils.
Require Import nnf.
Require Import seqt.

Require Import Compare_dec.
Require Import String.
Open Scope string_scope.
Require Import List.
Require Import ListSet.
Import ListNotations.
Require Import Lia.

Require Import Classical.

Set Implicit Arguments.

(*edit mark*)
Record kripke :=
{ world : Type;
  kseq  : world -> world -> Prop;
  val   : world -> string -> Prop }.



Definition path (M : kripke) := nat -> world M.

Definition path_reachable (M : kripke) (si : path M) (w : world M) : Prop := 
  si 0 = w /\ forall i : nat, kseq M (si i) (si (S i)).
(*edit mark*)
Definition kripke_complete (M : kripke) : Prop :=
forall w : world M, exists si, path_reachable si w .

Fixpoint force (M : kripke) (w : world M) (xi : nnf) : Prop :=
  match xi with
  | var p       => val M w p
  | neg p       => ~ val M w p
  | and phi psi => (force M w phi) /\ (force M w psi)
  | or phi psi  => (force M w phi) \/ (force M w psi)
  | eunt phi psi => exists si, path_reachable si w /\ 
    exists k, force M (si k) psi /\ forall i, i < k -> force M (si i) phi
  | ebef phi psi => exists si, path_reachable si w /\
    forall k, force M (si k) psi -> exists i, i < k /\ force M (si i) phi
  | aunt phi psi => forall si, path_reachable si w ->
    exists k, force M (si k) psi /\ forall i, i < k -> force M (si i) phi
  | abef phi psi => forall si, path_reachable si w ->
    forall k, force M (si k) psi -> exists i, i < k /\ force M (si i) phi
  | enext phi    => exists w', kseq M w w' /\ force M w' phi
  | anext phi    => forall w', kseq M w w' -> force M w' phi
  end.

Definition sat (M : kripke) (w : world M) (G : list nnf) : Prop :=
  forall phi, In phi G -> force M w phi.

Definition satable (G : list nnf) : Prop := exists M w, kripke_complete M /\ sat M w G.

Definition unsatable G := forall M i, kripke_complete M -> ~sat M i G. 

Section SemanticsMore.

  Variable M : kripke.

  (*the next two lemmas may not be useful, the construct of v makes the prove
  v is on si and have a path following the route of si*)
  Lemma seriality :
   kripke_complete M -> forall w , exists v , kseq M w v.
  Proof.
  intros kc w. specialize (kc w). destruct kc as [si [pr0 pr1]].
  specialize (pr1 0). exists (si 1). rewrite pr0 in pr1. assumption.
  Qed.
  
  Lemma path_reachable_start:
  forall si (w: world M), path_reachable si w -> (si 0) = w.
  Proof.
  intros si w pr. destruct pr as [pr1 pr0].
  assumption.
  Qed.

  (* Requires XM *)
  Lemma nnf_true_is_true : forall w, force M w nnf_true.
  Proof.
  intro w. simpl. apply classic.
  Qed.
  
  Lemma nnf_false_is_false : forall w, ~ force M w nnf_false.
  Proof.
  intros i H. destruct H. contradiction.
  Qed.
  


Search (imply_to_and).
  (* Requires XM *)
 Lemma force_not_neg :
    forall [w phi], ~ force M w phi -> force M w (neg_nnf phi).
  Proof.
  intros w phi; revert w.
  induction phi; intros w H; simpl in H |- *.
  - assumption.
  - apply NNPP. assumption.
  - apply not_and_or in H. destruct H as [H|H].
    + left. apply IHphi1. assumption.
    + right. apply IHphi2. assumption.
  - apply not_or_and in H. destruct H as [H1 H2]. split.
    + apply IHphi1. assumption.
    + apply IHphi2. assumption.
  -  intros si. apply not_ex_all_not with (n:= si) in H. 
    apply not_and_or in H.  destruct H as [H | H].
    try contradiction. apply not_all_ex_not in H. destruct H as [k H].
    apply imply_to_and in H. destruct H as [H1 H]. intros H0. 
    exists k. split. apply H1. intros i. apply not_ex_all_not with (n:=i) in H.
    intros ilek. apply IHphi1. intro Hphi. apply H. split; assumption.
  - intros si. apply not_ex_all_not with (n:= si) in H. 
    apply not_and_or in H. destruct H as [H | H]. try contradiction. intros pr k.
    apply not_ex_all_not with (n:=k) in H. apply not_and_or in H. destruct H as [H | H].
    try contradiction. intros forphi2. apply not_all_ex_not in H. destruct H as [i H].
    exists i. apply imply_to_and in H. destruct H as [leik H]. split. apply leik.
    apply IHphi1. apply H.
  - apply not_all_ex_not in H. destruct H as [si H]. exists si. apply imply_to_and in H.
    destruct H as [pr H]. split. apply pr. apply not_all_ex_not in H. destruct H as [k H].
    exists k. apply imply_to_and in H. destruct H as [forphi2 H]. split. apply forphi2.
    intros i. apply not_ex_all_not with (n:=i) in H. apply not_and_or in H.
    destruct H as [H | H]. try contradiction. apply IHphi1 in H. intros ilek; exact H.
  - apply not_all_ex_not in H. destruct H as [si H]. exists si. apply imply_to_and in H.
    destruct H as [pr H]. split. apply pr. intros k. apply not_ex_all_not with (n:=k) in H.
    apply not_and_or in H. destruct H as [H | H]. try contradiction. apply not_all_ex_not in H.
    intros forphi2. destruct H as [i H]. exists i. apply imply_to_and in H. 
    destruct H as [ilek H]. split. exact ilek. apply IHphi1. exact H.
  - intros w'. apply not_ex_all_not with (n:= w') in H. apply not_and_or in H.
    destruct H as [H | H]. try contradiction. intros w2w'. apply IHphi. exact H.
  - apply not_all_ex_not in H. destruct H as [w' H]. exists w'. apply imply_to_and in H.
    destruct H as [w2w' H]. split. exact w2w'. apply IHphi. exact H.
  Qed.

  (* Does not require XM *)
  Lemma force_neg_not :
    forall [w phi], force M w (neg_nnf phi) -> ~ force M w phi.
  Proof.
  intros w phi; revert w.
  induction phi; intros w H; simpl in H |- *.
  - assumption.
  - intro Hctr. contradiction.
  - intro Hctr. destruct H as [H|H].
    + apply (IHphi1 _ H). tauto.
    + apply (IHphi2 _ H). tauto.
  - intro Hctr. destruct Hctr as [Hctr|Hctr].
    + contradict Hctr. apply IHphi1. tauto.
    + contradict Hctr. apply IHphi2. tauto.
  - intro Hctr. destruct Hctr as [si [pr Hctr]].
    specialize (H si pr). destruct H as [k [forphi2 H]].
    specialize (Hctr k forphi2). destruct Hctr as [i [ilek Hctr]].
    specialize (H i ilek). apply IHphi1 in H. apply H in Hctr. assumption.
  - intro Hctr. destruct Hctr as [si [pr [k [forphi2 Hctr]]]].
    specialize (H si pr k forphi2). destruct H as [i [ilek H]].
    specialize (Hctr i ilek). contradict Hctr.
    apply IHphi1. assumption.
  - intro Hctr. destruct H as [si [pr [k [forphi2 H]]]].
    specialize (Hctr si pr k forphi2). destruct Hctr as [i [ilek Hctr]].
    specialize (H i ilek). contradict Hctr.
    apply IHphi1. assumption.
  - intro Hctr. destruct H as [si [pr H]].
    specialize (Hctr si pr). destruct Hctr as [k [forphi2 Hctr]].
    specialize (H k forphi2). destruct H as [i [ilek H]].
    specialize (Hctr i ilek). apply IHphi1 in H. apply H in Hctr. assumption.
  - intros Hctr. destruct Hctr as [w'[w2w' Hctr]].
    specialize (H w' w2w'). contradict Hctr. apply IHphi. assumption.
  - intros Hctr. destruct H as [w'[w2w' H]].
    specialize (Hctr w' w2w'). contradict Hctr. apply IHphi. assumption.
  Qed.


  (* Requires XM *)
  Theorem force_neg_not_iff :
    forall {w phi}, force M w (neg_nnf phi) <-> ~ force M w phi.
  Proof.
  intros w phi. revert w.
  induction phi as [p|p|phi1 IHphi1 phi2 IHphi2|phi1 IHphi1 phi2 IHphi2|
  phi1 IHphi1 phi2 IHphi2|phi1 IHphi1 phi2 IHphi2|phi1 IHphi1 phi2 IHphi2|
  phi1 IHphi1 phi2 IHphi2|phi0 IHphi0|phi0 IHphi0];
  intro w; simpl; try tauto.
  - setoid_rewrite IHphi1. setoid_rewrite IHphi2. tauto.
  - setoid_rewrite IHphi1. setoid_rewrite IHphi2. tauto.
  - setoid_rewrite IHphi1. split.
    + intros H Hctr. destruct Hctr as [si [pr Hctr]].
      specialize (H si pr). destruct H as [k [forphi2 H]].
      specialize (Hctr k forphi2). destruct Hctr as [i [ilek Hctr]].
      specialize (H i ilek). contradict Hctr. assumption.
    + intros H si . apply not_ex_all_not with (n:=si) in H. apply not_and_or in H.
      destruct H as [H | H]. try contradiction. intros pr. apply not_all_ex_not in H.
      destruct H as [k H]. exists k. apply imply_to_and in H. destruct H as [forphi2 H].
      split. assumption. intro i. apply not_ex_all_not with (n:=i) in H. apply not_and_or in H.
      intros ilek. destruct H as [H | H]. try contradiction. assumption.
  - setoid_rewrite IHphi1. split.
    + intros H Hctr. destruct Hctr as [si [pr [ k [forphi2 Hctr]]]].
      specialize (H si pr k forphi2). destruct H as [i [ilek H]].
      specialize (Hctr i ilek). contradict Hctr. assumption.
    + intros H si pr k forphi2.
      apply not_ex_all_not with (n:=si) in H.
      repeat (apply not_and_or in H; destruct H; try contradiction).
      apply not_ex_all_not with (n:=k) in H.
      repeat (apply not_and_or in H; destruct H; try contradiction).
      apply not_all_ex_not in H. destruct H as [j H].
      exists j. apply imply_to_and in H. split; tauto.
  - setoid_rewrite IHphi1. split.
    + intros H Hctr. destruct H as [si [pr [ k [forphi2 H]]]].
      specialize (Hctr si pr k forphi2). destruct Hctr as [i [ilek Hctr]].
      specialize (H i ilek). contradict Hctr. assumption.
    + intros H. apply not_all_ex_not in H. destruct H as [si H]. apply imply_to_and in H.
      destruct H as [pr H]. exists si. split. assumption. apply not_all_ex_not in H. 
      destruct H as [k H]. apply imply_to_and in H.
      destruct H as [forphi2 H]. exists k. split. assumption.  intros i ilek.
      apply not_ex_all_not with (n:=i) in H. apply not_and_or in H. destruct H as [H|H].
      try contradiction. assumption.
  - setoid_rewrite IHphi1. split.
    + intros H Hctr. destruct H as [si [pr H]].
      specialize (Hctr si pr). destruct Hctr as [k [forphi2 Hctr]].
      specialize (H k forphi2). destruct H as [i [ilek H]].
      specialize (Hctr i ilek). contradict Hctr. assumption.
    + intros H. apply not_all_ex_not in H. destruct H as [si H]. apply imply_to_and in H.
      destruct H as [pr H]. exists si. split. assumption. intros k. 
      apply not_ex_all_not with (n:=k) in H. apply not_and_or in H. intros forphi2. destruct H as [H|H].
       try contradiction. apply not_all_ex_not in H.
      destruct H as [i H]. exists i. apply imply_to_and in H. destruct H as [ilek H].
      split; tauto.
  - split. 
    + intros H Hctr. destruct Hctr as [w' [w2w' Hctr]].
     specialize (H w' w2w'). contradict Hctr. apply IHphi0. assumption.
    + intros H w' w2w'. apply not_ex_all_not with (n:=w') in H. 
      apply not_and_or in H. destruct H as [H|H]. try contradiction.
      apply IHphi0. assumption.
  - split.
    + intros H Hctr. destruct H as [w' [w2w' H]].
     specialize (Hctr w' w2w'). contradict Hctr. apply IHphi0. assumption.
    + intros H. apply not_all_ex_not in H. destruct H as [w' H].
      apply imply_to_and in H. exists w'. destruct H as [w2w' H]. 
      apply IHphi0 in H. split;tauto. 
  Qed.

  Lemma sat_subset :
    forall [i G G'], incl G' G -> sat M i G -> sat M i G'.
  Proof.
  intros i G G' H H0. intros phi Hphi. apply H0. apply H. assumption.
  Qed.

  Lemma sat_eqset :
    forall [i G G'], eqset G G' -> (sat M i G <-> sat M i G').
  Proof.
  intros i G G' H. split; apply sat_subset; apply H.
  Qed.

  Lemma odd_one_out : forall [i phi G],
    unsatable (phi :: G) -> kripke_complete M -> sat M i G -> ~ force M i phi.
  Proof.
  intros i phi G H KM H0 H1. apply (H M i). exact KM. intros psi Hpsi.
  destruct Hpsi as [Hpsi|Hpsi].
  - rewrite <- Hpsi. assumption.
  - apply H0. assumption.
  Qed.

  (* Requires XM *)
  Theorem force_alpha_iff :
  kripke_complete M ->
    forall [w phi], nnf_isalpha phi ->
      (force M w phi <->
      force M w (nnf_alpha1 phi) /\ force M w (nnf_alpha2 phi)).
  Proof.
  intros kc w phi aphi. split.
  - intro H. destruct phi; try contradiction;
    simpl in H |- *; try assumption. split.
    + apply force_neg_not_iff. intro Hctr.
      destruct H as [si [pr H]]. destruct pr as [si0 pri]. 
      specialize (H 0). rewrite <- si0 in Hctr. specialize (H Hctr).
      destruct H as [i [ile0 forphi1]]. try lia. 
    + destruct (classic (force M w phi1)) as [forphi1|nforphi1];
      try (now left). right. destruct H as [si [pr H]].
      destruct pr as [si0 pri]. specialize (pri 0) as pr1.
      rewrite si0 in pr1. exists (si 1). split. assumption.
      exists (fun k => si (S k)). split. unfold path_reachable.
      split. reflexivity. intro i. specialize (pri (S i)) as prS_i. 
      exact prS_i. intros k. specialize (H (S k)). intros forphi2.
      destruct H as [i H]. assumption. destruct H as [Hlt Hphi1].
      destruct i as [| i0]. rewrite si0 in Hphi1. try contradiction.
      exists i0. split. apply (Arith_prebase.lt_S_n_stt) in Hlt. assumption.
      assumption.
    + split. specialize (kc w). destruct kc as [si pr]. 
      specialize (H si pr 0). destruct pr as [pr0 pri].
      rewrite pr0 in H. apply force_neg_not_iff. intros Hctr.
      specialize (H Hctr). destruct H as [i [ile0 forphi10]].
      contradict ile0. try lia.
      destruct (classic (force M w phi1)) as [forphi1|nforphi1]. 
      try (now left). right. intros w' w2w' si pr_si_w' k forphi2.
      set (si1 := fun k =>
      match k with
      | 0 => w
      | S k' => si k'
      end). specialize (H si1). 
      assert (pr_si1_w : path_reachable si1 w).
      { 
        split. simpl. reflexivity.
        destruct pr_si_w' as [pr_si_w'0 pr_si_w'1].
        intros i. destruct i as [|i0].
        simpl. rewrite pr_si_w'0. assumption.
        simpl. specialize (pr_si_w'1 i0). assumption.
      }
      specialize (H pr_si1_w (S k)). simpl in H. 
      specialize (H forphi2). destruct H as [i H].
      destruct i as [|i0]. destruct H as [ le0sk forphi1]. 
      simpl in forphi1. try contradiction.
      exists i0. destruct H as [Si0leSk forphi1].
      split. apply (Arith_prebase.lt_S_n_stt) in Si0leSk. assumption.
      simpl in forphi1. assumption.
      (*edit mark*)
  - intro H. destruct phi; try contradiction;
    simpl in H |- *; try assumption.
    + destruct H as [for_n_phi2 H]. destruct H as [forphi1 | H].
      specialize (kc w). destruct kc as [si pr]. 
      exists si. split. assumption.
      destruct pr as [pr0 pr1]. intros k. destruct k as [|k0].
      rewrite pr0. apply force_neg_not_iff in for_n_phi2.
      try contradiction. intros forphi2. exists 0.
      split ; try lia. rewrite pr0; assumption. 
      destruct H as [w'[w2w'[si[pr_si_w' H]]]].
      set (si1 := fun k =>
      match k with
      | 0 => w
      | S k' => si k'
      end). exists si1. 
      assert (pr_si1_w : path_reachable si1 w).
      { 
        split. simpl. reflexivity.
        destruct pr_si_w' as [pr_si_w'0 pr_si_w'1].
        intros i. destruct i as [|i0].
        simpl. rewrite pr_si_w'0. assumption.
        simpl. specialize (pr_si_w'1 i0). assumption.
      } split. assumption. intros k forphi2. 
      destruct k as [|k0].  simpl in forphi2. 
      apply force_neg_not_iff in for_n_phi2. try contradiction.
      specialize (H k0). simpl in forphi2. specialize(H forphi2).
      destruct H as [i [ilek0 forphi1]]. exists (S i).
      split. apply (PeanoNat.Nat.succ_lt_mono) in ilek0. 
      assumption. simpl. assumption.
    + destruct H as [for_n_phi2 H]. intros si pr k for_k_phi2. 
      destruct pr as [pr0 pr1].  destruct k as [|k0].
      apply force_neg_not_iff in for_n_phi2.
       rewrite pr0 in for_k_phi2.
      try contradiction. destruct H as [forphi1 | H].
       exists 0. split. try lia.
      rewrite pr0. assumption. pose proof (pr1 0) as pr1_0.
      rewrite pr0 in pr1_0. specialize (H (si 1) pr1_0).
      specialize (H (fun k => si(S k))).
      assert (pr_si1_w' : 
      path_reachable (fun k : nat => si (S k)) (si 1)).
      { 
        split. simpl. reflexivity.
        simpl. intro i. specialize (pr1 (S i)) ;assumption.
      } 
      specialize (H pr_si1_w' k0 for_k_phi2). 
      destruct H as [i [ilek0 forphi1]]. exists (S i).
      split.  apply (PeanoNat.Nat.succ_lt_mono) in ilek0.
      assumption. assumption.
  Qed.
  (* Requires XM (sequence not defined(*edit mark*))*)
  Lemma sat_alpha_child (KM : kripke_complete M):
    forall [i phi s], nnf_isalpha phi ->
    In phi (s_G s) -> sat M i (s_G s) ->
      sat M i (s_G (alpha_child phi s)).
  Proof.
  intros i phi s aphi Hin Hsat. simpl.
  pose proof (Hsat _ Hin) as H.
  rewrite (force_alpha_iff KM aphi) in H.
  intros psi Hpsi. destruct Hpsi as [Hpsi|[Hpsi|Hpsi]].
  - rewrite <- Hpsi. tauto.
  - rewrite <- Hpsi. tauto.
  - apply Hsat. apply in_remove with nnf_eqdec phi.
    assumption.
  Qed.

  Theorem force_beta_iff :
    kripke_complete M ->
    forall [w phi], nnf_isbeta phi ->
      (force M w phi <->
      force M w (nnf_beta1 phi) \/ force M w (nnf_beta2 phi)).
  Proof.
  intros kc w phi bphi. split.
  - intro H. simpl in H. destruct phi; try contradiction.
    + simpl in H |- *. assumption.
    + simpl in H |- *. destruct H as [si [pr [k [for_k_phi2 H]]]].
      destruct pr as [pr0 pr1].
      destruct (classic(force M w phi2)) as [forphi2 | nforphi2].
      left; assumption. right. destruct k as [|k0].
      rewrite pr0 in for_k_phi2. 
     contradiction. pose proof(H 0) as H0. 
      pose (PeanoNat.Nat.lt_0_succ k0) as le0sk0. 
      specialize (H0 le0sk0).
      rewrite pr0 in H0. split; try assumption.
      exists (si 1). pose proof(pr1 0) as w2w'. rewrite pr0 in w2w'.
      split; try assumption. exists(fun k => si(S k)). split. split.
      reflexivity. intro i. specialize (pr1 (S i)) ; assumption.
      exists k0; split; try assumption. intros i ilek0. 
      apply (PeanoNat.Nat.succ_lt_mono) in ilek0. specialize (H (S i) ilek0).
      assumption.
    + simpl in H |- *. destruct (classic(force M w phi2)) as [forphi2 | nforphi2].
      left; assumption. right. split. specialize (kc w). destruct kc as [si pr].
      specialize (H si pr). destruct H as [k[for_k_phi2 H]].
      destruct k as [|k0]. apply path_reachable_start in pr. 
      rewrite pr in for_k_phi2. try contradiction. 
      pose proof (PeanoNat.Nat.lt_0_succ k0) as le0sk.
      specialize (H 0 le0sk). apply path_reachable_start in pr.
      rewrite pr in H. assumption. intros w' w2w' si pr_si_w'.
      set (si1 := fun k =>
      match k with
      | 0 => w
      | S k' => si k'
      end). specialize (H si1). 
      assert (pr_si1_w : path_reachable si1 w).
      { 
        split. simpl. reflexivity.
        destruct pr_si_w' as [pr_si_w'0 pr_si_w'1].
        intros i. destruct i as [|i0].
        simpl. rewrite pr_si_w'0. assumption.
        simpl. specialize (pr_si_w'1 i0). assumption.
      } 
      specialize (H pr_si1_w). destruct H as [k[for_k_phi2 H]].
      destruct k as [|k0]. apply path_reachable_start in pr_si1_w. 
      rewrite pr_si1_w in for_k_phi2. try contradiction.
      exists (k0). split; try assumption. intros i ilek0.
      apply (PeanoNat.Nat.succ_lt_mono) in ilek0.  specialize (H (S i) ilek0).
      assumption.
  - intro H. destruct phi; try contradiction; simpl in H |- *.
    + assumption.
    + destruct H as [H|H].
      * specialize(kc w). destruct kc as [si pr].
        exists si. split ; try assumption. exists 0.
        split ; try lia. apply path_reachable_start in pr. rewrite pr.
        assumption.
      * destruct H as [forphi1 [w'[w2w'[si[pr_si_w'[k[for_k_phi2 H]]]]]]].
        set (si1 := fun k =>
         match k with
        | 0 => w
        | S k' => si k'
        end). exists si1. split. split. simpl. reflexivity.
        destruct pr_si_w' as [pr_si_w'0 pr_si_w'1].
        intros i. destruct i as [|i0].
        simpl. rewrite pr_si_w'0. assumption.
        simpl. specialize (pr_si_w'1 i0). assumption.
        exists (S k). split; try assumption. destruct  i as [|i0].
        intros le0sk. simpl. assumption.
        intro i0lesk. apply PeanoNat.Nat.succ_lt_mono in i0lesk. 
        specialize(H i0 i0lesk). try assumption.
    + destruct H as [H|H]. 
      * intros si pr. exists 0.
        split; try lia. destruct pr as [pr0 pr1]. rewrite pr0.
        assumption.
      
      * intros si pr. destruct H as [forphi1 H].
       destruct pr as [pr0 pr1]. pose proof (pr1 0) as w2w'. rewrite pr0 in w2w'.
        specialize (H (si 1) w2w').  specialize (H (fun k => si(S k))).
      assert (pr_si1_w' : 
      path_reachable (fun k : nat => si (S k)) (si 1)).
      { 
        split. simpl. reflexivity.
        simpl. intro i. specialize (pr1 (S i)) ;assumption.
      } specialize (H pr_si1_w'). destruct H as [k [for_k_phi2 H]].
        exists (S k). split; try assumption. destruct i as [|i0].
        intro le0sk. rewrite pr0. assumption. intro leSi0Sk. 
        apply PeanoNat.Nat.succ_lt_mono in leSi0Sk.
        specialize(H i0 leSi0Sk). try assumption. 
  Qed.
(*edit mark sequence not defined*)
Lemma unsat_beta1_sat_beta2 (KM : kripke_complete M):
    forall [i phi s], nnf_isbeta phi ->
    In phi (s_G s) -> sat M i (s_G s) ->
    unsatable (s_G (beta1_child phi s)) ->
      sat M i (s_G (beta2_child phi s)).
  Proof.
  intros i phi s bphi Hin Hsat Hunsat. simpl in Hunsat.
  assert (~ force M i (nnf_beta1 phi)) as nfor1.
  { apply (odd_one_out Hunsat).
  exact KM. apply sat_subset with (G := s_G s); try assumption.
  intros psi Hpsi. apply (in_remove nnf_eqdec _ _ _ Hpsi). }
  pose proof (Hsat _ Hin) as forphi.
  rewrite (force_beta_iff KM bphi) in forphi.
  destruct forphi as [for1|for2]; try contradiction.
  simpl. intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
  - rewrite <- Hpsi. assumption.
  - apply Hsat. apply (in_remove _ _ _ _ Hpsi).
  Qed.

  Lemma unsat_beta2_sat_beta1 (KM : kripke_complete M):
    forall [i phi s], nnf_isbeta phi ->
    In phi (s_G s) -> sat M i (s_G s) ->
    unsatable (s_G (beta2_child phi s)) ->
      sat M i (s_G (beta1_child phi s)).
  Proof.
  intros i phi s bphi Hin Hsat Hunsat. simpl in Hunsat.
  assert (~ force M i (nnf_beta2 phi)) as nfor2.
  { apply (odd_one_out Hunsat).
  exact KM; apply sat_subset with (G := s_G s); try assumption.
  intros psi Hpsi. pose proof (in_remove nnf_eqdec (s_G s) psi phi Hpsi) as [HinG Hneq]. 
  apply Hsat. exact HinG.  }
  pose proof (Hsat _ Hin) as forphi.
  rewrite (force_beta_iff KM bphi) in forphi.
  destruct forphi as [for1|for2]; try contradiction.
  simpl. intros psi Hpsi. destruct Hpsi as [Hpsi|Hpsi].
  - rewrite <- Hpsi. assumption.
  - apply Hsat. apply (in_remove _ _ _ _ Hpsi).
  Qed.

  Lemma unsat_beta1_not_force_psi_eunt (KM : kripke_complete M):
    forall [i phi psi s], sat M i (s_G s) ->
    unsatable (s_G (beta1_child (eunt phi psi) s)) ->
      ~ force M i psi.
  Proof.
  intros i phi psi s H H0. apply (odd_one_out H0).
  - exact KM.
  - apply sat_subset with (G := (s_G s)); try assumption.
  intro xi. apply (in_remove nnf_eqdec).
  Qed.

  Lemma unsat_beta1_not_force_psi_aunt (KM : kripke_complete M):
    forall [i phi psi s], sat M i (s_G s) ->
    unsatable (s_G (beta1_child (aunt phi psi) s)) ->
      ~ force M i psi.
  Proof.
  intros i phi psi s H H0. apply (odd_one_out H0).
  - exact KM.
  - apply sat_subset with (G := (s_G s)); try assumption.
  intro xi. apply (in_remove nnf_eqdec).
  Qed.


  Lemma sat_beta_children (KM : kripke_complete M): forall [i phi s],
    nnf_isbeta phi -> In phi (s_G s) -> sat M i (s_G s) ->
      sat M i (s_G (beta1_child phi s)) \/
      sat M i (s_G (beta2_child phi s)).
  Proof.
  intros i xi s bxi Hin H. pose proof (H _ Hin) as H0.
  rewrite (force_beta_iff KM bxi) in H0.
  destruct H0 as [H0|H0].
  - left. simpl. intros psi Hpsi.
    destruct Hpsi as [Hpsi|Hpsi].
    + rewrite <- Hpsi. assumption.
    + apply (H psi). apply (in_remove _ _ _ _ Hpsi).
  - right. simpl. intros psi Hpsi.
    destruct Hpsi as [Hpsi|Hpsi].
    + rewrite <- Hpsi. assumption.
    + apply (H psi). apply (in_remove _ _ _ _ Hpsi).
  Qed.

  Lemma sat_enext : forall w G phi, In phi (unenext G) -> sat M w G ->
    exists w',  kseq M w w' /\ force M w' phi.
  Proof. intros w G phi Hphi Hsat. apply in_unenext_in_enext in Hphi.
  apply Hsat in Hphi. simpl in Hphi. exact Hphi.
  Qed.

  Lemma sat_anext : forall w G phi, In phi (unanext G) -> sat M w G ->
    forall w', kseq M w w' -> force M w' phi.
  Proof.
  intros w G phi Hphi Hsat. apply in_unanext_in_anext in Hphi.
  apply Hsat in Hphi. simpl in Hphi. exact Hphi.
  Qed.

(*edit mark : for every child in jump_child exists a successor sat it*)
Lemma sat_jump_child :
  forall [w s child], kripke_complete M -> sat M w (s_G s) ->
    In child (jump_child s) -> exists v, kseq M w v /\ sat M v (s_G child).
Proof.
  intros w s child KM Hsat Hchild.
  unfold jump_child in Hchild.
  destruct (unenext (s_G s)) as [|phi L] eqn:Hun.

  - simpl in Hchild.
    destruct Hchild as [Hchild | Hchild].
    + rewrite <- Hchild. simpl.
      destruct (KM w) as [si Hpath]. 
      destruct Hpath as [Hroot Hstep].
      exists (si 1). split.
      * rewrite <- Hroot.
        exact (Hstep 0).
      * intros psi Hpsi.
        eapply sat_anext.
        -- exact Hpsi.
        -- exact Hsat.
        -- rewrite <- Hroot. exact (Hstep 0).
    + contradiction.
  - simpl in Hchild.
    destruct Hchild as [Hchild | Hchild].
    + rewrite <- Hchild. simpl.
      assert (Hin_phi : In phi (unenext (s_G s))).
      {
        rewrite Hun. simpl. now left.
      }
    destruct (sat_enext (w := w) (G := s_G s) phi Hin_phi Hsat) as [w' [Hw' Hphi]].
      exists w'. split.
      * exact Hw'.
      * intros psi Hpsi.
        destruct Hpsi as [Hpsi | Hpsi].
        -- rewrite <- Hpsi. exact Hphi.
        -- eapply sat_anext.
           ++ exact Hpsi.
           ++ exact Hsat.
           ++ exact Hw'.
    + apply in_map_iff in Hchild.
      destruct Hchild as [psi [Hchild Hpsi]].
      rewrite <- Hchild. simpl.
      assert (Hin_psi : In psi (unenext (s_G s))).
      {
        rewrite Hun. simpl. now right.
      }
      destruct (sat_enext (w := w) (G := s_G s) psi Hin_psi Hsat) as [w' [Hw' Hpsi_force]].
      exists w'. split.
      * exact Hw'.
      * intros xi Hxi.
        destruct Hxi as [Hxi | Hxi].
        -- rewrite <- Hxi. exact Hpsi_force.
        -- eapply sat_anext.
           ++ exact Hxi.
           ++ exact Hsat.
           ++ exact Hw'.
Qed.
  
(*edit mark : need to do stuffs before it*)
End SemanticsMore.

Lemma satable_subset :
forall [G G'], incl G' G -> satable G -> satable G'.
Proof.
intros G G' H [M [i Hi]]. exists M, i. destruct Hi as [Hkc Hsat]. split. assumption.
eapply sat_subset. apply H. assumption.
Qed.
(*sequence not defined*)
(* Requires XM *)

Corollary unsat_alpha_child :  forall [phi s],
  nnf_isalpha phi -> In phi (s_G s) ->
  unsatable (s_G (alpha_child phi s)) -> unsatable (s_G s).
Proof.
intros phi s aphi Hin  Hunsat M i KM Hsat.
apply Hunsat with M i.
exact KM.
apply sat_alpha_child; assumption.
Qed.

Corollary unsat_beta_children : forall [phi s],
  nnf_isbeta phi -> In phi (s_G s) ->
  unsatable (s_G (beta1_child phi s)) ->
  unsatable (s_G (beta2_child phi s)) ->
    unsatable (s_G s).
Proof.
intros phi s bphi Hin H H0 M i KM H1.
pose proof (sat_beta_children KM bphi Hin H1) as H2.
destruct H2 as [H2|H2].
- apply (H _ _ KM H2).
- apply (H0 _ _ KM H2).
Qed.

Corollary unsat_jump_child_exists :
  forall s, (exists child, In child (jump_child s) /\ unsatable (s_G child)) ->
    unsatable (s_G s).
Proof.
  intros s [child [Hchild Hunsat]] M w KM Hsat.
  destruct (sat_jump_child KM Hsat Hchild) as [v [Hseq Hsat_child]].
  apply (Hunsat M v); assumption.
Qed.

Lemma unsat_contra : forall [n s],
  In (var n) (s_G s) /\ In (neg n) (s_G s) ->
  unsatable (s_G s).
Proof.
intros n s [Hvar Hneg] M i KM Hsat. apply Hsat in Hvar, Hneg.
simpl in Hvar, Hneg. contradiction.
Qed. 
