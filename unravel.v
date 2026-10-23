Require Import utils.
Require Import nnf.
Require Import closure.
Require Import semantics.
Require Import seqt.
Require Import ptree.
Require Import proper.

Require Import Arith.
Require Import Nat.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Wellfounded.
Require Import Lia.

Require Import Classical.

Set Implicit Arguments.

Section Unravelling.

Variable Tl : ltree.
Hypothesis gpt : gproper (l_root Tl).


Record uconfig : Type :=
{
  u_trail : list ptree;
  u_node  : ptree;
  u_in_root : u_node <=/ l_root Tl
}.


Definition alternate_choice
  (p : list ptree)
  (x c1 c2 : ptree) :=
  if even (count_occ ptree_eqdec p x)
  then c1
  else c2.


Lemma alternate_choice_or :
  forall p x c1 c2,
    alternate_choice p x c1 c2 = c1 \/
    alternate_choice p x c1 c2 = c2.
Proof.
  intros p x c1 c2.
  unfold alternate_choice.
  destruct (even (count_occ ptree_eqdec p x));
    [now left | now right].
Qed.


Definition blocked_target
  (x : ptree)
  (c : doseqt)
  (Hx : x <=/ l_root Tl)
  (Hb : blocked_candidate x c)
  : { y : ptree |
      loop_target x c y (l_root Tl) } :=
  l_looper Tl Hx Hb.


(*
Record psgu (prev curr : uconfig) : Prop :=
{
  sgu_trail_eq :
    u_trail curr =
      u_trail prev ++ [u_node prev];

  sgu_nonjump :
    ~ t_isjump (u_node prev) ->
    is_child (u_node curr) (u_node prev);

  sgu_jump :
    t_isjump (u_node prev) ->
    is_child (u_node curr) (u_node prev) \/
    exists c,
      blocked_candidate (u_node prev) c /\
      loop_target
        (u_node prev)
        c
        (u_node curr)
        (l_root Tl);

  sgu_alt_choice :
    forall c1 c2 bt fs phi,
      u_node prev = talt c1 c2 bt fs phi ->
      u_node curr =
        alternate_choice
          (u_trail prev)
          (u_node prev)
          c1 c2
}.
*)


Record unode : Type :=
{
  u_curr : uconfig
}.

(*
Lemma blocked_candidate_dec :
  forall x c,
    {blocked_candidate x c} +
    {~ blocked_candidate x c}.
Proof.
  intros x c.
Admitted.
*)

(* 10.14edit *)
(*
Lemma blocked_candidate_dec :
  forall x c,
    {blocked_candidate x c} +
    {~ blocked_candidate x c}.
Proof.
  intros x c.
  destruct x as [x fs xi|x bt fs xi|x bt fs xi|x1 x2 bt fs xi|cs fs xi].
  - right. intro H. destruct H as [H _]. simpl in H. contradiction.
  - right. intro H. destruct H as [H _]. simpl in H. contradiction.
  - right. intro H. destruct H as [H _]. simpl in H. contradiction.
  - right. intro H. destruct H as [H _]. simpl in H. contradiction.
  - destruct (in_dec seqt_eqdec c (temporary_jump_child (t_dose (tjump cs fs xi))))
    as [Hc|Hc].
    + destruct (get_blocker_G (s_G c) (t_dose (tjump cs fs xi))) as [Hb|Hnb].
      { left. split; [simpl; reflexivity|]. split; [exact Hc|].
        exists (proj1_sig Hb). exact (proj2_sig Hb). }
      { right. intro Hblocked. apply Hnb.
        destruct Hblocked as [_ [_ [h [Hhin Heq]]]].
        apply InA_alt. exists (fst h).
        split.
        - apply eqset_sym. exact Heq.
        - apply in_map. exact Hhin. }
    + right. intro Hblocked. apply Hc. exact (proj1 (proj2 Hblocked)).
Qed.
*)

(* 10.14edit *)
Lemma blocked_candidate_dec :
  forall x c,
    {blocked_candidate x c} +
    {~ blocked_candidate x c}.
Proof.
  intros x c.
  destruct x as [x fs xi|x bt fs xi|x bt fs xi|x1 x2 bt fs xi|cs fs xi].
  - right. intro H. destruct H as [H _]. simpl in H. contradiction.
  - right. intro H. destruct H as [H _]. simpl in H. contradiction.
  - right. intro H. destruct H as [H _]. simpl in H. contradiction.
  - right. intro H. destruct H as [H _]. simpl in H. contradiction.
  - destruct (in_dec seqt_eqdec c (temporary_jump_child (t_dose (tjump cs fs xi))))
    as [Hc|Hc].
    + destruct (get_blocker_G (s_G c) (t_dose (tjump cs fs xi))) as [Hb|Hnb].
      { left. split; [simpl; reflexivity|]. split; [exact Hc|].
        exists (proj1_sig Hb). exact (proj2_sig Hb). }
      { right. intro Hblocked. apply Hnb.
        destruct Hblocked as [_ [_ [h [Hhin Heq]]]].
        apply InA_alt. exists (fst h).
        split.
        - apply eqset_sym. exact Heq.
        - apply in_map. exact Hhin. }
    + right. intro Hblocked. apply Hc. exact (proj1 (proj2 Hblocked)).
Defined.

Definition virtual_target_of
  (x : ptree)
  (c : doseqt)
  (Hx : x <=/ l_root Tl)
  (Hb : blocked_candidate x c) : ptree :=
  proj1_sig (blocked_target Hx Hb).

Lemma virtual_target_of_spec :
  forall (x : ptree)
         (c : doseqt)
         (Hx : x <=/ l_root Tl)
         (Hb : blocked_candidate x c),
    loop_target
      x c
      (virtual_target_of (x := x) (c := c) Hx Hb)
      (l_root Tl).
Proof.
  intros x c Hx Hb.
  unfold virtual_target_of.
  destruct (blocked_target (x := x) (c := c) Hx Hb)
    as [y Hy].
  simpl.
  exact Hy.
Qed.

Definition virtual_target_opt
  (x : ptree)
  (Hx : x <=/ l_root Tl)
  (c : doseqt) : option ptree :=
  match blocked_candidate_dec x c with
  | left Hb =>
      Some (virtual_target_of (x := x) (c := c) Hx Hb)
  | right _ => None
  end.

Lemma virtual_target_opt_sound :
  forall (x : ptree) (Hx : x <=/ l_root Tl) (c : doseqt) (y : ptree),
    virtual_target_opt (x := x) Hx c = Some y ->
    blocked_candidate x c /\
    loop_target x c y (l_root Tl).
Proof.
  intros x Hx c y Hopt.
  unfold virtual_target_opt in Hopt.
  destruct (blocked_candidate_dec x c) as [Hb|Hnb].
  - split; [exact Hb|].
    injection Hopt. intro Heq. rewrite <- Heq.
    apply virtual_target_of_spec.
  - discriminate.
Qed.

Fixpoint virtual_targets_aux
  (x : ptree)
  (Hx : x <=/ l_root Tl)
  (cs : list doseqt)
  : list ptree :=
  match cs with
  | [] => []
  | c :: cs' =>
      match blocked_candidate_dec x c with
      | left Hb =>
          virtual_target_of
            (x := x) (c := c) Hx Hb
          ::
          virtual_targets_aux
            (x := x) Hx cs'
      | right _ =>
          virtual_targets_aux
            (x := x) Hx cs'
      end
  end.

Definition virtual_targets
  (x : ptree)
  (Hx : x <=/ l_root Tl)
  : list ptree :=
  virtual_targets_aux
    (x := x)
    Hx
    (temporary_jump_child (t_dose x)).

Definition virtual_step
  (x : ptree)
  (Hx : x <=/ l_root Tl)
  (y : ptree) : Prop :=
  exists c,
    In c (temporary_jump_child (t_dose x)) /\
    virtual_target_opt (x := x) Hx c = Some y.

Lemma virtual_target_opt_blocked :
  forall (x : ptree) (Hx : x <=/ l_root Tl) (c : doseqt)
    (Hb : blocked_candidate x c),
    virtual_target_opt (x := x) Hx c =
    Some (virtual_target_of (x := x) (c := c) Hx Hb).
Proof.
  intros x Hx c Hb. unfold virtual_target_opt.
  destruct (blocked_candidate_dec x c) as [Hb'|Hnb].
  - assert (E : Hb' = Hb) by apply proof_irrelevance.
    rewrite E. reflexivity.
  - contradiction.
Qed.

Lemma virtual_target_opt_unblocked :
  forall (x : ptree) (Hx : x <=/ l_root Tl) (c : doseqt),
    ~ blocked_candidate x c ->
    virtual_target_opt (x := x) Hx c = None.
Proof.
  intros x Hx c Hnb. unfold virtual_target_opt.
  destruct (blocked_candidate_dec x c) as [Hb|Hnb']; [contradiction|reflexivity].
Qed.

Lemma virtual_targets_aux_spec :
  forall (x : ptree) (Hx : x <=/ l_root Tl) (cs : list doseqt) (y : ptree),
    In y (virtual_targets_aux (x := x) Hx cs) <->
    exists c, In c cs /\
      virtual_target_opt (x := x) Hx c = Some y.
Proof.
  intros x Hx cs. induction cs as [|c cs IH]; intros y.
  - simpl. split.
    + intro H. contradiction.
    + intro H. destruct H as [c [H _]]. contradiction.
  - simpl. destruct (blocked_candidate_dec x c) as [Hb|Hnb].
    + simpl. rewrite IH. split.
      * intros [Heq|Hin].
        -- exists c. split; [left; reflexivity|].
           subst y. apply virtual_target_opt_blocked.
        -- destruct Hin as [c' [Hinc' Hopt]].
           exists c'. split; [right; exact Hinc'|exact Hopt].
      * intros [c' [Hinc Hopt]]. destruct Hinc as [Heq|Hinc].
        -- subst c'. left. rewrite (virtual_target_opt_blocked (x := x) (c := c) Hx Hb) in Hopt.
           injection Hopt. intro E. exact E.
        -- right. exists c'. split; assumption.
    + simpl. rewrite IH. split.
      * intros [c' [Hinc Hopt]]. exists c'. split; [right; exact Hinc|exact Hopt].
      * intros [c' [Hinc Hopt]]. destruct Hinc as [Heq|Hinc].
        -- subst c'. rewrite (virtual_target_opt_unblocked (x := x) (c := c) Hx Hnb) in Hopt. discriminate.
        -- exists c'. split; assumption.
Qed.

Lemma virtual_targets_spec :
  forall (x : ptree) (Hx : x <=/ l_root Tl) (y : ptree),
    In y (virtual_targets (x := x) Hx) <->
    virtual_step (x := x) Hx y.
Proof.
  intros x Hx y. unfold virtual_targets, virtual_step.
  apply virtual_targets_aux_spec.
Qed.

(* 10.14edit *)
Record psgu (prev curr : uconfig) : Prop :=
{
  sgu_trail_eq :
    u_trail curr = u_trail prev ++ [u_node prev];

  sgu_nonjump :
    ~ t_isjump (u_node prev) ->
    is_child (u_node curr) (u_node prev);

  sgu_jump :
    t_isjump (u_node prev) ->
    is_child (u_node curr) (u_node prev) \/
    virtual_step (x := u_node prev) (u_in_root prev) (u_node curr);

  sgu_alt_choice :
    forall c1 c2 bt fs phi,
      u_node prev = talt c1 c2 bt fs phi ->
      u_node curr =
        alternate_choice
          (u_trail prev)
          (u_node prev)
          c1 c2
}.

Definition jump_next_nodes
  (x : ptree)
  (Hx : x <=/ l_root Tl)
  : list ptree :=
  match x with
  | tjump cs fs xi =>
      nodup ptree_eqdec
        (cs ++ virtual_targets (x := x) Hx)
  | _ =>
      []
  end.


(* 
Lemma jump_next_nodes_spec :
  forall x Hx y,
    t_isjump x ->
    In y (jump_next_nodes (x := x) Hx) <->
      is_child y x \/
      exists c,
        blocked_candidate x c /\
        loop_target x c y (l_root Tl).
*)

(* 10.14edit *)
Lemma jump_next_nodes_spec :
  forall (x : ptree) (Hx : x <=/ l_root Tl) (y : ptree),
    t_isjump x ->
    In y (jump_next_nodes (x := x) Hx) <->
      is_child y x \/ virtual_step (x := x) Hx y.
Proof.
  intros x Hx y Hjump.
  destruct x as [c fs xi|c bt fs xi|c bt fs xi|c1 c2 bt fs xi|cs fs xi];
    simpl in Hjump; try contradiction.
  simpl.
  rewrite nodup_In.
  rewrite in_app_iff.
  rewrite virtual_targets_spec.
  tauto.
Qed.

Corollary jump_next_nodes_sound :
  forall (x : ptree) (Hx : x <=/ l_root Tl) (y : ptree),
    t_isjump x ->
    In y (jump_next_nodes (x := x) Hx) ->
    is_child y x \/
    exists c,
      blocked_candidate x c /\
      loop_target x c y (l_root Tl).
Proof.
  intros x Hx y Hjump Hin.
  apply (proj1 (jump_next_nodes_spec (x := x) Hx y Hjump)) in Hin.
  destruct Hin as [Hchild|Hvirtual].
  - left. exact Hchild.
  - right. destruct Hvirtual as [c [Hc Hopt]].
    exists c. exact (virtual_target_opt_sound (x := x) Hx c Hopt).
Qed.

Definition next_nodes
  (u : uconfig) : list ptree :=
  match u_node u with
  | talpha c _ _ => [c]
  | tbeta1 c _ _ _ => [c]
  | tbeta2 c _ _ _ => [c]
  | talt c1 c2 _ _ _ =>
      [alternate_choice (u_trail u) (u_node u) c1 c2]
  | tjump _ _ _ => jump_next_nodes (u_in_root u)
  end.

Lemma next_node_in_root :
  forall (u : uconfig) (y : ptree),
    In y (next_nodes u) -> y <=/ l_root Tl.
Proof.
  intros [trail x Hx] y Hin.
  destruct x as [c fs xi|c bt fs xi|c bt fs xi|c1 c2 bt fs xi|cs fs xi].
  - simpl in Hin.
    destruct Hin as [Hin|Hin]; [|contradiction].
    apply child_desceq with (y := talpha c fs xi).
    + simpl. exact (eq_sym Hin).
    + exact Hx.
  - simpl in Hin.
    destruct Hin as [Hin|Hin]; [|contradiction].
    apply child_desceq with (y := tbeta1 c bt fs xi).
    + simpl. exact (eq_sym Hin).
    + exact Hx.
  - simpl in Hin.
    destruct Hin as [Hin|Hin]; [|contradiction].
    apply child_desceq with (y := tbeta2 c bt fs xi).
    + simpl. exact (eq_sym Hin).
    + exact Hx.
  - simpl in Hin.
    destruct Hin as [Hin|Hin]; [|contradiction].
    rewrite <- Hin.
    destruct (alternate_choice_or trail (talt c1 c2 bt fs xi) c1 c2)
      as [Hchoice|Hchoice]; rewrite Hchoice.
    + apply child_desceq with (y := talt c1 c2 bt fs xi).
      * simpl. left. reflexivity.
      * exact Hx.
    + apply child_desceq with (y := talt c1 c2 bt fs xi).
      * simpl. right. reflexivity.
      * exact Hx.
  - simpl in Hin.
    apply (proj1 (jump_next_nodes_spec (x := tjump cs fs xi)
      Hx y (ltac:(simpl; trivial)))) in Hin.
    destruct Hin as [Hchild|Hvirtual].
    + apply (child_desceq y (y := tjump cs fs xi) (z := l_root Tl)).
      * exact Hchild.
      * exact Hx.
    + destruct Hvirtual as [c0 [Hc0 Hopt]].
      pose proof (virtual_target_opt_sound (x := tjump cs fs xi) Hx c0 Hopt)
        as [_ Hloop].
      destruct Hloop as [h [_ [_ [_ [Hyle _]]]]].
      exact Hyle.
Qed.

Lemma next_nodes_nodup :
  forall u,
    NoDup (next_nodes u).
Proof.
  intros [trail x Hx].
  destruct x.
  - simpl. constructor; [intros H; contradiction|constructor].
  - simpl. constructor; [intros H; contradiction|constructor].
  - simpl. constructor; [intros H; contradiction|constructor].
  - simpl. constructor; [intros H; contradiction|constructor].
  - simpl. apply NoDup_nodup.
Qed.

Lemma uconfig_ext :
  forall u v,
    u_trail u = u_trail v ->
    u_node u = u_node v ->
    u = v.
Proof.
  intros [trail1 node1 root1] [trail2 node2 root2] Htrail Hnode.
  simpl in Htrail, Hnode. subst trail2. subst node2.
  f_equal. apply proof_irrelevance.
Qed.

Fixpoint map_in
  {A B : Type}
  (l : list A)
  (f : forall x, In x l -> B)
  : list B :=
  match l as l0 return (forall x, In x l0 -> B) -> list B with
  | [] => fun _ => []
  | x :: xs => fun f0 =>
      f0 x (or_introl eq_refl) ::
      map_in xs (fun y Hy => f0 y (or_intror Hy))
  end f.

Lemma map_in_In_iff :
  forall (A B : Type) (l : list A)
    (f : forall x, In x l -> B) (z : B),
    In z (map_in l f) <->
    exists x (Hx : In x l), z = f x Hx.
Proof.
  intros A B l. induction l as [|x xs IH]; intros f z.
  - simpl. split.
    + contradiction.
    + intros [x [Hx _]]. contradiction.
  - simpl. split.
    + intros [Heq|Hin].
      * exists x, (or_introl eq_refl). exact (eq_sym Heq).
      * destruct (IH (fun y Hy => f y (or_intror Hy)) z) as [H _].
        destruct (H Hin) as [y [Hy Heq]].
        exists y, (or_intror Hy). exact Heq.
    + intros [y [Hy Heq]]. destruct Hy as [Heqxy|Hy].
      * subst y. left.
        exact (eq_sym Heq).
      * right. apply (proj2 (IH (fun y Hy => f y (or_intror Hy)) z)).
        exists y, Hy. exact Heq.
Qed.

Definition futr_list
  (u : uconfig) : list uconfig :=
  map_in
    (next_nodes u)
    (fun y Hy =>
      {| u_trail := u_trail u ++ [u_node u];
         u_node := y;
         u_in_root := next_node_in_root u y Hy |}).

Lemma psgu_iff_next_nodes :
  forall prev curr,
    psgu prev curr <->
    u_trail curr = u_trail prev ++ [u_node prev] /\
    In (u_node curr) (next_nodes prev).
Proof.
  intros prev curr. destruct prev as [trail x Hx].
  destruct curr as [trail' y Hy].
  destruct x as [c fs xi|c bt fs xi|c bt fs xi|c1 c2 bt fs xi|cs fs xi].
  - split.
    + intro H. destruct H as [Ht Hn Hj Ha]. split; [exact Ht|].
      simpl. specialize (Hn (fun H => H)).
      simpl in Hn. now left.
    + intros [Ht Hin]. constructor; simpl in *.
      * exact Ht.
      * intro Hdummy. simpl in Hin. destruct Hin as [Hin|Hin].
        -- exact (eq_sym Hin).
        -- contradiction.
      * intro H. contradiction.
      * intros c1' c2' bt' fs' phi' Heq. inversion Heq.
  - split.
    + intro H. destruct H as [Ht Hn Hj Ha]. split; [exact Ht|].
      simpl. specialize (Hn (fun H => H)). simpl in Hn. now left.
    + intros [Ht Hin]. constructor; simpl in *.
      * exact Ht.
      * intro Hdummy. simpl in Hin. destruct Hin as [Hin|Hin].
        -- exact (eq_sym Hin).
        -- contradiction.
      * intro H. contradiction.
      * intros c1' c2' bt' fs' phi' Heq. inversion Heq.
  - split.
    + intro H. destruct H as [Ht Hn Hj Ha]. split; [exact Ht|].
      simpl. specialize (Hn (fun H => H)). simpl in Hn. now left.
    + intros [Ht Hin]. constructor; simpl in *.
      * exact Ht.
      * intro Hdummy. simpl in Hin. destruct Hin as [Hin|Hin].
        -- exact (eq_sym Hin).
        -- contradiction.
      * intro H. contradiction.
      * intros c1' c2' bt' fs' phi' Heq. inversion Heq.
  - split.
    + intro H. destruct H as [Ht Hn Hj Ha]. split; [exact Ht|].
      simpl. specialize (Ha c1 c2 bt fs xi eq_refl).
      left. exact (eq_sym Ha).
    + intros [Ht Hin]. constructor; simpl in *.
      * exact Ht.
      * intro Hdummy. destruct Hin as [Hin|Hin].
        -- unfold is_child. simpl. rewrite <- Hin.
           exact (alternate_choice_or trail (talt c1 c2 bt fs xi) c1 c2).
        -- contradiction.
      * intro H. contradiction.
      * intros c1' c2' bt' fs' phi' Heq. inversion Heq.
        subst c1'; subst c2'; subst bt'; subst fs'; subst phi'.
        destruct Hin as [Hin|Hin]; [exact (eq_sym Hin)|contradiction].
  - split.
    + intro H. destruct H as [Ht Hn Hj Ha]. split; [exact Ht|].
      change (In y (jump_next_nodes (x := tjump cs fs xi) Hx)).
      apply (proj2 (jump_next_nodes_spec (x := tjump cs fs xi)
        Hx y (ltac:(simpl; trivial)))).
      apply Hj. simpl. trivial.
    + intros [Ht Hin]. constructor; simpl in *.
      * exact Ht.
      * intro H. contradiction.
      * intro H. change (In y (jump_next_nodes (x := tjump cs fs xi) Hx)) in Hin.
        apply (proj1 (jump_next_nodes_spec (x := tjump cs fs xi)
          Hx y (ltac:(simpl; trivial)))). exact Hin.
      * intros c1' c2' bt' fs' phi' Heq. inversion Heq.
Qed.

Lemma futr_list_in_iff :
  forall u v,
    In v (futr_list u) <->
    u_trail v = u_trail u ++ [u_node u] /\
    In (u_node v) (next_nodes u).
Proof.
  intros u v. unfold futr_list.
  rewrite (map_in_In_iff (next_nodes u)
    (fun y Hy =>
      {| u_trail := u_trail u ++ [u_node u];
         u_node := y;
         u_in_root := next_node_in_root u y Hy |}) v).
  split.
  - intros [y [Hy Heq]]. subst v. simpl. split; [reflexivity|exact Hy].
  - intros [Htrail Hnode].
    assert (Hv : v =
      {| u_trail := u_trail u ++ [u_node u];
         u_node := u_node v;
         u_in_root := next_node_in_root u (u_node v) Hnode |}).
    { apply uconfig_ext; simpl; [exact Htrail|reflexivity]. }
    exists (u_node v), Hnode. exact Hv.
Qed.

Lemma futr_list_spec :
  forall u v,
    In v (futr_list u) <-> psgu u v.
Proof.
  intros u v. rewrite futr_list_in_iff. exact (iff_sym (psgu_iff_next_nodes u v)).
Qed.

Lemma futr_list_nodup :
  forall u,
    NoDup (futr_list u).
Proof.
  intros u.
  assert (Hmap : forall (l : list ptree)
    (f : forall x, In x l -> uconfig),
    NoDup l ->
    (forall x Hx y Hy, f x Hx = f y Hy -> x = y) ->
    NoDup (map_in l f)).
  {
    intros l. induction l as [|x xs IH]; intros f Hnodup Hinj.
    - constructor.
    - simpl in Hnodup. inversion Hnodup as [| x0 xs0 Hnotin Hrest].
      constructor.
      + intro Htail. apply Hnotin. 
        destruct (proj1 (map_in_In_iff xs
          (fun y Hy => f y (or_intror Hy)) (f x (or_introl eq_refl))) Htail)
          as [y [Hy Heq]].
        apply Hinj in Heq. rewrite Heq. exact Hy.
      + apply IH; [exact Hrest|].
        intros x' Hx' y Hy' Heq. apply Hinj in Heq. exact Heq.
  }
  apply Hmap with (l := next_nodes u)
    (f := fun y Hy =>
      {| u_trail := u_trail u ++ [u_node u];
         u_node := y;
         u_in_root := next_node_in_root u y Hy |}).
  - apply next_nodes_nodup.
  - intros x Hx y Hy Heq. simpl in Heq. now inversion Heq.
Qed.

Definition futr_property
  (u : uconfig)
  (lfutr : list uconfig) : Prop :=
  NoDup lfutr /\
  forall v, In v lfutr <-> psgu u v.

Definition curr_lfutr
  (u : uconfig) : { lfutr : list uconfig | futr_property u lfutr }.
Proof.
  refine (exist _ (futr_list u) _).
  split.
  - apply futr_list_nodup.
  - apply futr_list_spec.
Defined.

Lemma curr_lfutr_value :
  forall u,
    proj1_sig (curr_lfutr u) = futr_list u.
Proof.
  intro u. reflexivity.
Qed.

(* old ctl

  Definition alternate_choice (p : list ptree) (x c1 c2 : ptree) :=
    if even (count_occ ptree_eqdec p x) then c1 else c2.
  
  Lemma alternate_choice_or (p : list ptree) (x c1 c2 : ptree) :
    alternate_choice p x c1 c2 = c1 \/
    alternate_choice p x c1 c2 = c2.
  Proof.
  unfold alternate_choice.
  destruct (even (count_occ ptree_eqdec p x));
  [now left | now right].
  Qed.

  Definition proj_ss [A : Type] [P : A -> Prop] [B : Prop]
  (x : {a : A | P a} + {B}) : option A :=
    match x with
    | inleft (exist _ a pa) => Some a
    | inright b             => None
    end. 

  

  Definition option_in {X : Type}
    (oa : option X) (oA : option (list X)) : Prop :=
  match oa, oA with
  | Some a, Some A => In a A
  | _, _ => False
  end.

  Definition option_list {X : Type} (oa : option (list X)) : list X :=
    match oa with
    | Some a => a
    | None => []
    end.
  
  Definition loop_targets_of (x : ptree) : list ptree :=
  option_list (proj_ss (l_looper Tl x)).

  Record psgu (prev curr : (list ptree) * ptree) : Prop :=
  { sgu_child      : ~ t_isjump (snd prev) -> is_child (snd curr)(snd prev);
    sgu_loop       : t_isjump (snd prev) -> is_child (snd curr) (snd prev) \/  In (snd curr) (option_list (proj_ss ((l_looper Tl) (snd prev))));
    sgu_trail_eq    : fst curr = fst prev ++ [snd prev];
    sgu_alt_choice : forall c1 c2 bt fs phi, snd prev = talt c1 c2 bt fs phi ->
      snd curr = alternate_choice (fst prev) (snd prev) c1 c2 ;
    sgu_alt_le_twice : forall c1 c2 bt fs phi, snd prev = talt c1 c2 bt fs phi ->
    In (talt c1 c2 bt fs phi) (fst prev) -> forall c3 c4 bt fs phi, (talt c3 c4 bt fs phi)<> (talt c1 c2 bt fs phi)-> 
    count_occ ptree_eqdec (fst prev) (talt c3 c4 bt fs phi) >= 2}.

  Record unode : Type :=
  {
    curr :(list ptree) * ptree;
    lfutr: list((list ptree) * ptree);
    sgu_all : forall u, In u lfutr <-> psgu curr u;
    lfutr_nodup : NoDup lfutr;
  }.

  Definition unode_ischild (u1 u2 : unode) : Prop :=
    psgu (curr u1) (curr u2).

  Lemma unode_child_in_futr : forall u1 u2, In (curr u2) (lfutr u1) <-> unode_ischild u1 u2.
  Proof.
    intros u1 u2.
    pose proof (sgu_all u1 (curr u2)) as Hsgu.
    unfold unode_ischild. 
    assumption.
  Qed.

Theorem finite_pred_list :forall (A : Type) (la : list A), forall P : A -> Prop,
      (forall a, P a -> In a la) -> exists la', forall a, P a <-> In a la'.
  Proof.
    intros A la. induction la as [| x xs IH].
  - intros P H. exists []. intros a. split.
    + intros HP. specialize (H a HP). contradiction.
    + intros Hin. contradiction.
  - intros P H. destruct (classic (P x)) as [Hpx|Hnpx].
    +   assert (Hrest :
        forall a,
          (P a /\ a <> x) ->
          In a xs).
      {
        intros a [HP Hneq].
        specialize (H a HP).
        simpl in H.
        destruct H as [Heq | Hin].
        - subst. contradiction.
        - exact Hin.
      }
      specialize
        (IH (fun a => P a /\ a <> x) Hrest).
      destruct IH as [l Hl].
      exists (x :: l).
      intros a.
      split.
      * intros HP.
        simpl.
        destruct (classic (a = x)) as [Heq | Hneq].
        -- left. subst. reflexivity.
        -- right.
           apply (proj1 (Hl a)).
           split; assumption.
      * intros Hin.
        simpl in Hin.
        destruct Hin as [Heq | Hin].
        -- subst.
           exact Hpx.
        -- apply (proj2 (Hl a)) in Hin.
           destruct Hin as [HP _].
           exact HP.
    +  assert (Hrest : forall a, P a -> In a xs).
      {
        intros a HP.
        specialize (H a HP).
        simpl in H.
        destruct H as [Heq | Hin].
        - subst.
          contradiction.
        - exact Hin.
      }
      specialize (IH P Hrest) as [la' IHla']. exists la'. assumption.
  Qed.

  Lemma alt_choice_in_list : forall (p : list ptree) (x c1 c2 : ptree),
    In (alternate_choice p x c1 c2) [c1; c2].
  Proof.
    intros p x c1 c2.
    unfold alternate_choice.
    destruct (even (count_occ ptree_eqdec p x)).
    - left. reflexivity.
    - right. simpl. left. reflexivity.
  Qed.

  Lemma snd_futr_in_list_futr_in : forall (curr : (list ptree) * ptree) (lp :list ptree), (forall ftr,
    psgu curr ftr -> In (snd ftr) lp) -> exists lfutr : list((list ptree) * ptree), forall ftr, psgu curr ftr -> In ftr lfutr.
  Proof.
    intros curr lp H. exists (map (fun x => (fst curr ++ [snd curr], x)) lp). intros ftr Hpsgu. 
    specialize (H ftr Hpsgu). destruct ftr as [p x]. simpl in *. subst. apply in_map_iff. exists x. split; try assumption. simpl.
    destruct Hpsgu as [H1 H2 H3tail]. simpl in *. subst. reflexivity.
  Qed.

  

  Lemma jump_futr_in_list : forall (curr : (list ptree) * ptree), 
  t_isjump (snd curr) -> exists lp : (list ptree), forall ftr, psgu curr ftr -> In (snd ftr) lp.
  Proof. 
    intros curr Hjump. destruct curr as [p x]. simpl in *. 
    destruct x as [c fs xi|c bt fs xi|c bt fs xi| c1 c2 bt fs xi|cs fs xi] eqn:Heqx; try contradiction.
    exists (cs ++ option_list (proj_ss ((l_looper Tl) (x)))). intros ftr Hpsgu. destruct ftr as [p' x']. simpl in *. subst.
    destruct Hpsgu as [H1 Hloop]. simpl in *. specialize (Hloop I). destruct (proj_ss (l_looper Tl (tjump cs fs xi))) as [A |] eqn:Hproj.
    - simpl in Hloop |- *.
      apply in_app_iff.
      exact Hloop.
    - simpl in Hloop |- *.
      apply in_app_iff.
      exact Hloop.
  Qed.
      


  Lemma futr_in_list_ex (curr: (list ptree) * ptree) : exists lfutr : list((list ptree) * ptree), forall ftr,
    psgu curr ftr -> In ftr lfutr.
  Proof.
    intros. destruct curr as [p x].
    destruct x as [c fs xi|c bt fs xi|c bt fs xi| c1 c2 bt fs xi|cs fs xi] eqn:Heqx.
    - exists [(p ++ [x], c)]. intros ftr u. destruct u as [H1 H2]. simpl in *. destruct H1 as [].
       subst. intro HF.  assumption. left. simpl in *. subst. destruct ftr as [p' x']. simpl in *. 
       subst. reflexivity.
    - exists [(p ++ [x], c)]. intros ftr u. destruct u as [H1 H2]. simpl in *. destruct H1 as [].
       subst. intro HF.  assumption. left. simpl in *. subst. destruct ftr as [p' x']. simpl in *. 
       subst. reflexivity.
    - exists [(p ++ [x], c)]. intros ftr u. destruct u as [H1 H2]. simpl in *. destruct H1 as [].
       subst. intro HF.  assumption. left. simpl in *. subst. destruct ftr as [p' x']. simpl in *. 
       subst. reflexivity.
    - assert (exists lp : (list ptree), forall ftr, psgu (p, x) ftr -> In (snd ftr) lp) as Hlp. { 
      exists [c1; c2]. intros ftr0 Hpsgu. destruct Hpsgu as [H1 H2 H3 Halt]. simpl in Halt. 
      specialize (Halt c1 c2 bt fs xi Heqx). rewrite Halt. apply alt_choice_in_list.
     } rewrite <- Heqx. destruct Hlp as [lp Hlp]. subst x.
      destruct (snd_futr_in_list_futr_in lp Hlp) as [lfutr Hlfutr].     
      exists lfutr. apply Hlfutr. 
    - assert (t_isjump (tjump cs fs xi)) as Hjump. { simpl. reflexivity. }
      destruct (jump_futr_in_list (p, tjump cs fs xi) Hjump) as [lp Hlp]. subst x.
      destruct (snd_futr_in_list_futr_in lp Hlp) as [lfutr Hlfutr].     
      exists lfutr. apply Hlfutr.
  Qed.
  
  Lemma futr_in_list_eq (curr: (list ptree) * ptree) : exists lfutr : list((list ptree) * ptree), forall ftr,
    In ftr lfutr <-> psgu curr ftr.
  Proof.
    destruct (futr_in_list_ex curr) as [lfutr Hlfutr].
   pose proof
  (finite_pred_list
     (A := (list ptree * ptree)%type) lfutr(fun ftr => psgu curr ftr) Hlfutr) as Hfinite.
     destruct Hfinite as [lfutr0 Hiff].
    exists lfutr0.
    intro ftr.
    specialize (Hiff ftr).
    tauto.
  Qed.
 Lemma futr_in_list_nodup (curr : list ptree * ptree) :
  exists lfutr : list (list ptree * ptree),
    NoDup lfutr /\
    forall ftr,
      In ftr lfutr <-> psgu curr ftr.
Proof.
  destruct (futr_in_list_eq curr) as [lfutr Hlfutr].
  assert (futr_eqdec : forall (ftr1 ftr2 : (list ptree) * ptree), {ftr1 = ftr2} + {ftr1 <> ftr2}).
  {
    intros [p1 x1] [p2 x2].
    destruct (ptree_eqdec x1 x2) as [Heq | Hneq].
    - subst. destruct (list_eq_dec ptree_eqdec p1 p2) as [Heq' | Hneq'].
      + subst. left. reflexivity.
      + right. intro Heq''. inversion Heq''. contradiction.
    - right. intro Heq''. inversion Heq''. contradiction.
  }
  exists (nodup futr_eqdec lfutr).
  split.
  - apply NoDup_nodup.
  - intro ftr.
    rewrite nodup_In.
    apply Hlfutr.
Qed.

  Definition futr_property (curr : list ptree * ptree)
  (lfutr : list (list ptree * ptree)) : Prop :=
  NoDup lfutr /\ forall u, In u lfutr <-> psgu curr u.

  Lemma futr_property_ex : forall curr, exists lfutr, futr_property curr lfutr.
  Proof.
    intros curr. destruct (futr_in_list_nodup curr) as [lfutr [Hnodup Hiff]].
    exists lfutr. split; assumption.
  Qed.

  *)

(* 10.14edit *)
(*
  Theorem unravel_ev_fulfilled :
    forall i phi psi u, In (unt phi psi) (t_G (snd (prev u))) ->
    exists v, k >= i /\ In psi (t_G (unravel k)).
*)

(*
  Record psgu (prev curr : (list ptree) * ptree) : Prop :=
  { sgu_child      : ~ t_isloop (snd prev) ->
      is_child (snd curr) (snd prev);
    sgu_loop       : t_isloop (snd prev) ->
      proj_ss ((l_looper Tl) (snd prev)) = Some (snd curr);
    sgu_trail_eq    : fst curr = fst prev ++ [snd prev];
    sgu_alt_choice : forall c1 c2 fs phi, snd prev = talt c1 c2 fs phi ->
      snd curr = alternate_choice (fst prev) (snd prev) c1 c2 }.
*)
(* 10.14edit *)
(*
  Definition return_succ_gen_unravel (prev : list ptree * ptree) :=
    {lu :list( (list ptree) * ptree) |forall u, In u lu <-> snd u <=/ l_root Tl /\ psgu prev u}.
  
  Definition succ_gen_unravel
    (prev : {u : (list ptree) * ptree | snd u <=/ l_root Tl}) :
    return_succ_gen_unravel (proj1_sig prev).
  Proof.
(*
  refine (
  let u := (proj1_sig prev) in let p := fst u in
  let x := snd u in let xlert := proj2_sig prev in
  match x as x' return x = x' -> return_succ_gen_unravel (proj1_sig prev) with
  | talpha c _ _   => fun Heqx => exist _ (p ++ [x], c) _
  | tbeta1 c _ _ _  => fun Heqx => exist _ (p ++ [x], c) _
  | tbeta2 c _ _ _  => fun Heqx => exist _ (p ++ [x], c) _
  | talt c1 c2 _ _  _=> fun Heqx =>
      exist _ (p ++ [x], alternate_choice p x c1 c2) _
  | tjump c _ _      => fun Heqx => exist _ (p ++ [x], c) _
  | tloop fs       => fun Heqx =>
      let lofx := l_looper Tl x in
      match lofx as lofx' return lofx = lofx' ->
      return_succ_gen_unravel (proj1_sig prev) with
      | inleft (exist _ c Hpl) => fun Heqlof =>
          exist _ (p ++ [x], c) _
      | inright Hctr => _
      end eq_refl
  end eq_refl
  ).
  all: try split; try (apply child_desceq with x; try assumption;
  rewrite Heqx; ((now left) || (now right) || reflexivity));
  try (simpl; destruct Hpl as [H H0]; destruct H; now left);
  try (exfalso; destruct Hctr;
    [contradiction | (contradict H; rewrite Heqx; apply I)]);
  try (constructor; simpl; fold u x; rewrite Heqx;
    try (tauto || contradiction || discriminate);
    intro; reflexivity).
  - destruct (alternate_choice_or p x c1 c2) as [Heq|Heq];
    rewrite Heq; apply child_desceq with x; try assumption;
    rewrite Heqx; [now left | now right].
  - constructor; simpl; fold u x; rewrite Heqx;
    try (tauto || contradiction || discriminate);
    rewrite <- Heqx.
    + intro. destruct (alternate_choice_or p x c1 c2) as [Heq|Heq];
      rewrite Heq; rewrite Heqx; [now left | now right].
    + intros c1' c2' fs phi Heq. rewrite Heqx in Heq.
      injection Heq. intros _ _ Heqc2 Heqc1.
      rewrite <- Heqc1, <- Heqc2. reflexivity.
  - constructor; simpl; fold u x; rewrite Heqx;
    try (tauto || contradiction || discriminate);
    try (simpl; tauto).
    intro H; clear H. rewrite <- Heqx. fold lofx. rewrite Heqlof.
    simpl. reflexivity.
*)
  Admitted.

  Lemma list_root_desceq : forall p , In p [([]:list ptree, (l_root Tl))] -> snd p <=/ l_root Tl.
  Proof.
  intros p H. destruct H as [H|H].
  - rewrite <- H. simpl. apply desceq_refl.
  - contradiction.
  Qed.

  Fixpoint gen_unravel (n : nat) :
    { u : (list ptree) * ptree | snd u <=/ l_root Tl} :=
  match n with
  | 0   => exist _ ([], (l_root Tl)) desceq_refl
  | S n => let sgu := succ_gen_unravel (gen_unravel n) in
      exist _ (proj1_sig sgu)  (proj2_sig sgu)
  end.

  Definition trail_unravel (n : nat) : list ptree :=
    fst (proj1_sig (gen_unravel n)).

  Definition unravel (n : nat) : ptree :=
    snd (proj1_sig (gen_unravel n)).

  Lemma unravel_desceq_rt :
    forall n, unravel n <=/ l_root Tl.
  Proof.
  intro n. unfold unravel.
  destruct (gen_unravel n) as [(p, x) xlert].
  simpl. assumption.
  Qed.

  Lemma unravel_child : forall [n],
    ~ t_isjump (unravel n) -> is_child (unravel (S n)) (unravel n).
  Proof.
  intros n Hnlp. unfold unravel at 1. simpl.
  destruct (succ_gen_unravel (gen_unravel n)) as [u [xlert pu]].
  simpl. apply (sgu_child pu Hnlp).
  Qed.

  Lemma unravel_loop : forall [n],
    t_isjump (unravel n) ->
    is_child (unravel (S n)) (unravel n) \/
      proj_ss (l_looper Tl (unravel n)) = Some (unravel (S n)).
  Proof.
  intro n. pose proof (eq_refl (unravel (S n))) as H.
  unfold unravel at 2 in H. simpl in H.
  destruct (succ_gen_unravel (gen_unravel n)) as [u [xlert pu]].
  simpl in H. rewrite H.
  pose proof (sgu_loop pu) as H0. fold (unravel n) in H0. simpl in H0.
  assumption.
  Qed.

  Lemma unravel_loop_target : forall [n],
    t_isjump (unravel n) -> is_child (unravel (S n)) (unravel n) \/
    loop_target (unravel n) (unravel (S n)) (l_root Tl).
  Proof.
  intros n H. apply unravel_loop in H.
  destruct (l_looper Tl (unravel n)) as [x|]; try discriminate.
  destruct x as [x px]. simpl in H.  destruct H as [Hisc | H]. left. assumption. injection H.
  intro Heqx. rewrite Heqx in px. right. assumption. destruct H as [Hisc| H].  left. assumption. 
  discriminate. 
  Qed.

  Lemma unravel_alt_choice : forall [n c1 c2 fs bt phi],
    unravel n = talt c1 c2 bt fs phi ->
    unravel (S n) = alternate_choice (trail_unravel n)
    (unravel n) c1 c2.
  Proof.
  intros n c1 c2 fs bt phi Hequn. unfold unravel at 1. simpl.
  destruct (succ_gen_unravel (gen_unravel n)) as [[p x] [xlert psgu]].
  simpl. pose proof (sgu_alt_choice psgu Hequn). assumption.
  Qed.

  Lemma trail_unravel_succ_eq : forall n,
    trail_unravel (S n) = trail_unravel n ++ [unravel n].
  Proof.
  intro n. unfold trail_unravel. simpl.
  destruct (succ_gen_unravel (gen_unravel n)) as [[p x] [xlert pu]].
  simpl. apply (sgu_trail_eq pu).
  Qed.

  Fixpoint unravel_from_ql (n r : nat) : list ptree :=
    match r with
    | 0    => []
    | S r' => unravel n :: unravel_from_ql (S n) r'
    end.
  
  Definition unravel_from_to (n m : nat) : list ptree :=
    unravel_from_ql n (m - n).
  
  Lemma unravel_from_to_eq_cons : forall n m, m > n ->
    unravel_from_to n m = unravel n :: unravel_from_to (S n) m.
  Proof.
  intros n m mgtn. unfold unravel_from_to at 1.
  destruct (m - n) as [|d] eqn:Heqmn; try lia.
  simpl. assert (d = m - (S n)) as Heqd. { lia. }
  rewrite Heqd. reflexivity.
  Qed.

  Lemma unravel_from_to_same : forall n, unravel_from_to n n = [].
  Proof.
  intro n. unfold unravel_from_to. rewrite Nat.sub_diag. reflexivity.
  Qed.

  Lemma unravel_from_to_succ_eq : forall n,
    unravel_from_to n (S n) = [unravel n].
  Proof.
  intro n. unfold unravel_from_to.
  rewrite Nat.sub_succ_l; try apply le_n.
  rewrite Nat.sub_diag. simpl. reflexivity.
  Qed.

  Lemma unravel_from_to_split : forall n k m, n <= k <= m ->
    unravel_from_to n m = unravel_from_to n k ++ unravel_from_to k m.
  Proof.
  intros n k m [nlek klem]. fold (k >= n) in nlek. revert k nlek m klem.
  apply (induction_from_rank n (fun x => forall m, x <= m ->
  unravel_from_to n m = unravel_from_to n x ++ unravel_from_to x m)).
  - intros m nlem. rewrite unravel_from_to_same. simpl. reflexivity.
  - intros k kgen IHk. intros m Sklem.
    rewrite (IHk (S k)); try lia.
    rewrite unravel_from_to_succ_eq.
    rewrite <- app_assoc. simpl.
    rewrite <- unravel_from_to_eq_cons; try lia.
    apply IHk. lia.
  Qed.

  Lemma unravel_from_to_eq_app : forall n m, m >= n ->
    unravel_from_to n (S m) = unravel_from_to n m ++ [unravel m].
  Proof.
  intros n m mgen.
  rewrite (@unravel_from_to_split n m (S m)); try lia.
  rewrite unravel_from_to_succ_eq. reflexivity.
  Qed.
  
  Lemma unravel_from_to_in_between : forall n m x,
    In x (unravel_from_to n m) -> exists k, n <= k < m /\ x = unravel k.
  Proof.
  assert (forall d n m x, d = m - n -> In x (unravel_from_ql n d) ->
  exists k : nat, n <= k < m /\ x = unravel k) as H.
  { induction d; try contradiction.
  intros n m x HeqSd Hx. simpl in Hx.
  destruct Hx as [Hx|Hx].
  - exists n. split; try lia. apply eq_sym. assumption.
  - destruct (IHd (S n) m x) as [k [Snkm Hk]];
    try (lia || assumption). exists k. split; [lia|assumption]. }
  intros n m x Hx. apply (H (m - n)); [reflexivity|assumption].
  Qed.

  Lemma unravel_from_to_between_in : forall n m k,
    n <= k < m -> In (unravel k) (unravel_from_to n m).
  Proof.
  intros n. assert (forall m, m >= n -> forall k, n <= k < m ->
  In (unravel k) (unravel_from_to n m)) as H.
  { apply (induction_from_rank n (fun m =>
  forall k, n <= k < m -> In (unravel k) (unravel_from_to n m))).
  - intro k. lia.
  - intros m mgen IHm k [nlek kltSm].
    rewrite unravel_from_to_eq_app; try assumption. apply in_app_iff.
    apply Arith_prebase.lt_n_Sm_le in kltSm.
    destruct (le_lt_eq_dec _ _ kltSm) as [klt|keqm].
    + left. apply IHm. exact (conj nlek klt).
    + right. left. rewrite keqm. reflexivity. }
  intros m k nkm. apply H; lia.
  Qed.

  Lemma trail_unravel_eq_app_from_to : forall m n, m >= n ->
    trail_unravel m = trail_unravel n ++ unravel_from_to n m.
  Proof.
  intros m n. revert m. apply induction_from_rank.
  - rewrite unravel_from_to_same, app_nil_r. reflexivity.
  - intros m mgen IHm. rewrite trail_unravel_succ_eq.
    rewrite unravel_from_to_eq_app; try assumption.
    rewrite IHm. rewrite app_assoc. reflexivity.
  Qed.


  Lemma proper_unravel :
    forall n, proper (unravel n).
  Proof.
  intro n. apply (l_desceq_proper gpt (unravel_desceq_rt n)).
  Qed.


  (* Infinite Occurrence *)

  Definition occ_inf [A : Type] (f : nat -> A) (x : A) :=
    forall n, exists m, m >= n /\ f m = x.
  
  Definition occ_inf_unr := occ_inf unravel.

  Lemma unravel_first_reocc : forall n, occ_inf_unr (unravel n) ->
    exists m, m > n /\ unravel m = unravel n /\
    forall k, n < k < m -> unravel k <> unravel n.
  Proof.
  intros n oiun.
  assert (forall p, p >= n ->
  (forall k, n < k <= p -> unravel k <> unravel n) \/
  (exists m, n < m <= p /\ unravel m = unravel n /\
    (forall k : nat, n < k < m -> unravel k <> unravel n))) as H.
  {
  apply (induction_from_rank n); try (left; lia).
  intros p pgen IHp. destruct IHp as [IHp|IHp].
  - destruct (ptree_eqdec (unravel (S p)) (unravel n))
    as [Heq|Hneq].
    + right. exists (S p). split; try lia.
      split; try assumption.
      intros k nkSp. apply IHp. lia.
    + left. intros k [nltk kleSp].
      destruct (le_lt_eq_dec _ _ kleSp) as [kltSp|keqSp].
      * apply IHp. lia.
      * rewrite keqSp. assumption.
  - right. destruct IHp as [m [nltlep Hm]].
    exists m. split; [lia|assumption].
  }
  destruct (oiun (S n)) as [p [pgeSn Hequp]].
  specialize (H p (Le.le_Sn_le_stt _ _ pgeSn)).
  destruct H as [H|H].
  - contradict Hequp. apply H. lia.
  - destruct H as [m [nltlep Hm]].
    exists m. split; try lia. assumption.
  Qed.

  (* Requires XM *)
  Lemma unravel_eve_all_occ_inf :
    exists n, forall m, m >= n -> occ_inf_unr (unravel m).
  Proof.
  destruct (list_specification (fun x => ~ occ_inf_unr x)
  (all_nodes (l_root Tl))) as [l Hl].
  assert (forall x, In x l -> exists n,
  forall m, m >= n -> unravel m <> x) as Hlwk.
  { intros x Hx. apply Hl in Hx. destruct Hx as [_ Hx].
  apply not_all_ex_not in Hx.
  setoid_rewrite not_ex_all_not_iff in Hx.
  setoid_rewrite not_and_or_iff in Hx.
  setoid_rewrite or_to_imply_iff in Hx.
  assumption. }
  destruct (map_exists _ _ Hlwk) as [l' Hl'].
  exists (list_max l'). intros m mgemax.
  apply NNPP. intro Hctr.
  assert (In (unravel m) l) as Huminl.
  { apply Hl. split; try assumption.
  apply desceq_in_all_nodes. apply unravel_desceq_rt. }
  destruct (Hl' _ Huminl) as [n [Hninl' Hn]].
  pose proof (eq_refl (unravel m)) as H. contradict H.
  apply Hn. apply Nat.le_trans with (list_max l');
  try assumption. apply list_max_ge_all. assumption.
  Qed.

  (* Requires XM *)
  Lemma unravel_ex_occ_inf : exists x, occ_inf_unr x.
  Proof.
  destruct unravel_eve_all_occ_inf as [n Hn].
  exists (unravel n). apply Hn. apply le_n.
  Qed.


  Lemma unravel_occ_inf_child :
    forall x y, occ_inf_unr x -> is_child y x -> occ_inf_unr y.
  Proof.
  intros x y oix Hch. destruct x as [c fs xi|c bt fs xi|c bt fs xi|
  c1 c2 bt fs xi|cs fs xi] eqn:Heqx; try (
  intro n; destruct (oix n) as [m [mgen Hequm]]; rewrite Hch;
  exists (S m); split; try lia; assert (~ t_isjump (unravel m))
  as nlpum; [(rewrite Hequm; tauto) |
  (pose proof (unravel_child nlpum) as H;
  rewrite Hequm in H; assumption)]); try contradiction.
  intro n. destruct (oix n) as [m [mgen urmeq]].
  pose proof (unravel_alt_choice urmeq) as HequSm.
  destruct Hch as [Hch|Hch].
  - unfold alternate_choice in HequSm.
    destruct (even (count_occ ptree_eqdec (trail_unravel m) (unravel m)))
    eqn:Heqeven.
    + exists (S m). split; try lia. rewrite HequSm, Hch. reflexivity.
    + rewrite <- urmeq in oix.
      destruct (unravel_first_reocc m oix) as [l [llt [urleq lnot]]].
      exists (S l). split; try lia.
      rewrite urmeq in urleq.
      pose proof (unravel_alt_choice urleq) as HequSl.
      unfold alternate_choice in HequSl.
      rewrite (@trail_unravel_eq_app_from_to l m) in HequSl; try lia.
      rewrite (unravel_from_to_eq_cons llt) in HequSl.
      rewrite count_occ_app in HequSl. simpl in HequSl.
      rewrite urleq, <- urmeq in HequSl.
      destruct (ptree_eqdec (unravel m) (unravel m));
      try contradiction.
      assert (count_occ ptree_eqdec (unravel_from_to (S m) l)
      (unravel m) = 0) as Hcoeq0.
      { apply count_occ_not_In. intro Hctr.
      apply unravel_from_to_in_between in Hctr.
      destruct Hctr as [k [Smkl urmequrk]]. apply eq_sym in urmequrk.
      contradict urmequrk. apply lnot. lia. }
      rewrite Hcoeq0 in HequSl.
      rewrite Nat.add_comm in HequSl.
      rewrite Nat.even_succ in HequSl.
      unfold Nat.odd in HequSl.
      rewrite Heqeven in HequSl.
      simpl in HequSl.
      rewrite HequSl, Hch. reflexivity.
  - unfold alternate_choice in HequSm.
    destruct (even (count_occ ptree_eqdec (trail_unravel m) (unravel m)))
    eqn:Heqeven.
    + rewrite <- urmeq in oix.
      destruct (unravel_first_reocc m oix) as [l [llt [urleq lnot]]].
      exists (S l). split; try lia.
      rewrite urmeq in urleq.
      pose proof (unravel_alt_choice urleq) as HequSl.
      unfold alternate_choice in HequSl.
      rewrite (@trail_unravel_eq_app_from_to l m) in HequSl; try lia.
      rewrite (unravel_from_to_eq_cons llt) in HequSl.
      rewrite count_occ_app in HequSl. simpl in HequSl.
      rewrite urleq, <- urmeq in HequSl.
      destruct (ptree_eqdec (unravel m) (unravel m));
      try contradiction.
      assert (count_occ ptree_eqdec (unravel_from_to (S m) l)
      (unravel m) = 0) as Hcoeq0.
      { apply count_occ_not_In. intro Hctr.
      apply unravel_from_to_in_between in Hctr.
      destruct Hctr as [k [Smkl urmequrk]]. apply eq_sym in urmequrk.
      contradict urmequrk. apply lnot. lia. }
      rewrite Hcoeq0 in HequSl.
      rewrite Nat.add_comm in HequSl.
      rewrite Nat.even_succ in HequSl.
      unfold Nat.odd in HequSl.
      rewrite Heqeven in HequSl.
      simpl in HequSl.
      rewrite HequSl, Hch. reflexivity.
    + exists (S m). split; try lia. rewrite HequSm, Hch. reflexivity.
  - unfold occ_inf_unr in *. intro n. destruct (oix n) as [m [mgen urmeq]].
    exists (S m). split; try lia. rewrite urmeq, Hch. reflexivity.
  Qed.

  Lemma unravel_same_succ : forall m n, ~ t_isalt (unravel m) ->
    unravel m = unravel n -> unravel (S m) = unravel (S n).
  Proof.
  intros m n nalt urmneq.
  destruct (unravel m) as [c fs xi|c fs xi|c fs xi|
  c1 c2 fs xi|c fs|fs] eqn:Hequrm.
  - assert (~ t_isloop (unravel m)) as nlpurm. { rewrite Hequrm. tauto. }
    assert (~ t_isloop (unravel n)) as nlpurn. { rewrite <- urmneq. tauto. }
    pose proof (unravel_child nlpurm) as Hchm.
    pose proof (unravel_child nlpurn) as Hchn.
    rewrite Hequrm in Hchm. rewrite <- urmneq in Hchn.
    rewrite Hchm, Hchn. reflexivity.
  - assert (~ t_isloop (unravel m)) as nlpurm. { rewrite Hequrm. tauto. }
    assert (~ t_isloop (unravel n)) as nlpurn. { rewrite <- urmneq. tauto. }
    pose proof (unravel_child nlpurm) as Hchm.
    pose proof (unravel_child nlpurn) as Hchn.
    rewrite Hequrm in Hchm. rewrite <- urmneq in Hchn.
    rewrite Hchm, Hchn. reflexivity.
  - assert (~ t_isloop (unravel m)) as nlpurm. { rewrite Hequrm. tauto. }
    assert (~ t_isloop (unravel n)) as nlpurn. { rewrite <- urmneq. tauto. }
    pose proof (unravel_child nlpurm) as Hchm.
    pose proof (unravel_child nlpurn) as Hchn.
    rewrite Hequrm in Hchm. rewrite <- urmneq in Hchn.
    rewrite Hchm, Hchn. reflexivity.
  - contradict nalt. apply I.
  - assert (~ t_isloop (unravel m)) as nlpurm. { rewrite Hequrm. tauto. }
    assert (~ t_isloop (unravel n)) as nlpurn. { rewrite <- urmneq. tauto. }
    pose proof (unravel_child nlpurm) as Hchm.
    pose proof (unravel_child nlpurn) as Hchn.
    rewrite Hequrm in Hchm. rewrite <- urmneq in Hchn.
    rewrite Hchm, Hchn. reflexivity.
  - assert (t_isloop (unravel m)) as lpurm. { rewrite Hequrm. exact I. }
    assert (t_isloop (unravel n)) as lpurn. { rewrite <- urmneq. exact I. }
    pose proof (unravel_loop lpurm) as Heqm.
    pose proof (unravel_loop lpurn) as Heqn.
    rewrite Hequrm, urmneq in Heqm. rewrite Heqm in Heqn. injection Heqn. tauto.
  Qed.

  Lemma unravel_occ_inf_loop :
    forall x, occ_inf_unr x -> t_isloop x ->
    exists y, (proj_ss (l_looper Tl x) = Some y) /\ occ_inf_unr y.
  Proof.
  intros x oix Hlpx. destruct x as [| | | | |fs]; try contradiction.
  destruct (oix 0) as [n [nge0 urneq]].
  exists (unravel (S n)). split.
  - rewrite <- urneq. apply (@unravel_loop n). rewrite urneq. apply I.
  - intro m. destruct (oix m) as [k [kgem urkeq]].
    exists (S k). split; try lia.
    apply unravel_same_succ.
    + rewrite urkeq. simpl. tauto.
    + rewrite urneq, urkeq. reflexivity.
  Qed.

  Lemma isloop_dec : forall x, {t_isloop x} + {~ t_isloop x}.
  Proof.
  intro x. destruct x; simpl;
  ((now left) || (now right)).
  Qed.

  Lemma unravel_root_not_occ_inf : ~ occ_inf_unr (l_root Tl).
  Proof.
  assert (forall n, n >= 1 -> unravel n <> l_root Tl) as H.
  { intros n nge1. apply not_eq_sym.
  destruct n as [|n]; try lia.
  destruct (isloop_dec (unravel n)) as [Hlp|Hnlp].
  - apply desc_not_eq. apply (unravel_loop_target Hlp).
  - apply desc_not_eq. 
    apply desc_desceq_desc with (unravel n).
    + left. apply (unravel_child Hnlp).
    + apply unravel_desceq_rt. }
  intro oirt. destruct (oirt 1) as [n [nge1 Hctr]].
  contradict Hctr. apply H. assumption.
  Qed.

  Lemma unravel_occ_inf_desc_rt :
    forall x, occ_inf_unr x -> x </ (l_root Tl).
  Proof.
  intros x oix. destruct (oix 0) as [n [_ Hequn]].
  rewrite <- Hequn.
  destruct (unravel_desceq_rt n) as [|Heq]; try assumption.
  contradict oix. rewrite <- Hequn, Heq.
  apply unravel_root_not_occ_inf.
  Qed.

  Lemma unravel_occ_inf_proper :
    forall x, occ_inf_unr x -> proper x.
  Proof.
  intros x oix.
  apply ((proj2 gpt) _ (unravel_occ_inf_desc_rt oix)).
  Qed.

  Lemma proj_looper_loop_target : forall x y,
    proj_ss (l_looper Tl x) = Some y ->
    loop_target x y (l_root Tl).
  Proof.
  intros x y H.
  destruct (l_looper Tl x) as [y'|Hctr]; try discriminate.
  destruct y' as [y' ply]. simpl in H.
  injection H. intro Heqy. rewrite Heqy in ply.
  assumption.
  Qed.

  (* Requires XM *)
  Lemma unravel_occ_inf_anc :
    exists x, occ_inf_unr x /\ t_c x = true /\
    forall y, (occ_inf_unr y /\ t_c y = true) -> t_d x <= t_d y.
  Proof.
  destruct (list_specification (fun x => occ_inf_unr x /\
  t_c x = true) (all_nodes (l_root Tl))) as [l Hl].
  destruct (@list_min_ex (map t_d l)) as [d [Hdin Hdeq]].
  - assert (forall x, occ_inf_unr x -> exists y,
    occ_inf_unr y /\ t_c y = true) as Htrav.
    { induction x as [c IHc fs xi|c IHc fs xi|c IHc fs xi
    |c1 IHc1 c2 IHc2 fs xi|c IHc fs|fs].
    - set (x := talpha c fs xi). intro H. apply IHc.
      apply unravel_occ_inf_child with x;
        try reflexivity; try assumption.
    - set (x := tbeta1 c fs xi). intro H. apply IHc.
      apply unravel_occ_inf_child with x;
        try reflexivity; try assumption.
    - set (x := tbeta2 c fs xi). intro H. apply IHc.
      apply unravel_occ_inf_child with x;
        try reflexivity; try assumption.
    - set (x := talt c1 c2 fs xi). intro H. apply IHc1.
      apply unravel_occ_inf_child with x;
       try (left; reflexivity); try assumption.
    - set (x := tjump c fs). intro H. apply IHc.
      apply unravel_occ_inf_child with x;
        try reflexivity; try assumption.
    - set (x := tloop fs). intro H.
      destruct (@unravel_occ_inf_loop x H I) as [y [ply oiy]].
      apply proj_looper_loop_target in ply.
      destruct ply as [_ [_ [coy _]]].
      exists y. split; assumption.
      }
    destruct unravel_ex_occ_inf as [x0 oix0].
    destruct (Htrav x0 oix0) as [x [oix cox]].
    intro Hctr. apply map_eq_nil in Hctr.
    fold (In x []). rewrite <- Hctr. apply Hl.
    split; try (split; assumption).
    apply desceq_in_all_nodes. left.
    apply unravel_occ_inf_desc_rt. assumption.
  - apply in_map_iff in Hdin. destruct Hdin as [x [Hdxeq Hxin]].
    exists x. destruct (proj1 (Hl x) Hxin) as [_ [oix cox]].
    repeat (split; try assumption).
    intros y [oiy coy]. rewrite Hdxeq, Hdeq.
    apply list_min_le_all. apply in_map_iff.
    exists y. split; try reflexivity.
    apply Hl. split; try (split; assumption).
    apply desceq_in_all_nodes. left.
    apply unravel_occ_inf_desc_rt. assumption.
  Qed.


  Lemma unful_persist :
    forall i phi psi, In (unt phi psi) (t_G (unravel i)) ->
    (forall j, j >= i -> ~ In psi (t_G (unravel j))) ->
    forall j, j >= i -> (In (unt phi psi) (t_G (unravel j)) \/
    In (and phi (next (unt phi psi))) (t_G (unravel j)) \/
    In (next (unt phi psi)) (t_G (unravel j))).
  Proof.
  intros i phi psi Hin Hnful. apply induction_from_rank;
  try now left. intros j jgei IHj.
  pose proof (proper_unravel j) as px.
  remember (unravel j) as x eqn:Hequj. apply eq_sym in Hequj.
  tree_dest_with_eqns x; try rename phi0 into xi; simpl in Hprin; try clear Heqset.
  - pose proof (False_ind _ : ~ t_isloop (talpha c fs xi)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. rewrite Hch.
    destruct IHj as [IHj|[IHj|IHj]].
    + left. unfold t_G. rewrite Heqsec.
      simpl. right. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
    + destruct (nnf_eqdec (and phi (next (unt phi psi))) xi)
      as [Heq|Hneq].
      * right. right. unfold t_G. rewrite Heqsec. simpl.
        right. left. rewrite <- Heq. simpl. reflexivity.
      * right. left. unfold t_G. rewrite Heqsec. simpl.
        right. right. fold (t_G x).
        apply in_in_remove; assumption.
    + right. right. unfold t_G. rewrite Heqsec.
      simpl. right. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
  - pose proof (False_ind _ : ~ t_isloop (tbeta1 c fs xi)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. rewrite Hch.
    destruct IHj as [IHj|[IHj|IHj]].
    + destruct (nnf_eqdec (unt phi psi) xi)
      as [Heq|Hneq].
      * pose proof (Hnful _ (Nat.le_le_succ_r _ _ jgei)) as H.
        contradict H. rewrite Hch.
        unfold t_G. rewrite Heqsec. simpl. left. rewrite <- Heq.
        simpl. reflexivity.
      * left. unfold t_G. rewrite Heqsec. simpl.
        right. fold (t_G x).
        apply in_in_remove; assumption.
    + right. left. unfold t_G. rewrite Heqsec.
      simpl. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
    + right. right. unfold t_G. rewrite Heqsec.
      simpl. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
  - pose proof (False_ind _ : ~ t_isloop (tbeta2 c fs xi)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. rewrite Hch.
    destruct IHj as [IHj|[IHj|IHj]].
    + destruct (nnf_eqdec (unt phi psi) xi)
      as [Heq|Hneq].
      * right. left. unfold t_G. rewrite Heqsec.
        simpl. left. rewrite <- Heq. simpl. reflexivity.
      * left. unfold t_G. rewrite Heqsec. simpl.
        right. fold (t_G x).
        apply in_in_remove; assumption.
    + right. left. unfold t_G. rewrite Heqsec.
      simpl. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
    + right. right. unfold t_G. rewrite Heqsec.
      simpl. right. fold (t_G x).
      apply in_in_remove; try assumption.
      intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
  - pose proof (False_ind _ : ~ t_isloop (talt c1 c2 fs xi)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. destruct Hch as [Hch|Hch].
    + rewrite Hch. destruct IHj as [IHj|[IHj|IHj]].
      * destruct (nnf_eqdec (unt phi psi) xi)
        as [Heq|Hneq].
      -- pose proof (Hnful _ (Nat.le_le_succ_r _ _ jgei)) as H.
          contradict H. rewrite Hch.
          unfold t_G. rewrite Heqsec1. simpl. left.
          rewrite <- Heq. simpl. reflexivity.
      -- left. unfold t_G. rewrite Heqsec1. simpl.
          right. fold (t_G x).
          apply in_in_remove; assumption.
      * right. left. unfold t_G. rewrite Heqsec1.
        simpl. right. fold (t_G x).
        apply in_in_remove; try assumption.
        intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
      * right. right. unfold t_G. rewrite Heqsec1.
        simpl. right. fold (t_G x).
        apply in_in_remove; try assumption.
        intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
    + rewrite Hch. destruct IHj as [IHj|[IHj|IHj]].
      * destruct (nnf_eqdec (unt phi psi) xi)
        as [Heq|Hneq].
      -- right. left. unfold t_G. rewrite Heqsec2.
          simpl. left. rewrite <- Heq.
          simpl. reflexivity.
      -- left. unfold t_G. rewrite Heqsec2. simpl.
          right. fold (t_G x).
          apply in_in_remove; assumption.
      * right. left. unfold t_G. rewrite Heqsec2.
        simpl. right. fold (t_G x).
        apply in_in_remove; try assumption.
        intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
      * right. right. unfold t_G. rewrite Heqsec2.
        simpl. right. fold (t_G x).
        apply in_in_remove; try assumption.
        intro Hctr. contradict (eq_ind_r _ Hprin Hctr).
  - pose proof (False_ind _ : ~ t_isloop (tjump c fs)) as Hnlpuj.
    rewrite <- Hequj in Hnlpuj.
    pose proof (unravel_child Hnlpuj) as Hch.
    rewrite Hequj in Hch. rewrite Hch.
    destruct IHj as [IHj|[IHj|IHj]].
    + apply (sc_no_beta (state_has_sc px I)) in IHj.
      contradict IHj. exact I.
    + apply (sc_no_alpha (state_has_sc px I)) in IHj.
      contradict IHj. exact I.
    + left. unfold t_G. rewrite Heqsec. simpl.
      fold (t_G x). apply in_next_in_unnext.
      assumption.
  - pose proof (I : t_isloop (tloop fs)) as Hlpuj.
    rewrite <- Hequj in Hlpuj.
    destruct (unravel_loop_target Hlpuj) as [_ [_ [_ Heqset]]].
    destruct IHj as [IHj|[IHj|IHj]].
    + apply (sc_no_beta (state_has_sc px I)) in IHj.
      contradict IHj. exact I.
    + apply (sc_no_alpha (state_has_sc px I)) in IHj.
      contradict IHj. exact I.
    + left. apply (eqset_in_iff Heqset).
      apply in_next_in_unnext. rewrite Hequj.
      assumption.
  Qed.

  Corollary unful_persist_in_state :
    forall i phi psi, In (unt phi psi) (t_G (unravel i)) ->
    (forall j, j >= i -> ~ In psi (t_G (unravel j))) ->
    forall j, j >= i -> t_isstate (unravel j) ->
    In (next (unt phi psi)) (t_G (unravel j)).
  Proof.
  intros i phi psi Hin Hnful j jgei stx.
  set (x := unravel j) in *.
  pose proof (proper_unravel j) as px.
  destruct (unful_persist _ _ Hin Hnful jgei) as [H|[H|H]].
  - apply (sc_no_beta (state_has_sc px stx)) in H.
    contradict H. exact I.
  - apply (sc_no_alpha (state_has_sc px stx)) in H.
    contradict H. exact I.
  - assumption.
  Qed.

  (* Requires XM *)
  (* This is the main proof of soundness,
  inspired by Florian Widmann's PhD *)
  Theorem unravel_ev_fulfilled :
    forall i phi psi, In (unt phi psi) (t_G (unravel i)) ->
    exists k, k >= i /\ In psi (t_G (unravel k)).
  Proof.
  intros i phi psi Hin. apply not_all_not_ex. intro Hnful.
  setoid_rewrite not_and_or_iff in Hnful.
  setoid_rewrite or_to_imply_iff in Hnful.
  pose proof (unful_persist_in_state _ _ Hin Hnful) as Hstate.
  destruct unravel_occ_inf_anc as [xh [oixh [coxh dxhle]]].
  assert (forall x, occ_inf_unr x ->
  In (unt phi psi) (t_uev x) /\ t_lp x >= t_d xh) as H.
  { intros x oix. pose proof (unravel_occ_inf_proper oix) as px.
    tree_ind_with_eqns x; try rename phi0 into xi;
      try (pose proof (unravel_occ_inf_child c oix eq_refl) as oic;
           pose proof (unravel_occ_inf_proper oic) as pc;
           specialize (IHc oic pc));
      try (pose proof (unravel_occ_inf_child c1 oix (or_introl eq_refl)) as oic1;
           pose proof (unravel_occ_inf_proper oic1) as pc1;
           specialize (IHc1 oic1 pc1));
      try (pose proof (unravel_occ_inf_child c2 oix (or_intror eq_refl)) as oic2;
           pose proof (unravel_occ_inf_proper oic2) as pc2;
           specialize (IHc2 oic2 pc2)).
  - destruct IHc as [Hinuevc Hlpcge].
    rewrite Hequev, Heqlp. tauto.
  - destruct IHc as [Hinuevc Hlpcge].
    assert (unt phi psi <> xi) as Hneqxi.
    { intro Hctr. destruct (oic i) as [j [jgei Hequj]].
    pose proof (Hnful j jgei) as H. contradict H.
    rewrite Hequj. unfold t_G. rewrite Heqsec. simpl. rewrite <- Hctr. now left. }
    rewrite Hequev, Heqlp. split.
    + apply (in_in_remove nnf_eqdec _ Hneqxi Hinuevc).
    + assumption.
  - destruct IHc as [Hinuevc Hlpcge].
    rewrite Hequev, Heqlp. tauto.
  - destruct IHc1 as [Hinuevc1 Hlpc1ge].
    destruct IHc2 as [Hinuevc2 Hlpc2ge].
    assert (unt phi psi <> xi) as Hneqxi.
    { intro Hctr. destruct (oic1 i) as [j [jgei Hequj]].
    pose proof (Hnful j jgei) as H. contradict H.
    rewrite Hequj. unfold t_G. rewrite Heqsec1. simpl.  rewrite <- Hctr. now left. }
    split.
    + rewrite Hequev. apply set_inter_intro.
      * apply (in_in_remove nnf_eqdec _ Hneqxi Hinuevc1).
      * assumption.
    + rewrite Heqlp. apply Nat.min_glb; assumption.
  - destruct IHc as [Hinuevc Hlpcge].
    rewrite Hequev, Heqlp. split; try assumption.
  - destruct (unravel_occ_inf_loop oix I) as [c [plc oic]].
    apply proj_looper_loop_target in plc.
    destruct plc as [_ [Heqdc [coc _]]].
    pose proof (dxhle c (conj oic coc)) as Hdcge.
    rewrite Hequev, <- Heqdc. split; try assumption.
    apply unt_in_get_unts. apply in_next_in_unnext.
    destruct (oix i) as [j [jgei Hequj]].
    rewrite <- Hequj. apply Hstate; try assumption.
    rewrite Hequj. exact I. }
  specialize (H xh oixh).
  pose proof (no_unful_case (proj1 gpt)
  (unravel_occ_inf_desc_rt oixh) coxh) as H0.
  destruct H0 as [H0|H0].
  - fold (In (unt phi psi) []). rewrite <- H0. tauto.
  - lia.
  Qed.
*)

End Unravelling.
