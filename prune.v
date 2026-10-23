Require Import ptree.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Inductive open_reachable (root : ptree) : ptree -> Prop :=
| open_reachable_root :
    t_mrk root = false ->
    open_reachable root root

| open_reachable_step :
    forall parent child,
      open_reachable root parent ->
      is_child child parent ->
      t_mrk child = false ->
      open_reachable root child.

Definition valid_jump_node (root j : ptree) : Prop :=
  open_reachable root j /\ t_isjump j.

Lemma open_reachable_unmarked :
  forall root x,
    open_reachable root x ->
    t_mrk x = false.
Proof.
  intros root x H.
  induction H; assumption.
Qed.

Lemma open_reachable_desceq :
  forall root x,
    open_reachable root x ->
    x <=/ root.
Proof.
  intros root x H.
  induction H.
  - apply desceq_refl.
  - eapply child_desceq; eauto.
Qed.

Lemma valid_jump_node_isjump :
  forall root j,
    valid_jump_node root j ->
    t_isjump j.
Proof.
  intros root j [_ Hj].
  exact Hj.
Qed.

Lemma valid_jump_node_unmarked :
  forall root j,
    valid_jump_node root j ->
    t_mrk j = false.
Proof.
  intros root j [Hreach _].
  now apply open_reachable_unmarked in Hreach.
Qed.


  Fixpoint valid_jump_nodes (x : ptree) : list ptree :=
    if t_mrk x then
      []
    else
      match x with
      | talpha c _ _ =>
          valid_jump_nodes c

      | tbeta c1 c2 _ _ _ =>
          valid_jump_nodes c1 ++ valid_jump_nodes c2

      | tjump cs _ _ =>
          x ::
          ((fix valid_jump_nodes_list
                (cs : list ptree) : list ptree :=
              match cs with
              | [] => []
              | c :: cs' =>
                  valid_jump_nodes c ++
                  valid_jump_nodes_list cs'
              end) cs)
      end.

Theorem valid_jump_nodes_spec : forall root j,
    In j (valid_jump_nodes root) <->
    valid_jump_node root j.
  Proof.
    (* TODO *)
  Abort.