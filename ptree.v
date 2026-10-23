Require Import utils.
Require Import nnf.
Require Import closure.
Require Import semantics.
Require Import seqt.

Require Import Bool.
Require Import List.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Relations.
Require Import Lia.

Set Implicit Arguments.


(* ptree stands for "pruned tree" *)
Inductive beta_type :=
  | beta_or
  | beta_eu
  | beta_au.

Inductive ptree :=
  | talpha : ptree -> full_seqt -> nnf -> ptree
  | tbeta1 : ptree -> beta_type -> full_seqt -> nnf -> ptree
  | tbeta2 : ptree -> beta_type -> full_seqt -> nnf -> ptree
  | talt   : ptree -> ptree -> beta_type -> full_seqt -> nnf -> ptree
  | tjump  : list ptree -> full_seqt -> nnf -> ptree.

Definition beta_type_eqdec (x y : beta_type) : {x = y} + {x <> y}.
Proof. decide equality. Defined.

Definition df_t : ptree := tjump [] df_fseqt df_nnf.

Definition t_fseqt (x : ptree) : full_seqt :=
  match x with
  | talpha _ fs _ => fs
  | tbeta1 _ _ fs _  => fs
  | tbeta2 _ _  fs _ => fs
  | talt _ _ _  fs _ => fs
  | tjump _ fs _   => fs
  end.

Definition t_dose (t : ptree) := fst (t_fseqt t).
Definition t_upse (t : ptree) := snd (t_fseqt t).

Definition t_G (t : ptree) := s_G (t_dose t).
Definition t_H (t : ptree) := s_H (t_dose t).
Definition t_R (t : ptree) := s_R (t_dose t).

Definition t_uev (t : ptree) := s_uev (t_upse t).
Definition t_mrk  (t : ptree) := s_mrk (t_upse t).


Definition t_isstate (t : ptree) : Prop :=
  match t with
  | tjump _ _ _  => True
  | _         => False
  end.

Definition t_isalpha (t : ptree) :=
  match t with
  | talpha _ _ _ => True
  | _            => False
  end.

Definition t_isbeta (t : ptree) : Prop :=
  match t with
  | tbeta1 _ _ _ _  => True
  | tbeta2 _ _ _ _ => True
  | talt _ _ _ _ _ => True
  | _            => False
  end.

Definition t_isbeta_or (t : ptree) : Prop :=
  match t with
  | tbeta1 _ beta_or _ _  => True
  | tbeta2 _ beta_or _ _ => True
  | talt _ _ beta_or _ _ => True
  | _            => False
  end.

Definition t_isbeta_au (t : ptree) : Prop :=
  match t with
  | tbeta1 _ beta_au _ _  => True
  | tbeta2 _ beta_au _ _ => True
  | talt _ _ beta_au _ _ => True
  | _            => False
  end.

  Definition t_isbeta_eu (t : ptree) : Prop :=
  match t with
  | tbeta1 _ beta_eu _ _  => True
  | tbeta2 _ beta_eu _ _ => True
  | talt _ _ beta_eu _ _ => True
  | _            => False
  end.

Definition t_isjump (t : ptree) : Prop :=
  match t with
  | tjump _ _ _  => True
  | _         => False
  end.

Definition t_prinform (t : ptree) : option nnf :=
  match t with
  | talpha _ _ phi => Some phi
  | tbeta1 _ _ _ phi => Some phi
  | tbeta2 _ _ _ phi => Some phi
  | talt _ _ _ _ phi => Some phi  
  | tjump _ _ phi       => Some phi
  end.


Fixpoint ptree_eqdec (x y : ptree) : {x = y} + {x <> y}.
Proof.
decide equality;
(apply nnf_eqdec || apply full_seqt_eqdec|| decide equality; try apply nnf_eqdec;
    try apply full_seqt_eqdec;
    try (apply list_eq_dec; apply ptree_eqdec)).
Defined.

Definition t_isalpha_dec (x : ptree) :
  {t_isalpha x} + {~ t_isalpha x}.
Proof. destruct x; ((now left) || (now right)). Defined.

Definition t_isbeta_dec (x : ptree) :
  {t_isbeta x} + {~ t_isbeta x}.
Proof. destruct x; ((now left) || (now right)). Defined.

Definition t_isstate_dec (x : ptree) :
  {t_isstate x} + {~ t_isstate x}.
Proof. destruct x; ((now left) || (now right)). Defined.

Definition option_eqdec [A : Type]
  (A_eqdec : forall (x y : A), {x = y} + {x <> y}) :
  forall (x y : option A), {x = y} + {x <> y}.
Proof. decide equality. Defined.


(* Descendent Relation *)

Definition is_child (x y : ptree) : Prop :=
  match y with
  | talpha c _ _   => x = c
  | tbeta1 c _ _ _ => x = c
  | tbeta2 c _ _ _ => x = c
  | talt c1 c2 _ _ _ => x = c1 \/ x = c2
  | tjump c _ _     => In x c 
  end.

Definition desc := clos_trans _ is_child.
Definition desceq (x y : ptree) := desc x y \/ x = y.


Reserved Notation "x <=/ y" (at level 70, no associativity).
Reserved Notation "x </ y" (at level 70, no associativity).

Reserved Notation "x <=/ y <=/ z" (at level 70, y at next level).
Reserved Notation "x <=/ y </ z" (at level 70, y at next level).
Reserved Notation "x </ y </ z" (at level 70, y at next level).
Reserved Notation "x </ y <=/ z" (at level 70, y at next level).

Infix "</"  := desc.
Infix "<=/" := desceq.

Notation "x <=/ y <=/ z" := (x <=/ y /\ y <=/ z).
Notation "x <=/ y </ z" := (x <=/ y /\ y </ z).
Notation "x </ y </ z" := (x </ y /\ y </ z).
Notation "x </ y <=/ z" := (x </ y /\ y <=/ z).

Theorem desceq_refl : forall {x}, x <=/ x.
Proof. intro x. right. reflexivity. Qed.

Lemma desceq_desc_desc [x y z] : x <=/ y -> y </ z -> x </ z.
Proof.
intros H H0. destruct H as [H|H].
- right with y; assumption.
- rewrite H. assumption.
Qed.

Lemma desc_desceq_desc [x y z] : x </ y -> y <=/ z -> x </ z.
Proof.
intros H H0. destruct H0 as [H0|H0].
- right with y; assumption.
- rewrite <- H0. assumption.
Qed.

Lemma child_desceq : forall x y z,
  is_child x y -> y <=/ z -> x <=/ z.
Proof.
intros x y z Hch ylez. left.
apply desc_desceq_desc with y; try assumption.
left. assumption.
Qed.

Lemma desceq_trans : forall x y z, x <=/ y -> y <=/ z -> x <=/ z.
Proof.
intros x y z xley ylez. destruct ylez as [yltz|yeqz].
- left. apply desceq_desc_desc with y; assumption.
- rewrite <- yeqz. assumption.
Qed.

Fixpoint tree_size (t : ptree) : nat :=
  match t with
  | talpha c _ _ => S (tree_size c)
  | tbeta1 c _ _ _ => S (tree_size c)
  | tbeta2 c _ _ _ => S (tree_size c)
  | talt c1 c2 _ _ _ => S (tree_size c1 + tree_size c2)
  | tjump cs _ _ =>
      S
        ((fix tree_size_list (cs : list ptree) : nat :=
            match cs with
            | [] => 0
            | c :: cs' => tree_size c + tree_size_list cs'
            end) cs)
  end.

Lemma child_lt_tree_size [x y] : is_child y x -> tree_size y < tree_size x.
Proof.
intro H. destruct x; try ((simpl in H; rewrite H; simpl; lia)||contradiction).
simpl in H. destruct H; simpl in H; rewrite H; simpl; lia.
simpl in H. induction l as [| a l IH].
- inversion H.
- simpl in H. destruct H as [Hy | Hy].
  + subst. simpl. lia.
  + simpl. specialize (IH Hy).
    simpl in IH. lia.
Qed.

Theorem desc_lt_tree_size [x y] : y </ x -> tree_size y < tree_size x.
Proof.
intro yltx. apply clos_trans_tn1 in yltx. induction yltx.
- apply (child_lt_tree_size H).
- apply child_lt_tree_size in H. lia.
Qed.

Theorem desc_not_eq [x y] : y </ x -> x <> y.
Proof.
intros H H0. apply desc_lt_tree_size in H. rewrite H0 in H. lia.
Qed.

Lemma not_desc_child_desc [x z] : z </ x ->
  (forall y, is_child y x -> ~ z </ y) -> is_child z x.
Proof.
intros zltx ally. apply clos_trans_tn1 in zltx.
inversion zltx; try assumption. apply clos_tn1_trans in H0.
contradict H0. apply ally. assumption.
Qed.

Definition desc_dec : forall z x, {z </ x} + {~ z </ x}.
Proof.
fix F 2.
intros z x. revert z. induction x as [c IHc fs phi| c IHc fs phi| c IHc fs phi| c1 IHc1 c2 IHc2 fs phi|cs fs phi];
try (
intro z; destruct (IHc z) as [zltc|nzltc];
  [left; right with c; try assumption; left; simpl; reflexivity|
  destruct (ptree_eqdec z c) as [Heq|Hneq];
    [left; rewrite Heq; left; simpl; reflexivity|
    right; intro Hctr; apply clos_trans_tn1 in Hctr; inversion Hctr;
      [simpl in H; contradiction|
      simpl in H; rewrite H in H0;
        apply clos_tn1_trans in H0; contradiction]]]).
- intro z. destruct (IHc1 z) as [zltc1|nzltc1].
  + left. right with c1; try assumption. left. simpl. now left.
  + destruct (ptree_eqdec z c1) as [Heq1|Hneq1].
    { left. rewrite Heq1. left. simpl. now left. }
    destruct (IHc2 z) as [zltc2|nzltc2].
    * left. right with c2; try assumption. left. simpl. now right.
    * destruct (ptree_eqdec z c2) as [Heq2|Hneq2].
     -- left. rewrite Heq2. left. simpl. now right.
     -- right. intro Hctr. apply clos_trans_tn1 in Hctr. inversion Hctr.
       ++ simpl in H. destruct H; contradiction.
       ++ simpl in H. destruct H.
         ** rewrite H in H0. apply clos_tn1_trans in H0. contradiction.
         ** rewrite H in H0. apply clos_tn1_trans in H0. contradiction.
- intro z. induction cs as [| c cs IHcs].
  -- right. intro Hctr. apply clos_trans_tn1 in Hctr.
     inversion Hctr; subst; simpl in *; contradiction.
  -- destruct (ptree_eqdec z c) as [Heq | Hneq].
     ++ subst. left. left. simpl. left. reflexivity.
     ++ destruct (F z c) as [zltc | nzltc].
        ** left. right with c.
        --- exact zltc.
        --- left. simpl. left. reflexivity.
        ** destruct IHcs as [zltcs | nzltcs].
        --- left. apply clos_trans_t1n in zltcs.
        apply clos_t1n_trans. clear nzltc Hneq. revert z zltcs.
        fix IH 2. intros z zltcs.
        inversion zltcs as [x Hstep | x y w Hstep Hrest]; subst.
         + constructor. simpl. right. simpl in Hstep. exact Hstep.
         + econstructor 2.
        * exact w.
        * apply IH. assumption.
         --- right. intro Hbig. apply clos_trans_tn1 in Hbig.
         inversion Hbig; subst.
        + simpl in H. destruct H as [Heq | Hin].
        * apply Hneq. symmetry. exact Heq.
        * apply nzltcs. left. simpl. exact Hin.
        + simpl in H. destruct H as [Hcy | Hycs].
        * apply nzltc. apply clos_tn1_trans. rewrite <- Hcy in H0. exact H0.
        * apply nzltcs. apply clos_tn1_trans. econstructor 2 with (y := y).
          simpl. exact Hycs. exact H0. 
Defined.

Theorem desc_child_or_child_dec [x z] : z </ x ->
  {y | is_child y x /\ z </ y} + {is_child z x}.
Proof.
intro zltx. induction x as [c IHc fs ph| c IHc fs ph| c IHc fs ph|c1 IHc1 c2 IHc2 fs phi|cs fs phi];
try (
destruct (desc_dec z c) as [zltc1|nzltc1];
  [left; exists c; simpl; split; tauto|
  right; apply not_desc_child_desc; try assumption;
    intros y Hy; simpl in Hy; rewrite Hy; assumption]).
- destruct (desc_dec z c1) as [zltc1|nzltc1].
  + left. exists c1. simpl. split; tauto.
  + destruct (desc_dec z c2) as [zltc2|nzltc2].
    * left. exists c2. simpl. split; tauto.
    * right. apply not_desc_child_desc; try assumption.
      intros y Hy. simpl in Hy. destruct Hy as [Hy|Hy];
      (rewrite Hy; assumption).
- induction cs as [|c l Hl].
  + apply False_rec.
    apply clos_trans_tn1 in zltx.
    inversion zltx; subst; simpl in *; contradiction.
  + assert( tjump_scanner : ~ z </ c -> z <> c -> z </ tjump (c :: l) fs phi -> z </ (tjump l fs phi)).
  { 
    intros nzltc Hneq zltcs. apply clos_trans_tn1 in zltcs. inversion zltcs; subst.
  - simpl in H. destruct H as [Hcz | Hin].
  + exfalso. apply Hneq. symmetry. exact Hcz.
  + apply clos_tn1_trans. apply tn1_step. simpl. exact Hin.
- simpl in H. destruct H as [Hcy | Hin].
  + exfalso. apply nzltc. apply clos_tn1_trans. rewrite <- Hcy in H0. exact H0.
  + eapply tn1_trans. econstructor 2 with (y := y).
  * simpl. exact Hin.
  * exact H0.
  }
   destruct (desc_dec z c) as [zltc | nzltc].
  ** left. exists c. split.
  * simpl. left. reflexivity.
  * exact zltc.
  ** destruct (ptree_eqdec z c) as [Heq | Hneq].
  * subst. right. simpl. left. reflexivity.
  * pose proof (tjump_scanner nzltc Hneq zltx) as zlt_tail.
    destruct (Hl zlt_tail) as [[y [Hychild Hylt]] | Hzchild].
    ++ left. exists y. split.
      -- simpl in Hychild. simpl. right. exact Hychild.
      -- exact Hylt.
    ++ right. simpl in Hzchild. simpl. right. exact Hzchild.
Defined.

Lemma desc_desceq_child [x z] : z </ x -> exists y, is_child y x /\ z <=/ y.
Proof.
intro zltx. apply clos_trans_tn1 in zltx. inversion zltx.
- exists z. split; [assumption | now right].
- apply clos_tn1_trans in H0. exists y. split; [assumption | now left].
Qed.


Lemma tjump_desc_child : forall x cs fseqt phi, (exists y, In y cs /\ x <=/ y) -> x </ (tjump cs fseqt phi).
Proof.
  intros x cs fseqt phi. induction cs as [|c cs IH].
  - intros H. destruct H as [y [Hin Hleq]]. contradiction.
  - intros IH'. destruct IH' as [y [Hin Hleq]].
    + destruct Hleq as [xley |xeqy].
    * eapply t_trans.
    exact xley. apply t_step. apply Hin.
    * subst x.
      apply t_step.
      apply Hin. 
Qed.



Lemma child_size_lt :
  forall x y, is_child x y -> tree_size x < tree_size y.
Proof.
  intros x y H.
  destruct y as [ | | | |cs fs phi];
  try (inversion H; subst; simpl; lia).
  simpl in H.
  induction cs as [|c l IHl].
  - contradiction.
  - destruct H as [xeqc|xinl].
    simpl. rewrite xeqc. lia.
    assert (size_list_lt: tree_size (tjump l fs phi) <=  tree_size (tjump (c :: l) fs phi) ).
    simpl. lia.
    pose proof (IHl xinl) as Hlt.
    lia.
Qed.

Lemma desc_size_lt :
  forall x y, x </ y -> tree_size x < tree_size y.
Proof.
  intros x y H.
  induction H.
  - apply child_size_lt.
    assumption.
  - lia.
Qed.

Lemma no_desc_tjump_nil :
  forall x fs phi, ~ x </ tjump [] fs phi.
Proof.
  intros x fs phi H.
  remember (tjump [] fs phi) as t eqn:Ht.
  induction H.
  - subst.
    contradict H.
  - subst z.
    inversion H; subst; simpl in *; contradiction.
Qed.

Theorem desc_ptree_induction [P : ptree -> Prop] :
  (forall x, forall (IH : forall y, y </ x -> P y), P x) -> forall x, P x.
Proof.
  intros IS.
  assert (Hn : forall n x, tree_size x <= n -> P x).
  {
    induction n as [|n IHn].
    - intros x Hx.
      destruct x; simpl in Hx; lia.
    - intros x Hx.
      apply IS.
      intros y Hyx.
      apply IHn.
      pose proof (desc_size_lt Hyx ) as Hsize.
      lia.
  }
  intro x.
  apply (Hn (tree_size x)).
  lia.
Qed.


Fixpoint all_nodes (x : ptree) : list (ptree) :=
  x ::
  match x with
  | talpha c _ _   => all_nodes c
  | tbeta1 c _ _ _ => all_nodes c
  | tbeta2 c _ _ _ => all_nodes c
  | talt c1 c2 _ _ _ => all_nodes c1 ++ all_nodes c2
  | tjump cs _ _       =>
        ((fix all_nodes_jump (cs : list ptree) : list(ptree) :=
            match cs with
            | [] => []
            | c :: cs' => all_nodes c ++ all_nodes_jump cs'
            end) cs)
  end.

Lemma all_nodes_self_in : forall x, In x (all_nodes x).
Proof.
intro x. destruct x; now left.
Qed.

Theorem desceq_in_all_nodes (y : ptree) :
  forall x, x <=/ y -> In x (all_nodes y).
Proof.
intros x xley. destruct xley as [xlty|xeqy].
- apply clos_trans_tn1 in xlty. induction xlty.
  + destruct y; try ((simpl in H |- *; rewrite H;
    right; apply all_nodes_self_in) || contradiction).
    destruct H as [H|H]; simpl in H |- *; rewrite H;
    right; apply in_app_iff; [left|right];
    apply all_nodes_self_in. simpl in *.  right.
    induction l as [|c l IHl]. 
    *contradiction.
    * destruct H as [H| H].
     subst c. apply in_or_app. left.
     apply (all_nodes_self_in x). 
     pose (IHl H) as H1.
     apply in_or_app. right. assumption.
  + destruct z;
    try ((right; rewrite <- H; assumption) || contradiction).
    destruct H as [H|H]; right; apply in_app_iff; [left|right];
    rewrite <- H; assumption.
    assert (incl (all_nodes y) (all_nodes(tjump l f n))). 
    * simpl in *. unfold incl. intros z Hz.
    right. revert H. induction l as [|c l IH]; intros H.
    -- contradiction.
    -- simpl in H. simpl. destruct H as [Hy | Hy].
    ++ subst c. apply in_or_app. left. exact Hz.
    ++ apply in_or_app. right. apply IH. exact Hy.
    * apply H0. assumption.
- rewrite xeqy. apply all_nodes_self_in.
Qed.



(* tpath Relation *)

Inductive tpath : list ptree -> ptree -> ptree -> Prop :=
  | tpath_nil  : forall x, tpath [] x x
  | tpath_cons : forall p x y z, is_child y x ->
      tpath p y z -> tpath (x :: p) x z.

(* [tpath p start endpoint] stores [start] and the intermediate parents in
   [p].  The endpoint is deliberately separate; for a zero-length path the
   stored list is empty. *)
Lemma tpath_nil_iff : forall x y,
  tpath [] x y <-> x = y.
Proof.
  intros x y. split.
  - intro Hpath. inversion Hpath. reflexivity.
  - intro Heq. subst y. constructor.
Qed.

Lemma tpath_start_in : forall p x y,
  tpath p x y -> p <> [] -> In x p.
Proof.
  intros p x y Hpath. induction Hpath.
  - contradiction.
  - intro Hnonempty. now left.
Qed.

Definition tpath_nodes (p : list ptree) (endpoint : ptree) : list ptree :=
  endpoint :: p.

Lemma tpath_endpoint_in_nodes : forall p x y,
  tpath p x y -> In y (tpath_nodes p y).
Proof. intros p x y _. now left. Qed.

Lemma tpath_end_desceq_start : forall x y p, tpath p x y -> y <=/ x.
Proof.
intros x y p piep. induction piep.
- now right.
- destruct IHpiep as [Hdesc|Heq].
  + left. right with y; [assumption | now left].
  + rewrite Heq. left. left. assumption.
Qed.

Lemma tpath_endpoint_desceq : forall p x y,
  tpath p x y -> y <=/ x.
Proof. intros p x y Hpath. exact (tpath_end_desceq_start Hpath). Qed.

Lemma in_tpath_desceq : forall x y z p, tpath p x z ->
  In y p -> y <=/ x.
Proof.
intros x y z p piep. induction piep.
- simpl. tauto.
- intros Hy. destruct Hy as [Hy|Hy].
  + now right.
  + apply IHpiep in Hy. destruct Hy as [Hy|Hy].
    * left. right with y0; [assumption | now left].
    * left. left. rewrite Hy. assumption.
Qed.

Lemma in_tpath_nodes_desceq : forall p root endpoint z,
  tpath p root endpoint ->
  In z (tpath_nodes p endpoint) -> z <=/ root.
Proof.
  intros p root endpoint z Hpath Hin.
  destruct Hin as [Heq | Hin].
  - subst z. apply tpath_endpoint_desceq with (p := p). exact Hpath.
  - apply in_tpath_desceq with (z := endpoint) (p := p); assumption.
Qed.

Definition unmarked_tpath
  (p : list ptree) (root endpoint : ptree) : Prop :=
  tpath p root endpoint /\
  Forall (fun x => t_mrk x = false) (tpath_nodes p endpoint).

Lemma unmarked_tpath_endpoint_unmarked : forall p root endpoint,
  unmarked_tpath p root endpoint -> t_mrk endpoint = false.
Proof.
  intros p root endpoint [_ Hall].
  inversion Hall. assumption.
Qed.

Lemma unmarked_tpath_start_unmarked : forall p root endpoint,
  unmarked_tpath p root endpoint -> t_mrk root = false.
Proof.
  intros p root endpoint [Hpath Hall].
  rewrite Forall_forall in Hall. apply Hall.
  unfold tpath_nodes.
  destruct p as [|a p].
  - apply tpath_nil_iff in Hpath. subst endpoint.
    now left.
  - right. apply tpath_start_in with (y := endpoint);
      [exact Hpath | discriminate].
Qed.

Lemma cut_tpath [p x z] : tpath p x z -> forall y, In y p ->
  exists q, tpath q y z /\ incl q p.
Proof.
intros H y Hy. induction H; try contradiction.
destruct Hy as [Hy|Hy].
- exists (x :: p). rewrite Hy in H |- *. split; try (apply incl_refl).
  right with y0; try assumption.
- destruct (IHtpath Hy) as [q [Hq1 Hq2]].
  exists q. split; try assumption. apply incl_tl. assumption.
Qed.

Inductive tpath_alt : list ptree -> ptree -> ptree -> Prop :=
  | tpath_alt_nil  : forall x, tpath_alt [] x x
  | tpath_alt_cons : forall p x z, p <> [] -> hd df_t p = x ->
      (forall n, S n < length p -> is_child (nth (S n) p df_t) (nth n p df_t)) ->
      is_child z (last p df_t) -> tpath_alt p x z.

Lemma tpath_l_alt [p x z] : tpath p x z -> tpath_alt p x z.
Proof.
intro H. induction H; try left.
inversion IHtpath.
- simpl. right.
  + discriminate.
  + simpl. reflexivity.
  + simpl. lia.
  + simpl. rewrite <- H3. assumption.
- right.
  + discriminate.
  + simpl. reflexivity.
  + intros n Hn. destruct p; try (simpl in Hn; lia).
    destruct n.
    * simpl. simpl in H2. rewrite H2. assumption.
    * specialize (H3 n). simpl. simpl in H3. apply H3.
      simpl in Hn. lia.
  + destruct p; try contradiction. rewrite last_cons_cons_eq.
    assumption.
Qed.

Lemma tpath_alt_l [p x z] : tpath_alt p x z -> tpath p x z.
Proof.
revert x z. induction p.
- intros x z H. inversion H; [left|contradiction].
- intros x z H. inversion H. simpl in H1. rewrite H1.
  destruct p.
  + simpl in H3. rewrite H1 in H3. right with z; [assumption|left].
  + right with p.
    * specialize (H2 O). simpl in H2. rewrite H1 in H2. apply H2. lia.
    * apply IHp. right.
     -- discriminate.
     -- simpl. reflexivity.
     -- intros n Hn. specialize (H2 (S n)). simpl in H2. simpl. apply H2.
        simpl in Hn. lia.
     -- rewrite last_cons_cons_eq in H3. assumption.
Qed.

Lemma tpath_l_alt_iff {p x z} : tpath p x z <-> tpath_alt p x z.
Proof.
split; [apply tpath_l_alt|apply tpath_alt_l].
Qed.
