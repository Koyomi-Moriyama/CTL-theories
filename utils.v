Require Import Arith.
Require Import List.
Require Import ListDec.
Require Import ListSet.
Require Import SetoidList.
Import ListNotations.
Require Import Lia.
Require Import RelationClasses.

Require Import Classical.


Theorem induction_from_rank (s:nat) : forall P : nat -> Prop, P s ->
  (forall n, n >= s -> P n -> P (S n)) -> forall n, n >= s -> P n.
Proof.
intros P base IS. induction n.
- intro H. apply Arith_prebase.le_n_0_eq_stt in H.
  rewrite H. assumption.
- intro H. destruct (le_lt_eq_dec _ _ H) as [sltSn|seqSn].
  + apply IS; try lia. apply IHn. lia.
  + rewrite <- seqSn. assumption.
Qed.

Set Implicit Arguments.

Section ListMore.
  Variable A : Type.
  Variable A_eqdec : forall (x y : A), {x = y} + {x <> y}.

  Lemma In_not_nil : forall (l : list A) [x], In x l -> l <> [].
  Proof.
  intros x l Hx Hctr. rewrite Hctr in Hx. contradiction.
  Qed.

  Lemma incl_not_nil (l l' : list A) : incl l l' -> l <> [] -> l' <> [].
  Proof.
  intros H H0. destruct l as [|a l]; try contradiction.
  intro Hctr. fold (In a []). rewrite <- Hctr.
  apply H. now left.
  Qed.

  Lemma last_cons_cons_eq [l : list A] (a b d : A) :
    last (a :: b :: l) d = last (b :: l) d.
  Proof.
  simpl. destruct l; reflexivity.
  Qed.
  
  Lemma nth_last [l : list A] (d : A) :
    nth (length l - 1) l d = last l d.
  Proof.
  induction l.
  - simpl. reflexivity.
  - destruct l; try reflexivity. set (l' := a0 :: l). fold l' in IHl.
    fold ([a] ++ l'). rewrite app_length. rewrite <- Nat.add_sub_assoc.
    + rewrite app_nth2_plus. rewrite IHl. unfold l'. unfold app.
      rewrite last_cons_cons_eq. reflexivity.
    + simpl. lia.
  Qed.

  Definition eqset (l1 l2 : list A) : Prop := incl l1 l2 /\ incl l2 l1.

  Theorem eqset_in_iff (l l' : list A) :
    eqset l l' -> (forall x, In x l <-> In x l').
  Proof.
  intros H x. split; apply H.
  Qed.

  Theorem eqset_dec (l1 l2 : list A) : {eqset l1 l2} + {~ eqset l1 l2}.
  Proof.
  destruct (incl_dec A_eqdec l1 l2) as [Hi12|Hni12].
  - destruct (incl_dec A_eqdec l2 l1) as [Hi21|Hni21].
    + left. unfold eqset. tauto.
    + right. unfold eqset. tauto.
  - right. unfold eqset. tauto.
  Defined.

  Theorem eqset_refl : forall l, eqset l l.
  Proof. intro l. split; apply incl_refl. Qed.

  Theorem eqset_sym : forall l l', eqset l l' -> eqset l' l.
  Proof. intros l l'. unfold eqset. tauto. Qed.
  
  Theorem eqset_tran : forall l m n, eqset l m -> eqset m n -> eqset l n.
  Proof.
  intros l m n Hlm Hmn. destruct Hlm as [Hlm Hml].
  destruct Hmn as [Hmn Hnm]. split.
  - intros x Hx. apply Hmn, Hlm. assumption.
  - intros x Hx. apply Hml, Hnm. assumption.
  Qed.

  Instance eqset_equivalence : Equivalence eqset :=
  {
    Equivalence_Reflexive  := eqset_refl;
    Equivalence_Symmetric  := eqset_sym;
    Equivalence_Transitive := eqset_tran
  }.

  Lemma eqset_cons_remove [a l] : In a l -> eqset l (a :: remove A_eqdec a l).
  Proof.
  intro H. split.
  - intros x Hx. destruct (A_eqdec x a) as [Heq|Hneq].
    + now left.
    + right. apply in_in_remove; assumption.
  - intros x Hx. destruct Hx as [Hx|Hx].
    + rewrite <- Hx. assumption.
    + apply in_remove in Hx. tauto.
  Qed.

  Lemma eqset_eqset_cons_cons [a : A] [l l'] : eqset l l' -> eqset (a :: l) (a :: l').
  Proof.
  intro H. destruct H as [H H0]. split.
  - intros x Hx. destruct Hx as [Hx|Hx]; try (now left). right. apply (H x Hx).
  - intros x Hx. destruct Hx as [Hx|Hx]; try (now left). right. apply (H0 x Hx).
  Qed.

  Lemma inclA_cons_inclA [a l l'] : inclA eqset (a :: l) l' -> inclA eqset l l'.
  Proof. intros H x Hx. apply H. constructor 2. assumption. Qed.

  Lemma neqset_in_in_remove [a b l] : ~ eqset a b -> InA eqset a l ->
  InA eqset a (remove (list_eq_dec A_eqdec) b l).
  Proof.
  intros H H0. rewrite InA_alt in H0. destruct H0 as [x [Heqs Hin]].
  assert (x <> b) as H0. { intro Heq. contradict H. rewrite <- Heq. assumption. }
  rewrite InA_alt. exists x. split; try assumption.
  apply in_in_remove; assumption.
  Qed.

  Lemma inclA_nin_inclA_remove [a l l'] : ~ InA eqset a l -> inclA eqset l l' ->
  inclA eqset l (remove (list_eq_dec A_eqdec) a l').
  Proof.
  intros H H0 x Hx. apply neqset_in_in_remove.
  - intro H1. contradict H. rewrite InA_alt in Hx.
    destruct Hx as [y [Heqs Hin]]. rewrite InA_alt. exists y.
    split; try assumption. apply eqset_tran with x; try assumption.
    apply eqset_sym. assumption.
  - apply H0. assumption.
  Qed.
  
  Lemma eq_InA_InA [a b l] : eqset a b -> InA eqset a l -> InA eqset b l.
  Proof.
  intros H H0. induction H0.
  - constructor 1. apply eqset_tran with a; try assumption. apply eqset_sym. assumption.
  - constructor 2. assumption.
  Qed. 

  Theorem NoDupA_set_incl_length l l' :
    NoDupA eqset l -> inclA eqset l l' -> length l <= length l'.
  Proof.
  intro N. revert l'. induction N as [|a l Hal N IH]; simpl.
  - intros. now apply Nat.le_0_l.
  - intros l' H. assert (InA eqset a l') as H0.
    { apply H. constructor 1. apply eqset_refl. }
    rewrite InA_alt in H0. destruct H0 as [a' [Heqs Hin]].
    apply inclA_cons_inclA in H.
    assert (inclA eqset l (remove (list_eq_dec A_eqdec) a' l')) as H0.
    { apply inclA_nin_inclA_remove; try assumption. intro Hctr.
    contradict Hal. apply eq_InA_InA with a'; try assumption. apply eqset_sym.
    assumption. }
    specialize (IH _ H0).
    pose proof (remove_length_lt (list_eq_dec A_eqdec) _ _ Hin) as H1.
    lia.
  Qed.

  Fixpoint power_set (l : list A) : list (list A) :=
    match l with
    | []      => [[]]
    | a :: l' => (map (cons a) (power_set l')) ++ (power_set l')
    end.
  
  Lemma not_in_incl_cons_incl [a : A] [l l'] : ~ In a l -> incl l (a :: l') -> incl l l'.
  Proof.
  intros H H0 x Hx. specialize (H0 x Hx). destruct H0 as [H0|H0].
  - rewrite <- H0 in Hx. contradiction.
  - assumption.
  Qed.

  Lemma incl_remove (a : A) (l : list A) : incl (remove A_eqdec a l) l.
  Proof.
  intros x Hx. apply in_remove in Hx. tauto.
  Qed.

  Theorem incl_inset_power_set (l l' : list A) : incl l l' -> InA eqset l (power_set l').
  Proof.
  revert l. induction l'.
  - intros l H. rewrite (incl_l_nil H). simpl. constructor 1.
    split; apply incl_nil_l.
  - intros l H. destruct (in_dec A_eqdec a l) as [Hin|Hnin].
    + pose proof (remove_In A_eqdec l a) as H0.
      set (l0 := remove A_eqdec a l).
      pose proof (incl_tran (incl_remove a l) H) as H1.
      apply (not_in_incl_cons_incl H0) in H1.
      specialize (IHl' _ H1). apply InA_alt in IHl'.
      destruct IHl' as [l0' [Hl0'1 Hl0'2]].
      set (l1 := a :: l0').
      simpl. apply InA_app_iff. left.
      pose proof (eqset_tran (eqset_cons_remove Hin)
      (eqset_eqset_cons_cons Hl0'1)) as H2.
      rewrite InA_alt. setoid_rewrite in_map_iff.
      exists l1. split; try assumption.
      exists l0'. split; tauto.
    + pose proof (not_in_incl_cons_incl Hnin H) as H0.
      simpl. apply InA_app_iff. right. apply IHl'. assumption.
  Qed.

  Theorem all_eq_dec (l : list A) (a : A) :
  {forall b, In b l -> b = a} + {exists b, In b l /\ b <> a}.
  Proof.
  induction l as [|a0 l'].
  - now left.
  - destruct IHl' as [Hl|Hr].
    + destruct (A_eqdec a0 a) as [Heq|Hneq].
      * left. rewrite Heq. intros b H. destruct H as [H|H].
      -- apply eq_sym. assumption.
      -- apply Hl. assumption.
      * right. exists a0. split; [(now left)|assumption].
    + right. destruct Hr as [b [Hin Hneq]]. exists b.
      split; [(now right)|assumption].
  Defined.

  Lemma remove_all : forall (y : A) l,
    (forall x, In x l -> x = y) -> remove A_eqdec y l = [].
  Proof.
  intros y l Halleq. induction l as [|a l].
  - simpl. reflexivity.
  - rewrite (Halleq a); try now left. simpl.
    destruct (A_eqdec y y); try contradiction.
    apply IHl. intros x Hx. apply Halleq. now right.
  Qed.


  (* Requires XM *)
  Lemma list_specification (P : A -> Prop) : forall l : list A,
    exists l' : list A, forall x, In x l' <-> (In x l /\ P x).
  Proof.
  induction l as [|a l].
  - exists []. simpl. tauto.
  - destruct IHl as [l0 Hl0].
    destruct (classic (P a)) as [Pa|nPa].
    + exists (a :: l0). intro x. split.
      * intro Hx. destruct Hx as [Hx|Hx].
       -- rewrite <- Hx. split; [now left | assumption].
       -- apply Hl0 in Hx. simpl. tauto.
      * intro Hx. destruct Hx as [Hx Px].
        destruct Hx as [Hx|Hx].
       -- rewrite <- Hx. now left.
       -- right. apply Hl0. split; assumption.
    + exists l0. intro x. split.
      * intro Hx. apply Hl0 in Hx. simpl. tauto.
      * intro Hx. destruct Hx as [Hx Px].
        destruct Hx as [Hx|Hx].
       -- rewrite <- Hx in Px. contradiction.
       -- apply Hl0. split; assumption.
  Qed.



  (* Minimum and Maximum over lists *)

  Fixpoint list_min (l : list nat) : nat :=
    match l with
    | []      => 0
    | [a]     => a
    | a :: l' => min a (list_min l')
    end.

  Lemma list_min_2cons_eq : forall a b l,
    list_min (a :: b :: l) = min a (list_min (b :: l)).
  Proof.
  intros a b l. simpl. reflexivity.
  Qed.

  Lemma list_min_le_all : forall l x, In x l -> list_min l <= x.
  Proof.
  induction l as [|a l].
  - simpl. contradiction.
  - intros x Hx. destruct Hx as [Hx|Hx].
    + destruct l as [|b l].
      * simpl. rewrite <- Hx. apply Nat.le_refl.
      * simpl. rewrite <- Hx. apply Nat.le_min_l.
    + destruct l as [|b l]; try contradiction.
      rewrite list_min_2cons_eq.
      apply Nat.le_trans with (list_min (b :: l)).
      * apply Nat.le_min_r.
      * apply IHl. assumption.
  Qed.
  
  Lemma list_min_ex : forall l, l <> [] ->
    exists x, In x l /\ x = list_min l.
  Proof.
  induction l as [|a l]; try contradiction.
  intro H; clear H.
  destruct (list_eq_dec Nat.eq_dec l []) as [Hemp|Hnemp].
  - rewrite Hemp. exists a. split; try now left.
    simpl. reflexivity.
  - destruct (le_lt_dec (list_min l) a) as [Hle|Hlt].
    + destruct (IHl Hnemp) as [x [Hxin Hxeq]].
      exists x. split; try now right.
      destruct l as [|b l]; try contradiction.
      rewrite list_min_2cons_eq.
      rewrite (min_r _ _ Hle). assumption.
    + exists a. split; try now left.
      destruct l as [|b l]; try contradiction.
      rewrite list_min_2cons_eq.
      apply eq_sym.
      apply (min_l _ _ (Nat.lt_le_incl _ _ Hlt)).
  Qed.

  Definition list_max := fold_right max 0.

  Lemma list_max_ge_all : forall l x, In x l -> list_max l >= x.
  Proof.
  intro l. induction l as [|a l]; try contradiction.
  intros x Hx. destruct Hx as [Hx|Hx].
  - simpl. rewrite <- Hx. apply Nat.le_max_l.
  - simpl. apply Nat.le_trans with (list_max l).
    + apply IHl. assumption.
    + apply Nat.le_max_r.
  Qed.

End ListMore.



Lemma map_exists [A B : Type] (P : A -> B -> Prop) : forall l,
  (forall x, In x l -> exists y, P x y) ->
  exists l', forall x, In x l -> exists y, In y l' /\ P x y.
Proof.
intro l. induction l as [|a l].
- intro H; clear H. exists []. intros x Hx. contradiction.
- intro H. destruct IHl as [l' Hl'].
  { intros x Hx. apply H. now right. }
  destruct (H a) as [b Pab]; try now left.
  exists (b :: l'). intros x Hx. destruct Hx as [Hx|Hx].
  + exists b. split; try now left. rewrite <- Hx. assumption.
  + destruct (Hl' x Hx) as [y [Hy Pxy]].
    exists y. split; [now right | assumption].
Qed.


(* This section requires XM *)
Section LogicMore.

  Lemma not_and_or_iff {P Q : Prop} : ~ (P /\ Q) <-> ~ P \/ ~ Q.
  Proof.
  split; [apply not_and_or | apply or_not_and].
  Qed.

  Lemma or_to_imply_iff {P Q : Prop} : ~ P \/ Q <-> (P -> Q).
  Proof.
  split; [apply or_to_imply | apply imply_to_or].
  Qed.

  Lemma not_ex_all_not_iff [A : Type] (P : A -> Prop) :
    ~ (exists x, P x) <-> forall x, ~ P x.
  Proof.
  split. apply not_ex_all_not. apply all_not_not_ex.
  Qed.

End LogicMore.
