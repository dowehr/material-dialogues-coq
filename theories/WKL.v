Require Import Undecidability.FOLC.GenCompleteness Lia Nat.

(** ** Compactness and Weak König's Lemma  *)

Definition max_list_with {A} (f : A -> nat) : list A -> nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => Nat.max (f x) (go l)
  end.
Notation max_list := (max_list_with (fun x => x)).

Lemma max_list_spec l :
  l <> nil -> In (max_list l) l. 
Proof.
  destruct l as [ | x l] using rev_ind; try congruence.
  clear IHl. intros _. induction l; cbn in *.
  - left. lia.
  - destruct (Nat.max_dec a (max_list (l ++ [x]))) as [H1 | H1].
    + now left.
    + right. rewrite H1 in *. eauto.
Qed.

Lemma max_list_spec' x l :
  In x l -> x <= max_list l.
Proof.
  intros H.
  induction l in x, H |- *.
  - inv H.
  - inv H; cbn.
    + lia. 
    + eapply IHl in H0. lia.
Qed.

Lemma dec2bool_iff P (d : dec P) :
  dec2bool d = true <-> P.
Proof.
  destruct d; cbn; firstorder.
Qed.

Require Import Equations.Prop.DepElim.

Lemma to_list_inj {X n} (v1 v2 : Vector.t X n) :
  to_list v1 = to_list v2 -> v1 = v2.
Proof.
  induction v1 in v2 |- *; intros; cbn.
  - depelim v2. reflexivity.
  - depelim v2. inv H. f_equal. eapply IHv1, H2.
Qed.

Lemma cast_refl {X n} (v : Vector.t X n) :
  cast v eq_refl = v.
Proof.
  induction v; cbn; congruence.
Qed.

Lemma to_list_cast_of_list {X} (l : list X) n (e : length l = n) :
  to_list (cast (of_list l) e) = l.
Proof.
  destruct e. rewrite cast_refl.
  eapply to_list_of_list_opp.
Qed.

Lemma to_list_length {X n} (v : Vector.t X n) :
  length (to_list v) = n.
Proof.
  induction v; cbn.
  - reflexivity.
  - f_equal. now rewrite <- IHv.
Qed.

Lemma map_nth_id:
  forall (D : Type) (x : D) (l : list D),
    [nth_default x l x0 | x0 ∈ seq 0 (| l |)] = l.
Proof.
  intros D x l.
  induction l using rev_ind.
  + reflexivity.
  + rewrite app_length, seq_app, map_app.
    rewrite <- IHl at 3. f_equal.
    * eapply map_ext_in. intros ? ? % in_seq.
      unfold nth_default.
      rewrite nth_error_app1. reflexivity. lia.
    * cbn. f_equal. unfold nth_default.
      rewrite nth_error_app2, minus_diag.  reflexivity. lia.
Qed.

Lemma Vector_to_list_map {X Y n} (f : X -> Y) (v : Vector.t X n) :
  to_list (Vector.map f v) = map f (to_list v).
Proof.
  induction v.
  - reflexivity.
  - cbn. f_equal. fold (to_list v). rewrite <- IHv. reflexivity.
Qed.

Definition decidable_model := 
fun (Sigma : Signature) (D : Type) (I : interp D) => exists f : forall P, vector D (pred_ar P) -> bool, forall P, forall v : vector D (pred_ar P), f P v = true <-> i_P v.

Notation omniscient_on I phi := (forall (rho : env _), dec (rho ⊨ phi)).
Definition omniscient := fun (Sigma : Signature) (D : Type) (I : interp D) => inhabited (forall phi, omniscient_on I phi).

Lemma omniscient_to_classical {Σ : Signature} D (I : interp D) :
  omniscient I -> classical I.
Proof.
  intros [d] rho phi psi. cbn.
  destruct (d phi rho), (d psi rho); tauto.
Qed.

Definition vec_to_env {X} (v : list X) (d : X) : env X :=
  (nth_default d v).

Lemma omniscient_to_decidable {Σ : Signature} D (x : D) (I : interp D) :
  omniscient I -> decidable_model I.
Proof.
  intros [d].
  unshelve eexists (fun P v => d (Pred P (cast (of_list (map var_term (seq 0 (pred_ar P)))) _)) (nth_default x (to_list v))).
  - now rewrite map_length, seq_length.
  - intros P v. rewrite dec2bool_iff.
    cbn.
    match goal with
    | [ |- i_P ?a <-> i_P ?b ] => enough (a = b) as H by now rewrite H
    end. clear.
    eapply to_list_inj.
    rewrite Vector_to_list_map, to_list_cast_of_list, map_map. cbn.
    assert (pred_ar P = length (to_list v)) by now rewrite to_list_length.
    revert H. generalize (to_list v). intros. rewrite H.
    eapply map_nth_id.
Qed.

Lemma decidable_to_omniscient {Σ : Signature} (I : interp unit) :
  decidable_model I -> standard_bot I -> omniscient I.
Proof.
  intros [d Hd] SB. econstructor. intros phi rho.
  induction phi in rho |- *; cbn.
  - firstorder.
  - destruct (d P (Vector.map (eval rho) t)) eqn:E.
    + left. now eapply Hd.
    + right. intros ? % Hd. congruence.
  - destruct (IHphi1 rho), (IHphi2 rho); firstorder.
  - destruct (IHphi (tt .: rho)). left; now intros [].
    right. firstorder.
Qed.

Definition prefix {A} : list A -> list A -> Prop := fun l1 l2 => exists k, l2 = l1 ++ k.

Definition decidable {X} (p : X -> Prop) := exists f, forall x, p x <-> f x = true.

Record is_tree (tree_T : list bool -> Prop) :=
  {
    tree_inhab : exists l : list bool, tree_T l ;
    tree_p : forall l1 l2, prefix l1 l2 -> tree_T l2 -> tree_T l1 ;
    (* tree_dec :       decidable tree_T ; *)
  }.

Record tree :=
  {
  tree_T :> list bool -> Prop ;
  tree_is_tree :> is_tree tree_T
  }.

Definition bounded_tree (T : list bool -> Prop) := 
  exists k, forall a, length a >= k -> ~ T a.

Definition infinite_tree (T : list bool -> Prop) := 
  forall k, exists a, T a /\ (length a >= k ).

Definition infinite_path (T : list bool -> Prop) :=
  exists f : nat -> bool, forall n, T (map f (seq 0 n)).

Definition wellfounded_tree (T : list bool -> Prop) :=
  forall f : nat -> bool, exists n, ~ T (map f (seq 0 n)).

Lemma bounded_infinite_contra T :
  bounded_tree T -> infinite_tree T -> False.
Proof.
  firstorder.
Qed. 

Lemma path_wellfounded_contra T :
  infinite_path T -> wellfounded_tree T -> False.
Proof.
  intros [f H] H2.
  specialize (H2 f) as [n].
  eauto.
Qed.

Definition stable {X} (p : X -> Prop) := forall x, ~~ p x -> p x.

Definition WKL (C : (list bool -> Prop) -> Prop) :=
  forall T : tree, C T -> infinite_tree T -> infinite_path T.

Definition model_existence (CT : forall Sigma, @theory Sigma -> Prop) (Cond : forall Sigma D, @interp Sigma D -> Prop) :=
  forall {Sigma : Signature},
  forall {HdF : eq_dec Funcs} {HdP : eq_dec Preds},
  forall {HeF : enumT Funcs} {HeP : enumT Preds},
  forall T (T_closed : closed_T T), CT _ T -> consistent T ->
                               has_model (Cond Sigma) T.

Definition countable (X : Type) := inhabited (eq_dec X) /\ inhabited (enumT X).

Definition compactness (CT : forall Sigma, @theory Sigma -> Prop) (C : forall Sigma D, @interp Sigma D -> Prop) :=
  forall {Sigma : Signature},
  forall {HdF : eq_dec Funcs} {HdP : eq_dec Preds},
  forall {HeF : enumT Funcs} {HeP : enumT Preds},
  forall T (T_closed : closed_T T), CT _ T ->
  (forall Gamma, Gamma ⊏ T -> has_model (C Sigma) (fun x => In x Gamma))
  -> has_model (C Sigma) T.

Definition completeness (CT : forall Sigma, @theory Sigma -> Prop) (C : forall Sigma D, @interp Sigma D -> Prop) :=
  forall {Sigma : Signature},
  forall {HdF : eq_dec Funcs} {HdP : eq_dec Preds},
  forall {HeF : enumT Funcs} {HeP : enumT Preds},
  forall T (T_closed : closed_T T), CT _ T ->
                               forall phi, closed phi -> valid_T (C Sigma) T phi ->
                               T ⊩CE phi.

Lemma modex_standard :
  model_existence (fun _ _ => True) (fun Sigma D I => @SM Sigma D I /\ countable D).
Proof.
  intros Sigma HdF HdP HeF HeP T T_closed T_cons.
  pose proof (@model_bot_correct Sigma HdF HdP HeF HeP T T_closed).
  exists (@term Sigma). eexists. exists ids.
  setoid_rewrite <- H.
  repeat split; try exact _.
  - intros. eapply Out_T_sub. cbn. asimpl. assumption.
  - eapply model_bot_classical.
  - now eapply model_bot_standard.
Qed.

Lemma modex_compact (CT : forall Sigma, @theory Sigma -> Prop) (C : forall Sigma D, @interp Sigma D -> Prop) :
  (forall Sigma D I, C Sigma D I -> SM I) ->
  model_existence CT C -> compactness CT C.
Proof.
  intros HImpl HM Sigma HdF HdP HeF HeP T T_closed TC H.
  apply HM in T_closed as (D & I & rho & HI); trivial.
  + intros [Gamma [H1 H2]]. apply H in H1 as (D & I & rho & H3 & H4).
    apply Soundness' in H2. eapply HImpl. apply H4. now eapply (H2 D I (HImpl _ _ _ H4) rho). 
  + now exists D, I, rho.
Qed.

Definition XM := forall P : Prop, P \/ ~ P.

Lemma comp_modex (CT : forall Sigma, @theory Sigma -> Prop) (C : forall Sigma D, @interp Sigma D -> Prop) :
  XM -> completeness CT C -> model_existence CT C.
Proof.
  intros xm compl Sigma Hdf HdP HeF HeP T T_closed TC H.
  assert (dne : forall P, ~~ P -> P). { red in xm. intros. specialize (xm P). tauto. }
  eapply dne. intros HM.
  eapply H. eapply compl; eauto. econstructor.
  intros D I HDI rho HT. exfalso. eapply HM.
  exists D, I, rho. split; eauto.
Qed.

Lemma compact_standard :
  compactness (fun _ _ => True) (fun Sigma D I => @SM Sigma D I /\ countable D).
Proof.
  apply modex_compact. 2:apply modex_standard. firstorder.
Qed.

Definition DM `{Signature} D (I : interp D) := SM I /\ countable D /\ decidable_model I.
Definition OM `{Signature} D (I : interp D) := SM I /\ countable D /\ omniscient I.

Definition count_sig := @B_S False ltac:(tauto) nat (fun n => 0).

Definition Neg `{Signature} phi := Impl phi Fal.

Definition Or `{Signature} phi psi := Impl (Neg phi) psi.

Definition And `{Signature} phi psi := Neg (Or (Neg phi) (Neg psi)).

Lemma Neg_sat `{Signature} D (I : interp D) rho phi :
  standard_bot I ->
  rho ⊨ Neg phi <-> ~ rho ⊨ phi.
Proof.
  firstorder.
Qed.

Lemma omniscient_on_Neg `{Signature} D (I : interp D) phi :
  standard_bot I ->
  omniscient_on I phi -> omniscient_on I (Neg phi).
Proof.
  intros ? ? ?. destruct (X rho); cbn; firstorder.
Qed.
Hint Resolve omniscient_on_Neg : core.

Lemma Or_sat `{Signature} D (I : interp D) rho phi psi :
  standard_bot I -> inhabited (omniscient_on I phi) -> inhabited (omniscient_on I psi) ->
  rho ⊨ Or phi psi <-> rho ⊨ phi \/ rho ⊨ psi.
Proof.
  firstorder.
Qed.

Lemma omniscient_on_Or `{Signature} D (I : interp D) phi psi :
  standard_bot I ->
  omniscient_on I phi ->
  omniscient_on I psi ->
  omniscient_on I (Or phi psi).
Proof.
  firstorder.
Qed.
Hint Resolve omniscient_on_Or : core.

Lemma And_sat `{Signature} D (I : interp D) rho phi psi :
  standard_bot I -> inhabited (omniscient_on I phi) -> inhabited (omniscient_on I psi) ->
  rho ⊨ And phi psi <-> rho ⊨ phi /\ rho ⊨ psi.
Proof.
  intros ? [] [].
  split; unfold And; rewrite Neg_sat, Or_sat; eauto; firstorder.
Qed.

Lemma omniscient_on_And `{Signature} D (I : interp D) phi psi :
  standard_bot I ->
  omniscient_on I phi ->
  omniscient_on I psi ->
  omniscient_on I (And phi psi).
Proof.
  intros. destruct (X rho), (X0 rho); cbn; firstorder.
Qed.
Hint Resolve omniscient_on_And : core.

Fixpoint fExists `{Signature} (l : list form) :=
  match l with
  | [] => Fal
  | phi :: l => Or phi (fExists l)
  end.

Lemma to_False_iff {P : Prop} :
  (P -> False) -> (P <-> False).
Proof.
  tauto.
Qed.

Lemma omniscient_on_fExists_sat `{Signature} D (I : interp D) l :
  standard_bot I -> (forall phi, In phi l -> omniscient_on I phi) ->
  omniscient_on I (fExists l).
Proof.
  intros SB omn rho.
  induction l  as [ | phi] in SB, omn, rho |- *.
  - firstorder.
  - cbn - [Or].
    edestruct (omn phi); eauto.
    + left. rewrite Or_sat; eauto. 
    + edestruct IHl; eauto.
      * left. rewrite Or_sat; eauto.
      * right. rewrite Or_sat; eauto. firstorder.
Qed.

Lemma fExists_sat' `{Signature} D (I : interp D) rho l :
  standard_bot I -> (forall phi, In phi l -> omniscient_on I phi) ->
  rho ⊨ fExists l <-> exists phi, In phi l /\ rho ⊨ phi.
Proof.
  intros SB omn.
  induction l.
  - firstorder.
  - cbn - [Or].
    rewrite Or_sat, IHl; eauto.
    split.
    + intros [ | [? []]]; eauto.
    + intros [? [[-> | ]]]; eauto.
    + econstructor. eapply omniscient_on_fExists_sat; eauto.
Qed.

Lemma fExists_sat `{Signature} D (I : interp D) rho l :
  standard_bot I -> omniscient I ->
  rho ⊨ fExists l <-> exists phi, In phi l /\ rho ⊨ phi.
Proof.
  intros ? []. eapply fExists_sat'; eauto.
Qed.

Fixpoint fAll `{Signature} (l : list form) :=
  match l with
  | [] => Impl Fal Fal
  | phi :: l => And phi (fAll l)
  end.

Lemma omniscient_on_fAll_sat `{Signature} D (I : interp D) l :
  standard_bot I -> (forall phi, In phi l -> omniscient_on I phi) ->
  omniscient_on I (fAll l).
Proof.
  intros SB omn rho.
  induction l  as [ | phi] in SB, omn, rho |- *.
  - firstorder.
  - cbn - [And].
    edestruct (omn phi); eauto.
    + edestruct IHl; eauto.
      * left. rewrite And_sat; eauto.
      * right. rewrite And_sat; eauto. firstorder.
    + right. rewrite And_sat; eauto. firstorder.
Qed.

Lemma fAll_sat' `{Signature} D (I : interp D) rho l :
  standard_bot I -> (forall phi, In phi l -> (omniscient_on I phi)) ->
  rho ⊨ fAll l <-> forall phi, In phi l -> rho ⊨ phi.
Proof.
  intros SB omn.
  induction l.
  - firstorder.
  - cbn - [And].
    rewrite And_sat, IHl; eauto.
    split.
    + intros [] ? [-> | ]; eauto.
    + eauto 9.
    + econstructor. eapply omniscient_on_fAll_sat; eauto.
Qed.

Lemma fAll_sat `{Signature} D (I : interp D) rho l :
  standard_bot I -> omniscient I ->
  rho ⊨ fAll l <-> forall phi, In phi l -> rho ⊨ phi.
Proof.
  intros ? []. eapply fAll_sat'; eauto.
Qed.

Definition listable {X} (p : X -> Prop) := { L : list X | forall x, p x <-> In x L}.

Lemma listable_list_length :
  forall k : nat, listable (fun x : list bool => length x = k).
Proof.
  fix rec 1.
  destruct k as [ | k  ].
  - clear rec. exists [ [] ]. intros [] ; cbv ; firstorder. inv H.
  - specialize (rec k) as (L & IH). exists (map (fun l => l ++ [true]) L ++ map (fun l => l ++ [false]) L).
    intros l.
    rewrite in_app_iff, !in_map_iff.
    repeat setoid_rewrite <- IH.
    destruct l as [ | [] ? _] using rev_ind.
    + cbn. split. inversion 1. intros [([] & [=] & <-) | ([] & [=] & <-)].
    + cbn. split. 
      * inversion 1. rewrite app_length in H. cbn in H. rewrite plus_comm in H. inv H. eauto.
      * firstorder.
        -- eapply app_inj_tail in H as []. subst.
           now rewrite app_length, plus_comm.
        -- eapply app_inj_tail in H as []. subst.
           now rewrite app_length, plus_comm.
    + cbn. split. 
      * inversion 1. rewrite app_length in H. cbn in H. rewrite plus_comm in H. inv H. eauto.
      * firstorder.
        -- eapply app_inj_tail in H as []. subst.
           now rewrite app_length, plus_comm.
        -- eapply app_inj_tail in H as []. subst.
           now rewrite app_length, plus_comm.
Defined.

Notation nat := (nat).

Fixpoint mapi {X Y} (f : nat -> X -> Y) (l : list X) i :=
  match l with
  | [] => []
  | x :: l => f i x :: mapi f l (S i)
  end.

Lemma in_mapi_iff {X Y} (f : nat -> X -> Y) l y i :
  In y (mapi f l i) <-> exists x j, f (j + i) x = y /\ nth_error l j = Some x.
Proof.
  induction l as [ | x l] in i |- *; cbn.
  - firstorder. destruct x0; inv H0.
  - rewrite IHl. intuition subst.
    + now exists x, 0. 
    + destruct H0 as (x' & j & H1 & H2).
      exists x', (S j). split. rewrite <- H1; f_equal. lia. now cbn.
    + destruct H as (x' & [ | j] & H1 & H2); cbn in *.
      * inv H2. eauto.
      * right. exists x', j. split. rewrite <- H1; f_equal. lia. now cbn.
Qed.

Lemma mapi_app {X Y} (f : nat -> X -> Y) (l1 l2 : list X) i :
  mapi f (l1 ++ l2) i = mapi f l1 i ++ mapi f l2 (length l1 + i).
Proof.
  induction l1 in l2, i |- *; cbn.
  - reflexivity.
  - rewrite IHl1. repeat f_equal. lia.
Qed.

Lemma infinite_iff (T : tree) :
  infinite_tree T <-> forall k : nat, exists a : list bool, T a /\ | a | = k.
Proof.
  split.
  - intros H k. destruct (H k) as (? & ? & ?).
    exists (firstn k x). split. eapply tree_p. eapply T. 2:eauto.
    rewrite <- (firstn_skipn k x) at 2. eexists; eauto.
    rewrite firstn_length. lia.
  - intros H k. destruct (H k) as (? & ? & ?). exists x. split. eauto. lia.
Qed.

Inductive Is_Filter {X} (P : X -> Prop) : list X -> list X -> Prop :=
| Is_Filter_nil : Is_Filter P nil nil
| Is_Filter_true x l1 l2 : Is_Filter P l1 l2 -> P x -> Is_Filter P (x :: l1) (x :: l2)
| Is_Filter_false x l1 l2 : Is_Filter P l1 l2 -> ~ P x -> Is_Filter P (x :: l1) l2.

Lemma Is_Filter_filter {X} (P : X -> Prop) L L' (d : forall x, dec (P x)) :
  Is_Filter P L L' <-> L' = filter d L.
Proof.
  induction L in L' |- *; cbn.
  - split.
    + intros H. now inv H.
    + intros ->. econstructor.
  - destruct (d a); cbn.
    + split.
      * intros H. inv H; now eapply IHL in H2 as ->.
      * intros ->. econstructor; intuition.
    + split.
      * intros H. inv H; now eapply IHL in H2 as ->.
      * intros ->. econstructor; intuition.
Qed.

Lemma Is_Filter_In {X} (P : X -> Prop) {l1 : list X} {l2 : list X} {x} :
  Is_Filter P l1 l2 ->
  In x l2 <-> In x l1 /\ P x.
Proof.
  induction 1 in x |- *.
  - firstorder.
  - cbn; rewrite IHIs_Filter; now firstorder subst.
  - cbn; rewrite IHIs_Filter; now firstorder subst.
Qed.

Lemma Is_Filter_func {X} (P : X -> Prop) {l1 : list X} {l2 l2' : list X} :
  Is_Filter P l1 l2 -> Is_Filter P l1 l2' ->
  l2 = l2'.
Proof.
  induction 1 in l2' |- *; inversion 1; subst; f_equal; intuition.
Qed.

Lemma Is_filter_exists {X} (P : X -> Prop) {l1 : list X} :
  ~~ exists l2, Is_Filter P l1 l2.
Proof.
  induction l1.
  - intros H; apply H. repeat econstructor.
  - intros H. eapply IHl1. intros (l2 & Hl2).
    assert (Ha : ~~ (P a \/ ~ P a)) by tauto.
    apply Ha. clear Ha. intros [Ha | Ha].
    + eapply H. exists (a :: l2). econstructor; eauto.
    + eapply H. exists l2. econstructor; eauto.
Qed.

Lemma  Forall2_In {A B} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) b :
  Forall2 P l1 l2 ->
  In b l2 -> exists a, In a l1 /\ P a b.
Proof.
  induction 1.
  - firstorder.
  - intros [-> | H1].
    + exists x; eauto.
    + destruct (IHForall2 H1) as (? & ? & ?). eauto.
Qed.

Lemma Forall2_In1 {A B} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) a :
  Forall2 P l1 l2 ->
  In a l1 -> exists b, In b l2 /\ P a b.
Proof.
  induction 1.
  - firstorder.
  - intros [-> | H1].
    + exists y; eauto.
    + destruct (IHForall2 H1) as (? & ? & ?). eauto.
Qed.

Section WKL.

  Variable T : tree.

  Definition is_phi n psi := exists L, Is_Filter T (proj1_sig (listable_list_length n)) L /\ psi = fExists (map (fun l => fAll (mapi (fun i (b : bool) => if b then @Pred count_sig i Vector.nil else Neg (@Pred count_sig i Vector.nil)) l 0)) (L)).

  Definition Th psi := exists n, is_phi n psi.

  Lemma closed_Th :
    closed_T Th.
  Proof.
    intros psi n (m & L & H_L & ->).
    induction H_L; cbn.
    + econstructor.
    + repeat econstructor; eauto.
      generalize 0 as k. clear.
      induction x; intros; cbn; try destruct a; repeat econstructor.
      * intros. inv X.
      * eauto.
      * intros. inv X.
      * eauto.
    + repeat econstructor; eauto.
  Qed.

  Lemma get_index_list Γ :
    Γ ⊏ Th -> exists L, List.Forall2 is_phi L Γ.
  Proof.
    intros HΓ.
    induction Γ as [ | psi Γ].
    - now exists [].
    - destruct IHΓ as [L]. firstorder subst.
      subst. specialize (HΓ psi (or_introl eq_refl)) as [n Hn].
      exists (n :: L). subst. econstructor; eauto.
  Qed.

  Lemma phi_down D (I : interp D) rho n m phi_n phi_m :
    @standard_bot count_sig D I -> omniscient I ->
    is_phi n phi_n -> is_phi m phi_m ->
    rho ⊨ phi_n -> n >= m -> rho ⊨ phi_m.
  Proof.
    intros SB omn (L & H_L & ->) (L' & H_L' & ->) H.
    eapply fExists_sat in H as (phi' & H1 & H); eauto.
    destruct (listable_list_length n) as [L_ HL] eqn:E.
    eapply in_map_iff in H1 as (l & <- & [H3 % HL H4] % (Is_Filter_In H_L)); eauto.
    rewrite fAll_sat in H; eauto.
    intros Hle.
    eapply fExists_sat; eauto.
    eexists. split.
    - eapply in_map_iff. exists (firstn m l). split. reflexivity.
      eapply Is_Filter_In; eauto.
      split.
      + destruct (listable_list_length m). cbn. eapply i.
        eapply firstn_length_le. lia.
      + eapply tree_p.  eapply T. 2:eauto. rewrite <- (firstn_skipn m l) at 2. eexists; eauto.
    - eapply fAll_sat; eauto. intros. eapply H.
      rewrite <- (firstn_skipn m l).
      rewrite mapi_app. eauto.
  Qed.
  
  Definition M_u (u : list bool) : @interp count_sig unit.
    econstructor.
    * intros [].
    * cbn. intros n _.
      exact (nth n u false = true).
    * exact False.
  Defined.

  Lemma M_u_SB u : standard_bot (M_u u).
  Proof.
    now cbv.
  Qed.
  Hint Immediate M_u_SB.

  Lemma M_u_dec l : decidable_model (M_u l).
  Proof.
    unshelve eexists.
    -- cbn. intros k _.
       exact (nth k l false).
    -- cbn. reflexivity.
  Qed.
  Hint Immediate M_u_dec.

  Lemma M_u_omni u : omniscient (M_u u).
  Proof.
    eapply decidable_to_omniscient; eauto.
  Qed.
  Hint Immediate M_u_omni.

  Lemma model_u u :
    T u -> forall phi_n n, n <= |u| -> is_phi n phi_n -> sat (I := M_u u) (fun _ => tt) phi_n.
  Proof.
    revert u. intros l Hs' phi_m m H  Hphi.
    destruct Hphi as (L' & HL' & ->).
    eapply fExists_sat; eauto. eexists. split.
    -- eapply in_map_iff. exists (firstn m l). split. reflexivity.
       eapply Is_Filter_In. eassumption. split; eauto.
       destruct listable_list_length as (? & HH). cbn. eapply HH. rewrite firstn_length. lia.
       eapply tree_p. eapply T. 2:eauto. rewrite <- (firstn_skipn m l) at 2. eexists; eauto.
    -- eapply fAll_sat; eauto. intros phi' (b & j & <- & HH) % in_mapi_iff.
       rewrite <- plus_n_O. destruct b; cbn.
       rewrite <- nth_default_eq. unfold nth_default. rewrite <- (firstn_skipn m l).
       rewrite (nthe_app_l _ HH); eauto.
       rewrite <- nth_default_eq. unfold nth_default. rewrite <- (firstn_skipn m l).
       rewrite (nthe_app_l _ HH); eauto.
  Qed.

  Hint Resolve omniscient_to_classical.

  Instance enumT_unit : enumT unit.
  Proof.
    exists (fun _ => [tt]). eauto. intros []; cbn; exists 0. eauto.
  Qed.

  Lemma infinite_finitely_satisfiable :
    infinite_tree T -> forall Gamma : list form, Gamma ⊏ Th -> has_model (OM) (fun x : form => x el Gamma).
  Proof.
    intros infT. intros Γ HΓ.
    pose proof (get_index_list HΓ) as [L HL]. 
    pose (m := max_list L).
    rewrite infinite_iff in infT.
    destruct (infT m) as (l & Hl & Hs).
    exists unit, (M_u l), (fun _ => tt).
    split; eauto. 2:split. 3:split.
    intros phi (n & H & Hphi) % (Forall2_In HL).
    assert (Hn : n <= m) by now eapply max_list_spec'.
    assert (In m L) as (phi_m & Hphi_m & Hm) % (Forall2_In1 HL) by (eapply max_list_spec; intros ->; inv H).
    eapply phi_down with (n := m); eauto.
    destruct Hm as (L' & HL' & ->).
    eapply fExists_sat; eauto. eexists. split.
    - eapply in_map_iff. exists (firstn m l). split. reflexivity.
      eapply Is_Filter_In. eassumption. split; eauto.
      destruct listable_list_length as (? & HH). cbn. eapply HH. rewrite firstn_length. lia.
      eapply tree_p. eapply T. 2:eauto. rewrite <- (firstn_skipn m l) at 2. eexists; eauto.
    - eapply fAll_sat; eauto. intros phi' (b & j & <- & HH) % in_mapi_iff.
      rewrite <- plus_n_O. destruct b; cbn.
      rewrite <- nth_default_eq. unfold nth_default. rewrite <- (firstn_skipn m l).
      rewrite (nthe_app_l _ HH); eauto.
      rewrite <- nth_default_eq. unfold nth_default. rewrite <- (firstn_skipn m l).
      rewrite (nthe_app_l _ HH); eauto.
    - repeat split; eauto.
    - econstructor. econstructor. eauto. econstructor. eauto.
    - eapply M_u_omni.
  Qed.

  Lemma has_model_OM_DM (Th : @theory count_sig) :
    has_model (OM) Th -> has_model (DM) Th.
  Proof.
    intros (D & I & rho & H1 & H2).
    exists D, I, rho. split; eauto.
    split. eapply H2. split. eapply H2.
    eapply omniscient_to_decidable. eapply rho, 0. eapply H2.
  Qed.

  Lemma infinite_finitely_satisfiable' :
    infinite_tree T -> forall Gamma : list form, Gamma ⊏ Th -> has_model (DM) (fun x : form => x el Gamma).
  Proof.
    intros. eapply has_model_OM_DM, infinite_finitely_satisfiable; eauto.
  Qed.

  Lemma phi_exists n :
    ~~ exists phi, is_phi n phi.
  Proof.
    intros H.
    eapply (Is_filter_exists (l1 := proj1_sig (listable_list_length n)) (P := T)).
    intros (L & HL).
    eapply H. repeat econstructor; eassumption.
  Qed.

  Lemma exists_quasi_path :
    has_model (DM) Th -> exists f : nat -> bool, forall n : nat, ~~ T (map f (seq 0 n)).
  Proof.
    intros (D & I & rho & H & (classI & standI) & (eq_dec_D & enum_D) & (f & decI)).
    pose (g := fun n : nat => f n Vector.nil).
    exists g. intros n. unfold Th in H. unfold contains in H.
    intros HT. eapply (@phi_exists n). intros (phi_n & Hphin). eapply HT; clear HT.
    specialize (H (phi_n) ltac:(unfold contains; eauto)).
    assert ( forall l, forall phi0 : form, phi0 el mapi (fun (i : nat) (b : bool) => if b then @Pred count_sig i Vector.nil else Neg (@Pred count_sig i Vector.nil)) l 0 -> forall rho0 : env D, dec (rho0 ⊨ phi0)) as HHH.  {
      intros ? ? ? % in_mapi_iff. clear - H1 standI decI.
      revert H1.
      generalize 0 as k.
      induction l; intros k H1.
      * exfalso. destruct H1 as (? & [] & ? & ?); cbn in *; congruence.
      * decide (phi0 = @Pred count_sig k Vector.nil).
        -- subst. intros. destruct (f k Vector.nil) eqn:E.
           left. eapply decI. eauto. right. intros ? % decI. cbn in *. congruence.
        -- decide (phi0 = Neg (@Pred count_sig k Vector.nil)).
           ++ subst. intros. destruct (f k Vector.nil) eqn:E.
              right. eapply decI in E. cbn. firstorder. left.
              intros ? % decI. cbn in *. congruence.
           ++ eapply (IHl (S k)).
              destruct H1 as (x & j & ? & ?).
              destruct j.
              ** cbn in H0. destruct x.
                 --- inv H0. cbn in n. congruence.
                 --- inv H0. cbn in n0. congruence.
              ** cbn in *. exists x, j; destruct x; subst; split; eauto; repeat f_equal; lia.
    }
    destruct Hphin as (L_ & HL_ & ->).
    eapply fExists_sat' in H as (phi' & H1 & H); eauto.
    eapply in_map_iff in H1 as (l & <- & HLL).
    rewrite fAll_sat' in H.
    destruct (listable_list_length n) as [L HL].
    cbn in *.
    eapply (Is_Filter_In HL_) in HLL as [H3 H4].
    eapply HL in H3. 
    enough (l = [g p | p ∈ seq 0 n]) as -> by eassumption.
    subst. clear - H decI standI.
    revert H. generalize 0 as k.
    induction l; cbn; intros.
    + reflexivity.
    + f_equal. destruct a.
      * pose proof (H (@Pred count_sig k Vector.nil) (or_introl eq_refl)) as H0.
        eapply decI in H0. unfold g. cbn in H0. now rewrite H0.
      * pose proof (H (Neg (@Pred count_sig k Vector.nil)) (or_introl eq_refl)) as H0.
        cbn in H0. unfold g. rewrite <- decI in H0.
        symmetry. eapply not_true_is_false.
        intros [] % H0 % standI.
      * eapply IHl. intros. eapply H. eauto.
    + eauto.
    + eauto. 
    + intros phi0 ? % in_map_iff. clear - H2 standI decI HHH.
      induction L_.
      * exfalso. destruct H2 as (? & ? & ?); cbn in *; congruence.
      * decide (phi0 = fAll (mapi (fun (i : nat) (b : bool) => if b then @Pred count_sig i Vector.nil else Neg (@Pred count_sig i Vector.nil)) a 0)).
        -- subst. intros.
           eapply omniscient_on_fAll_sat. eauto. eapply HHH. 
        -- eapply IHL_. destruct H2 as (? & ? & ?). destruct H0.
           ++ subst. congruence.
           ++ eauto.
  Qed.

  Lemma compact_DM_WKL :
    compactness (fun _ _ => True) (@DM) -> infinite_tree T ->  exists f : nat -> bool, forall n : nat, ~~ T (map f (seq 0 n)).
  Proof.
    intros compact infT.
    unshelve epose proof (compact count_sig _ _ _ _ Th _ _ _).
    - eapply closed_Th.
    - cbn. econstructor.
    - now eapply infinite_finitely_satisfiable'.
    - now eapply exists_quasi_path. 
  Qed.

  Lemma compact_OM_WKL :
    compactness (fun _ _ => True) (@OM) -> infinite_tree T ->  exists f : nat -> bool, forall n : nat, ~~ T (map f (seq 0 n)).
  Proof.
    intros compact infT.
    unshelve epose proof (compact count_sig _ _ _ _ Th _ _ _).
    - eapply closed_Th.
    - cbn. econstructor.
    - now eapply infinite_finitely_satisfiable.
    - now eapply exists_quasi_path, has_model_OM_DM.
  Qed.

  Lemma decidable_to_decidable_n :
    (forall x, dec (T x)) -> forall n x, dec (is_phi n x).
  Proof.
    intros d n.
    intros phi.
    decide (phi = fExists (map (fun l => fAll (mapi (fun i (b : bool) => if b then @Pred count_sig i Vector.nil else Neg (@Pred count_sig i Vector.nil)) l 0)) (filter d (proj1_sig (listable_list_length n))))).
    - left. subst. eexists. split.
      eapply Is_Filter_filter. reflexivity.
      reflexivity.
    - right. intros (L & HL1 & ->).
      now eapply (Is_Filter_filter _ _ d) in HL1 as ->.
  Qed.

  Fixpoint count_conjs (phi : @form count_sig) :=
    match phi with
    | ¬ ((¬ phi --> ⊥) --> ¬ psi) => S (count_conjs psi)
    | _ => 0
    end.

  Definition get_n (phi : form) :=
    match phi with
    | (phi --> ⊥) --> _ => count_conjs phi
    | _ => 0
    end.

  Lemma decidable_to_decidable :
    decidable T -> infinite_tree T -> decidable Th.
  Proof.
    intros [d] % decidable_iff inf_T.
    eapply decidable_iff. econstructor.
    intros phi.
    destruct (decidable_to_decidable_n d (get_n phi) phi).
    - left. eexists. eauto.
    - right. intros (m & L & H1 & ->).
      eapply (Is_Filter_filter _ _ d) in H1 as ->.
      destruct n. eexists. split.
      eapply Is_Filter_filter. reflexivity.
      repeat f_equal.
      enough ((get_n
          (fExists
             (map (fun l => fAll (mapi (fun (i : nat) (b : bool) => if b then @Pred count_sig i Vector.nil else Neg (@Pred count_sig  i Vector.nil)) l 0))
                  (filter (fun x : list bool => d x) (proj1_sig (listable_list_length m)))))) = m) as ->.
      reflexivity. destruct (listable_list_length m) as [L HL]; cbn.
      cbn. destruct (inf_T m) as (u & Hu & Hs).
      assert (|firstn m u| = m) as Hm. { rewrite firstn_length_le. reflexivity. lia. }
      eapply HL in Hm.
      assert (T (firstn m u)) as HT. {
        eapply tree_p. eapply T. 2:eauto.
        eexists. rewrite <- (firstn_skipn m u) at 1. reflexivity.
      }
      destruct filter eqn:E.
      + exfalso. change (In (firstn m u) nil).
        rewrite <- E. eapply in_filter_iff.
        split. eauto. eapply Dec_auto. eauto.
      + cbn.
        assert (m = length l) as ->.
        * symmetry. eapply HL. eapply in_filter_iff. rewrite E. eauto.
        * clear. generalize 0. induction l; cbn; intros.
          -- reflexivity.
          -- now rewrite IHl.
  Qed.

  Lemma compact_DM_WKLD :
    compactness (fun _ T => decidable T) (@DM) -> infinite_tree T ->  decidable T -> exists f : nat -> bool, forall n : nat, ~~ T (map f (seq 0 n)).
  Proof.
    intros compact infT decT.
    unshelve epose proof (compact count_sig _ _ _ _ Th _ _ _).
    - eapply closed_Th.
    - cbn. eapply decidable_to_decidable; eauto.
    - now eapply infinite_finitely_satisfiable'.
    - now eapply exists_quasi_path. 
  Qed.

End WKL.

Lemma compact_implies_WKL' :
  compactness (fun _ _ => True) (@DM) -> WKL (fun T => forall l, ~~ T l -> T l).
Proof.
  intros comp T stab infT.
  destruct (compact_DM_WKL comp infT) as [g].
  exists g. eauto.
Qed.

Corollary compact_implies_WKL :
  XM -> compactness (fun _ _ => True) (@DM) -> WKL (fun _ => True).
Proof.
  intros xm wkl % compact_implies_WKL' T _ H.
  eapply wkl; eauto. intros.
  destruct (xm (T l)); tauto.
Qed.

Lemma compact_OM_implies_WKL' :
  compactness (fun _ _ => True) (@OM) -> WKL (fun T => forall l, ~~ T l -> T l).
Proof.
  intros comp T stab infT.
  destruct (compact_OM_WKL comp infT) as [g].
  exists g. eauto.
Qed.

Corollary compact_OM_implies_WKL :
  XM -> compactness (fun _ _ => True) (@OM) -> WKL (fun _ => True).
Proof.
  intros xm wkl % compact_OM_implies_WKL' T _ H.
  eapply wkl; eauto. intros.
  destruct (xm (T l)); tauto.
Qed.

Corollary compact_implies_WKL_D :
  XM -> compactness (fun _ T => decidable T) (@DM) -> WKL decidable.
Proof.
  intros xm comp T decT infT.
  destruct (compact_DM_WKLD comp infT decT) as [f Hf].
  exists f. intros n.
  eapply decidable_iff in decT as [d].
  destruct (d (map f (seq 0 n))).
  - eauto.
  - exfalso. eapply Hf. eassumption.
Qed.

Lemma modex_impl CT :
  model_existence CT (@DM) -> model_existence CT (@SM).
Proof.
  intros H Sigma H1 H2 H3 H4 T clT TC consT.
  destruct (H Sigma H1 H2 H3 H4 T clT TC consT) as (D & I & rho & H0 & HDM).
  exists D, I, rho. split. eauto. eapply HDM.
Qed.

Lemma modex_impl_OM_DM CT :
  model_existence CT (@OM) -> model_existence CT (@DM).
Proof.
  intros H Sigma H1 H2 H3 H4 T clT TC consT.
  destruct (H Sigma H1 H2 H3 H4 T clT TC consT) as (D & I & rho & H0 & HDM).
  exists D, I, rho. split. eauto. unfold DM. split. eapply HDM. split. eapply HDM.
  eapply omniscient_to_decidable. exact (rho 0). eapply HDM.  
Qed.

Require Import Undecidability.FOLC.ND.

Lemma Forall_app {X} l1 l2 (P : X -> Prop) :
  List.Forall P (l1 ++ l2) <-> (List.Forall P l1 /\ List.Forall P l2).
Proof.
  induction l1; cbn.
  - firstorder.
  - split; firstorder; inv H; try econstructor; firstorder.
Qed.

Definition ldecidable {X} (p : X -> Prop) := forall x, p x \/ ~ p x.

Lemma Forall2_length {X} {Y} (P : X -> Y -> Prop) l1 l2 :
  Forall2 P l1 l2 -> |l1| = |l2|.
Proof.
  induction 1; cbn; firstorder congruence.
Qed.

Lemma WKL_to_decidable : WKL (fun _ => True) -> forall p : nat -> Prop, ldecidable p -> decidable p.
Proof.
  intros wkl p d.
  pose (T l := Forall2 (fun b i => b = true <-> p i) l (seq 0 (|l|))).
  unshelve edestruct wkl as [f Hf]; cbn in *.
  - exists T. econstructor.
    + exists []. econstructor.
    + intros l1 ? [l2 ->]. intros (l1' & l1'' & ? & ? & ?) % Forall2_app_inv_l.
      rewrite app_length, seq_app in H1.
      pose proof (Forall2_length H). rewrite H2 in *.
      eapply (f_equal (firstn (|l1'|))) in H1.
      rewrite !firstn_app in H1.
      rewrite !seq_length, !minus_diag in H1.
      replace (|l1'|) with (|seq 0 (|l1'|)|) in H1 at 1 by now rewrite seq_length.
      rewrite !firstn_all, !firstn_O, !app_nil_r in H1.
      now rewrite <- H1, <- H2 in H.
  - eauto.
  - cbn in *; intros k.
    induction k as [ | k [l [IH1 IH2]]].
    + exists []. repeat econstructor.
    + destruct (d (|l|)).
      * exists (l ++ [true]). split.
        unfold T. rewrite app_length, seq_app. eapply Forall2_app.
        -- eapply IH1.
        -- cbn. repeat econstructor; firstorder.
        -- rewrite app_length; cbn; lia.
      * exists (l ++ [false]). split.
        unfold T. rewrite app_length, seq_app. eapply Forall2_app.
        -- eapply IH1.
        -- cbn. repeat econstructor. congruence. firstorder.
        -- rewrite app_length; cbn; lia.
  - cbn in *. exists f.
    intros n. specialize (Hf (n + 1)).
    unfold T in Hf.
    rewrite !map_length, !seq_length in Hf.
    rewrite seq_app, map_app in Hf. cbn in Hf.
    eapply Forall2_app_inv_l in Hf as (l1' & l2' & ? & ? & ?).
    inv H0. inv H6. eapply app_inj_tail in H1 as [].
    subst. inv H0. tauto.
Qed.

Require Import Undecidability.FOLC.Markov.


Lemma decidable_to_decidable_data : (forall p : nat -> Prop, ldecidable p -> decidable p) -> forall X, discrete X -> enumerable__T X -> forall p : X -> Prop, ldecidable p -> decidable p.
Proof.
  intros wkl X [d ]%decidable_iff [e He] p ld.
  enough (decidable (fun n => match e n with Some x => p x | _ => False end)) as [f Hf].
  - unshelve epose proof (fun x => mu _ (He x)) as g.
    + intros. cbn.
      destruct (e x0).
      * destruct (d (x1, x)). left. congruence. right. congruence.
      * right. congruence.
    + exists (fun x => f (proj1_sig (g x))).
      intros x. specialize (Hf (proj1_sig (g x))).
      destruct (g x) as [n Hn]; cbn in *.
      now rewrite Hn in Hf.
  - eapply wkl. intros n. destruct (e n); try tauto. eapply ld.
Qed.

Lemma WKL_to_decidable_data : WKL (fun _ => True) -> forall X, discrete X -> enumerable__T X -> forall p : X -> Prop, ldecidable p -> decidable p.
Proof.
  intros wkl.
  eapply decidable_to_decidable_data,  WKL_to_decidable, wkl.
Qed.

Lemma nthe_seq m n k :
  k < n -> nth_error (seq m n) k = Some (k + m).
Proof.
  induction n in m, k |- *; cbn; intros.
  - lia.
  - destruct k; cbn.
    + reflexivity.
    + rewrite IHn. f_equal. lia. lia.
Qed.

Lemma PCO_implies_modex :
  XM -> (forall p : nat -> Prop, ldecidable p -> decidable p) -> model_existence (fun _ _ => True) (@OM).
Proof.
  intros xm wkl Sigma Feq Peq Fe Pe Th Thcl _ consT.
  pose proof (modex_standard Feq Peq Fe Pe Thcl I consT) as (D & I & rho & H & [HM1 HM2] & [[HM3] [HM4]]).
  exists D, I, rho. split. eauto. do 2 split; eauto.
  repeat split; eauto. red.
  assert (decidable (fun x : form * list D => vec_to_env (snd x) (rho 0) ⊨ (fst x) )) as [d] % decidable_iff.
  - eapply decidable_to_decidable_data; eauto.
    + eapply discrete_iff. econstructor. exact _.
    + eapply enum_enumT. econstructor. exact _.
    + red. intros. eapply xm.
  - econstructor. intros phi rho'.
    destruct (find_unused phi) as [n Hn].
    specialize (d (phi, map rho' (seq 0 n))).
    eapply dec_transfer. 2:eassumption. cbn.
    eapply sat_ext_unused; eauto.
    intros. unfold vec_to_env. unfold nth_default.
    erewrite map_nth_error. reflexivity.
    rewrite nthe_seq. f_equal. lia. lia.
Qed.

Lemma WKL_implies_modex :
  XM -> WKL (fun _ => True) -> model_existence (fun _ _ => True) (@OM).
Proof.
  intros xm wjl. eapply PCO_implies_modex. eauto.
  now eapply WKL_to_decidable.
Qed.

Lemma CO_iff_EM_WKL : (forall X, forall p : X -> Prop, discrete X -> enumerable__T X -> decidable p) <-> XM /\ WKL (fun _ => True).
Proof.
  split.
  - intros. 
    assert (xm : XM). {
      intros P. specialize (H nat (fun _ => P) (ltac:(eapply discrete_iff; econstructor; eauto)) (ltac:(eapply enum_enumT; eauto))).
      eapply decidable_iff in H as [d].
      destruct (d 0); tauto.
    }
    split. eapply xm.
    eapply compact_implies_WKL; eauto.
    eapply modex_compact. firstorder.
    eapply modex_impl_OM_DM.
    eapply PCO_implies_modex; eauto.
    intros. eapply H. eapply discrete_iff. econstructor. eauto.
    eapply enum_enumT. econstructor. eauto.
  - intros. eapply WKL_to_decidable_data; eauto.
    eapply H.  intros n. eapply H.
Qed.
