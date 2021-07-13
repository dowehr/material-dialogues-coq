(** ** Material Dialogues * *)

From FOL Require Import GenTarski FullTarski FullFOL DeMorgan.

Section MaterialDialogues.
  Context {Sigma : Signature}.
  Hypothesis eq_dec_Funcs : eq_dec Funcs.
  Hypothesis eq_dec_Preds : eq_dec Preds.

  Section Rules.
    Context {domain : Type}.
    Context {I : interp domain}.

    Inductive attack :=
    | AFal : attack
    | APred (P : Preds) : vector term (pred_ar P) -> attack
    | AImpl : form -> form -> attack
    | AConj : bool -> form -> form -> attack
    | ADisj : form -> form -> attack
    | AAll : domain -> form -> attack
    | AEx : form -> attack.

    Definition target a :=
      match a with
      | AFal => Fal
      | @APred P v => Pred P v
      | AImpl phi psi => phi --> psi
      | AConj _ phi psi => phi ∧ psi
      | ADisj phi psi => phi ∨ psi
      | AAll _ phi => ∀ phi
      | AEx phi => ∃ phi
      end.
    Definition attacks a phi := target a = phi.
    Infix "⩥" := attacks (at level 70).

    Definition admission a :=
      match a with
      | AImpl phi _ => Some phi
      | _ => None
      end.
    Definition acons a A :=
      match admission a with
      | Some phi => phi :: A
      | None => A
      end.
    Infix "a::" := acons (at level 55).

    Definition subst_attack sigma a :=
      match a with
      | AFal => AFal
      | APred v => APred (Vector.map (subst_term sigma) v)
      | AImpl phi psi => AImpl phi[sigma] psi[sigma]
      | AConj b phi psi => AConj b phi[sigma] psi[sigma]
      | ADisj phi psi => ADisj phi[sigma] psi[sigma]
      | AAll s phi => AAll s phi[up_term_term sigma]
      | AEx phi => AEx phi[up_term_term sigma]
      end.

    Lemma subst_attack_attacks a phi sigma :
      a ⩥ phi -> subst_attack sigma a ⩥ phi[sigma].
    Proof.
      destruct a; intros <-; reflexivity.
    Qed.

    Lemma subst_attack_admission a phi sigma :
      admission (subst_attack sigma a) = Some phi -> exists psi : form, phi = psi[sigma] /\ admission a = Some psi.
    Proof.
      destruct a; cbn; try congruence; intros [= H]; now exists f.
    Qed.

    Lemma subst_attack_ids a :
      a = subst_attack ids a.
    Proof.
      destruct a; comp; try reflexivity. f_equal. symmetry. now apply vec_id.
    Qed.

    Lemma subst_attack_stacks a sigma sigma' :
      subst_attack sigma' (subst_attack sigma a) = subst_attack (sigma >> subst_term sigma') a.
    Proof.
      destruct a; comp; try reflexivity. erewrite vec_comp. reflexivity.
      intros; now comp.
    Qed.

    Lemma subst_attack_attack a phi sigma :
      a ⩥ subst_form sigma phi -> exists a', subst_attack sigma a' = a /\ a' ⩥ phi.
    Proof.
      destruct a; unfold attacks; cbn; destruct phi; cbn; try discriminate 1.
      - intros. exists AFal; cbn; intuition.
      - intros [= -> H]. resolve_existT. exists (APred t0); intuition.
      - intros [= -> ->]. exists (AImpl phi1 phi2); intuition.
      - intros [= -> ->]. exists (AConj b phi1 phi2); intuition.
      - intros [= -> ->]. exists (ADisj phi1 phi2); intuition.
      - intros [= ->]. exists (AAll d phi); intuition.
      - intros [= ->]. exists (AEx phi); intuition.
    Qed.

    Inductive defense :=
    | Dadm : form -> defense
    | Dwit : domain -> form -> defense
    | Dmat (P : Preds) : vector term (pred_ar P) -> defense
    | Dfal : defense.

    Definition defends d a :=
      match a with
      | AFal => d = Dfal
      | @APred P v => d = Dmat v
      | AImpl phi psi => d = Dadm psi
      | AConj b phi psi => if b then d = Dadm phi else d = Dadm psi
      | ADisj phi psi => d = Dadm phi \/ d = Dadm psi
      | AAll s phi => d = Dwit s phi
      | AEx phi => exists s, d = Dwit s phi
      end.
    Infix "⥼" := defends (at level 70).

    Definition subst_defense sigma d :=
      match d with
      | Dadm phi => Dadm phi[sigma]
      | Dwit d phi => Dwit d phi[up_term_term sigma]
      | Dmat v => Dmat (Vector.map (subst_term sigma) v)
      | Dfal => Dfal
      end.
    Lemma subst_attack_defends a sigma d :
      d ⥼ subst_attack sigma a -> exists d', d = subst_defense sigma d' /\ d' ⥼ a.
    Proof.
      destruct a; comp.
      - intros ->. now exists Dfal.
      - intros ->. now exists (Dmat t).
      - intros ->. now exists (Dadm f0).
      - destruct b; intros ->; [now exists (Dadm f) | now exists (Dadm f0)].
      - intros [-> | ->]; [exists (Dadm f) | exists (Dadm f0)]; intuition.
      - intros ->. exists (Dwit d0 f); now comp.
      - intros [? ->]. exists (Dwit x f); split; [now comp | now exists x].
    Qed.

    Definition state : Type := env domain * list form * list attack.

    Definition just rho d :=
      match d with
      | Dmat v => i_P (Vector.map (eval rho) v)
      | Dfal => False
      | _ => True
      end.

    Definition pdef d s : state :=
      match s with
        (rho, A, C) =>
          match d with
          | Dwit s phi => (s .: rho, map (subst_form ↑) A, map (subst_attack ↑) C)
          | _ => (rho, A, C)
          end
      end.

    Inductive pmove :=
    | PA : attack -> pmove
    | PD : form -> pmove
    | PM : pmove.

    Definition defmove d :=
      match d with
      | Dadm phi => PD phi
      | Dwit s phi => PD phi
      | Dmat _ => PM
      | Dfal => PM
      end.

    Inductive pturn : state -> state -> pmove -> Prop :=
    | PAtk rho A C phi a : phi el A -> a ⩥ phi -> pturn (rho, A, C) (rho, A, C) (PA a)
    | PDef rho A C c d : c el C -> d ⥼ c -> just rho d -> pturn (rho, A, C) (pdef d (rho, A, C)) (defmove d).

    Definition odef d s : state :=
      match s with
        (rho, A, C) =>
          match d with
          | Dadm phi => (rho, phi :: A, C)
          | Dwit s phi => (s .: rho, phi :: map (subst_form form_shift) A, map (subst_attack ↑) C)
          | Dmat _ => (rho, A, C)
          | Dfal => (rho, A, C)
          end
      end.

    Inductive oturn : state -> pmove -> state -> Prop :=
    | OAtk rho A C phi c : c ⩥ phi -> oturn (rho, A, C) (PD phi) (rho, c a:: A, c :: C)
    | OCnt rho A C a phi c : admission a = Some phi -> c ⩥ phi -> oturn (rho, A, C) (PA a) (rho, c a:: A, c :: C)
    | ODef rho A C a d : d ⥼ a -> just rho d -> oturn (rho, A, C) (PA a) (odef d (rho, A, C)).

    Inductive win s : Prop :=
    | WS s' pm : pturn s s' pm -> (forall s'', oturn s' pm s'' -> win s'') -> win s.

    Definition msat rho A phi := forall a, a ⩥ phi -> win (rho, a a:: A, [a]).
  End Rules.
  Infix "⩥" := attacks (at level 70).
  Infix "⥼" := defends (at level 70).
  Infix "a::" := acons (at level 55).
  Arguments WS {_ _ _} _ _ _ _.


  Definition mvalid A phi := forall domain (I : interp domain) (rho : env domain), msat rho A phi.

  Section Soundness.
    Inductive kprv G D : Prop :=
    | LFal : Fal el G -> kprv G D
    | Ax P v : Pred P v el G -> Pred P v el D -> kprv G D
    | LImpl phi psi : phi --> psi el G -> kprv G (phi :: D) -> kprv (psi :: G) D -> kprv G D
    | RImpl phi psi : phi --> psi el D -> kprv (phi :: G) (psi :: D) -> kprv G D
    | LConj phi psi : phi ∧ psi el G -> kprv (phi :: psi :: G) D -> kprv G D
    | RConj phi psi : phi ∧ psi el D -> kprv G (phi :: D) -> kprv G (psi :: D) -> kprv G D
    | LDisj phi psi : phi ∨ psi el G -> kprv (phi :: G) D -> kprv (psi :: G) D -> kprv G D
    | RDisj phi psi : phi ∨ psi el D -> kprv G (phi :: psi :: D) -> kprv G D
    | LAll phi t : ∀ phi el G -> kprv (phi[t .: ids] :: G) D -> kprv G D
    | RAll phi : ∀ phi el D -> kprv (map (subst_form form_shift) G) (phi :: map (subst_form form_shift) D) -> kprv G D
    | LEx phi : ∃ phi el G -> kprv (phi :: map (subst_form form_shift) G) (map (subst_form form_shift) D) -> kprv G D
    | REx phi t : ∃ phi el D -> kprv G (phi[t .: ids] :: D) -> kprv G D.
    Infix "⇒" := kprv (at level 70).

    Section Satisfaction.
      Context {domain : Type}.
      Context {I : interp domain}.

      Inductive form_equiv : env domain * form -> env domain * form -> Prop :=
      | EqFal rho rho' : form_equiv (rho, ⊥) (rho', ⊥)
      | EqPred rho rho' P v v' : Vector.map (eval rho) v = Vector.map (eval rho') v' ->
                                 form_equiv (rho, Pred P v) (rho', Pred P v')
      | EqImpl rho rho' phi psi phi' psi' : form_equiv (rho, phi) (rho', phi') -> form_equiv (rho, psi) (rho', psi') ->
                                            form_equiv (rho, phi --> psi) (rho', phi' --> psi')
      | EqConj rho rho' phi psi phi' psi' : form_equiv (rho, phi) (rho', phi') -> form_equiv (rho, psi) (rho', psi') ->
                                            form_equiv (rho, phi ∧ psi) (rho', phi' ∧ psi')
      | EqDisj rho rho' phi psi phi' psi' : form_equiv (rho, phi) (rho', phi') -> form_equiv (rho, psi) (rho', psi') ->
                                            form_equiv (rho, phi ∨ psi) (rho', phi' ∨ psi')
      | EqAll rho rho' phi phi' : (forall d, form_equiv (d .: rho, phi) (d .: rho', phi')) ->
                                  form_equiv (rho, ∀ phi) (rho', ∀ phi')
      | EqEx rho rho' phi phi' : (forall d, form_equiv (d .: rho, phi) (d .: rho', phi')) ->
                                 form_equiv (rho, ∃ phi) (rho', ∃ phi').
      Notation "p '≡' q" := (form_equiv p q) (at level 70).
      Hint Constructors form_equiv.

      Global Instance form_equiv_equiv : Equivalence form_equiv.
      Proof.
        constructor.
        - intros [rho phi]. induction phi in rho |-*; eauto.
        - induction 1; eauto.
        - intros p q r. induction 1 in r |-*; intros H''; inv H''; eauto.
          constructor; congruence.
      Qed.

      Inductive attack_equiv : env domain * (@attack domain) -> env domain * (@attack domain) -> Prop :=
      | EqAFal rho rho' : attack_equiv (rho, AFal) (rho', AFal)
      | EqAPred rho rho' P v v' : (rho, Pred P v) ≡ (rho', Pred P v') -> attack_equiv (rho, APred v) (rho', APred v')
      | EqAImpl rho rho' phi psi phi' psi' : (rho, phi) ≡ (rho', phi') -> (rho, psi) ≡ (rho', psi') ->
                                             attack_equiv (rho, AImpl phi psi) (rho', AImpl phi' psi')
      | EqAConj rho rho' phi psi phi' psi' b : (rho, phi) ≡ (rho', phi') -> (rho, psi) ≡ (rho', psi') ->
                                               attack_equiv (rho, AConj b phi psi) (rho', AConj b phi' psi')
      | EqADisj rho rho' phi psi phi' psi' : (rho, phi) ≡ (rho', phi') -> (rho, psi) ≡ (rho', psi') ->
                                             attack_equiv (rho, ADisj phi psi) (rho', ADisj phi' psi')
      | EqAAll rho rho' phi phi' s : (forall d, (d .: rho, phi) ≡ (d .: rho', phi')) ->
                                     attack_equiv (rho, AAll s phi) (rho', AAll s phi')
      | EqAEx rho rho' phi phi' : (forall d, (d .: rho, phi) ≡ (d .: rho', phi')) ->
                                  attack_equiv (rho, AEx phi) (rho', AEx phi').
      Notation "p 'a≡' q" := (attack_equiv p q) (at level 70).
      Hint Constructors attack_equiv.

      Global Instance attack_equiv_equiv : Equivalence attack_equiv.
      Proof.
        constructor.
        - intros [rho []]; eauto using (@Equivalence_Reflexive _ _ form_equiv_equiv).
        - intros ? ? []; eauto using (@Equivalence_Symmetric _ _ form_equiv_equiv).
        - intros ? ? ? []; intros H''; inv H''; eauto using (@Equivalence_Transitive _ _ form_equiv_equiv).
      Qed.

      Inductive defense_equiv : env domain * (@defense domain) -> env domain * (@defense domain) -> Prop :=
      | EqDadm rho rho' phi phi' : (rho, phi) ≡ (rho', phi') -> defense_equiv (rho, Dadm phi) (rho', Dadm phi')
      | EqDwit rho rho' phi phi' s : (forall d, (d .: rho, phi) ≡ (d .: rho', phi')) ->
                                     defense_equiv (rho, Dwit s phi) (rho', Dwit s phi')
      | EqDmat rho rho' P v v' : (rho, Pred P v) ≡ (rho', Pred P v') -> defense_equiv (rho, Dmat v) (rho', Dmat v')
      | EqDfal rho rho' : defense_equiv (rho, Dfal) (rho', Dfal).
      Notation "p 'd≡' q" := (defense_equiv p q) (at level 70).
      Hint Constructors defense_equiv.

      Global Instance defense_equiv_equiv : Equivalence defense_equiv.
      Proof.
        constructor.
        - intros [rho []]; eauto using (@Equivalence_Reflexive _ _ form_equiv_equiv).
        - intros ? ? []; eauto using (@Equivalence_Symmetric _ _ form_equiv_equiv).
        - intros ? ? ? []; intros H''; inv H''; eauto using (@Equivalence_Transitive _ _ form_equiv_equiv).
      Qed.

      Lemma form_attack_equiv rho rho' phi phi' a :
        (rho, phi) ≡ (rho', phi') -> a ⩥ phi -> exists a', a' ⩥ phi' /\ (rho, a) a≡ (rho', a').
      Proof with (split; [ unfold attacks; intuition | eauto]).
        intros H; inv H; destruct a; intros H'; inv H'.
        - exists AFal...
        - exists (APred v')...
        - exists (AImpl phi'0 psi')...
        - exists (AConj b phi'0 psi')...
        - exists (ADisj phi'0 psi')...
        - exists (AAll d phi'0)...
        - exists (AEx phi'0)...
      Qed.

      Lemma attack_equiv_admission rho rho' a a' phi :
        (rho, a) a≡ (rho', a') -> admission a = Some phi ->
        exists phi', admission a' = Some phi' /\ (rho, phi) ≡ (rho', phi').
      Proof.
        destruct a; inversion 2. inv H. exists phi'; intuition.
      Qed.

      Lemma attack_equiv_defense rho rho' a a' d :
        (rho, a) a≡ (rho', a') -> d ⥼ a -> exists d', d' ⥼ a' /\ (rho, d) d≡ (rho', d').
      Proof with split; [unfold defends; intuition | eauto].
        intros H; inv H.
        - intros ->. exists Dfal...
        - intros ->. exists (Dmat v')...
        - intros ->. exists (Dadm psi')...
        - destruct b; intros ->; [exists (Dadm phi') | exists (Dadm psi')]...
        - intros [-> | ->]; [exists (Dadm phi') | exists (Dadm psi')]...
        - intros ->. exists (Dwit s phi')...
        - intros [s ->]. exists (Dwit s phi')... now exists s.
      Qed.

      Lemma defense_equiv_just rho rho' d d' :
        (rho, d) d≡ (rho', d') -> just rho d -> just rho' d'.
      Proof.
        inversion 1; subst; cbn; eauto. inv H1. resolve_existT. now rewrite H2.
      Qed.

      Section ListEquiv.
        Variable (X Y : Type) (R : X * Y -> X * Y -> Prop).
        Context {R_equiv : Equivalence R}.

        Inductive list_equiv : X * list Y -> X * list Y -> Prop :=
        | LEBase x x' : list_equiv (x, nil) (x', nil)
        | LECons x x' y y' A A' : R (x, y) (x', y') -> list_equiv (x, A) (x', A') ->
                                  list_equiv (x, y :: A) (x', y' :: A').
        Hint Constructors list_equiv.

        Lemma list_equiv_in x x' A A' y :
          list_equiv (x, A) (x', A') -> y el A -> exists y', y' el A' /\ R (x, y) (x', y').
        Proof.
          enough (forall p q, list_equiv p q -> forall x x' A A' y, p = (x, A) -> q = (x', A') ->
                      y el A -> exists y', y' el A' /\ R (x, y) (x', y')).
          1: intros H1 H2; eapply (H _ _ H1); [ | |exact H2]; easy.
          clear x x' A A' y. intros p q; induction 1; intros ? ? ? ? ? H1 H2 Hy; inv H1; inv H2.
          1: inversion Hy. destruct Hy as [-> | Hy].
          - exists y'. intuition.
          - destruct (IHlist_equiv _ _ _ _ _ eq_refl eq_refl Hy) as (y'' & ? & ?). exists y''; intuition.
        Qed.

        Global Instance list_equiv_equiv : Equivalence list_equiv.
        Proof.
          constructor.
          - intros [rho A]; induction A; eauto using (@Equivalence_Reflexive _ _ R_equiv).
          - intros ? ?; induction 1; eauto using (@Equivalence_Symmetric _ _ R_equiv).
          - intros p q r; induction 1 in r |-*; intros H''; inv H'';
              eauto using (@Equivalence_Transitive _ _ R_equiv).
        Qed.

        Lemma list_equiv_map' x f g A :
          (forall x y, R (x, y) (f x, g y)) -> list_equiv (x, A) (f x, map g A).
        Proof.
          intros Hfg; induction A; cbn; eauto.
        Qed.

        Lemma list_equiv_map'' x x' (f g : Y -> Y) A :
          (forall y, R (x, f y) (x', g y)) -> list_equiv (x, map f A) (x', map g A).
        Proof.
          intros Hfg; induction A; cbn; eauto.
        Qed.

        Lemma list_equiv_map x x' f g A A' :
          (forall x y, R (x, y) (f x, g y)) -> list_equiv (x, A) (x', A') -> list_equiv (f x, map g A) (f x', map g A').
        Proof.
          intros Hfg H. etransitivity; [etransitivity |]. 2: exact H.
            1: symmetry. all: now apply list_equiv_map'.
        Qed.
      End ListEquiv.
      Hint Constructors list_equiv.

      Ltac transport H :=
        lazymatch type of H with
        | ?a el ?A =>
          let a' := fresh a "'" in let Ha'1 := fresh "H" a' "1" in let Ha'2 := fresh "H" a' "2" in
          lazymatch goal with
          | [H' : @list_equiv _ _ _ (_, A) _ |- _ ] => destruct (list_equiv_in H' H) as (a' & Ha'1 & Ha'2)
          end
        | ?a ⩥ ?phi =>
          let a' := fresh a "'" in let Ha'1 := fresh "H" a' "1" in let Ha'2 := fresh "H" a' "2" in
          lazymatch goal with
          | [H' : form_equiv (_, phi) _ |- _ ] => destruct (form_attack_equiv H' H) as (a' & Ha'1 & Ha'2)
          | [H' : form_equiv _ (_, phi) |- _ ] => symmetry in H'; destruct (form_attack_equiv H' H)
                                                  as (a' & Ha'1 & Ha'2)
          end
        | admission ?c = Some ?a =>
          let a' := fresh a "'" in let Ha'1 := fresh "H" a' "1" in let Ha'2 := fresh "H" a' "2" in
          lazymatch goal with
          | [H' : attack_equiv (_, c) _ |- _ ] => destruct (attack_equiv_admission H' H) as (a' & Ha'1 & Ha'2)
          | [H' : attack_equiv _ (_, c) |- _ ] => symmetry in H'; destruct (attack_equiv_admission H' H)
                                                  as (a' & Ha'1 & Ha'2)
          end
        | ?a ⥼ ?c =>
          let a' := fresh a "'" in let Ha'1 := fresh "H" a' "1" in let Ha'2 := fresh "H" a' "2" in
          lazymatch goal with
          | [H' : attack_equiv (_, c) _ |- _ ] => destruct (attack_equiv_defense H' H) as (a' & Ha'1 & Ha'2)
          | [H' : attack_equiv _ (_, c) |- _ ] => symmetry in H'; destruct (attack_equiv_defense H' H)
                                                  as (a' & Ha'1 & Ha'2)
          end
        | just ?rho ?d =>
          let H' := fresh H "'" in
          lazymatch goal with
          | [He : defense_equiv (?rho', ?d') (rho, d) |- _ ] =>
            symmetry in He; assert (H' : just rho' d') by exact (defense_equiv_just He H)
          | [He : defense_equiv (rho, d) (?rho', ?d') |- _ ] =>
            assert (H' : just rho' d') by exact (defense_equiv_just He H)
          end
        end.

      Notation "p 'A≡' q" := (list_equiv form_equiv p q) (at level 70).
      Notation "p 'C≡' q" := (list_equiv attack_equiv p q) (at level 70).

      Lemma forms_equiv_acons rho rho' a a' A A' :
        (rho, a) a≡ (rho', a') -> (rho, A) A≡ (rho', A') -> (rho, a a:: A) A≡ (rho', a' a:: A').
      Proof.
        inversion 1; subst; cbn; eauto.
      Qed.
      Hint Resolve forms_equiv_acons.

      Definition subst_equiv (p q : env domain * (nat -> term)) :=
        match p, q with
          (rho, sigma), (rho', sigma') => forall n, eval rho (sigma n) = eval rho' (sigma' n)
        end.
      Notation "p 's≡' q" := (subst_equiv p q) (at level 70).

      Lemma eval_shift rho t d :
        eval (d .: rho) (subst_term (fun x => var_term (shift x)) t) = eval rho t.
      Proof.
        induction t using strong_term_ind; comp; try congruence.
        f_equal. erewrite vec_comp. 2: intros; reflexivity. now apply vec_map_ext.
      Qed.

      Lemma subst_equiv_up_term_term rho rho' sigma sigma' d :
        (rho, sigma) s≡ (rho', sigma') -> (d .: rho, up_term_term sigma) s≡ (d .: rho', up_term_term sigma').
      Proof.
        intros H []. 1: reflexivity. cbn. unfold ">>". rewrite! eval_shift. apply H.
      Qed.

      Lemma subst_equiv_term rho rho' sigma sigma' t :
        (rho, sigma) s≡ (rho', sigma') -> eval rho t[sigma] = eval rho' t[sigma'].
      Proof.
        intros H. induction t using strong_term_ind; comp; try congruence.
        f_equal. erewrite! vec_comp. 2, 3: intros; reflexivity. now apply vec_map_ext.
      Qed.

      Lemma subst_equiv_form rho rho' sigma sigma' phi :
        (rho, sigma) s≡ (rho', sigma') -> (rho, phi[sigma]) ≡ (rho', phi[sigma']).
      Proof.
        induction phi in rho, rho', sigma, sigma' |-*; intros Hsubs; comp; eauto.
        - constructor. erewrite! vec_comp. 2, 3: intros; reflexivity. apply vec_map_ext.
          intros ? ?. now apply subst_equiv_term.
        - constructor. intros d. now apply IHphi, subst_equiv_up_term_term.
        - constructor. intros d. now apply IHphi, subst_equiv_up_term_term.
      Qed.

      Lemma subst_equiv_form_ids rho rho' sigma phi :
        (rho, ids) s≡ (rho', sigma) -> (rho, phi) ≡ (rho', phi[sigma]).
      Proof with apply subst_equiv_form.
        replace (rho, phi) with (rho, phi[ids]) by (now comp)...
      Qed.

      Lemma subst_equiv_form_sym rho rho' f sigma phi phi' :
         (forall rho, (rho, ids) s≡ (f rho, sigma)) -> (rho, phi) ≡ (rho', phi') ->
         (f rho, phi[sigma]) ≡ (f rho', phi'[sigma]).
      Proof.
        intros Hsubs Heq. etransitivity; [etransitivity|]. 2: exact Heq. 1: symmetry.
        all: now apply subst_equiv_form_ids.
      Qed.

      Lemma subst_equiv_attack rho rho' sigma sigma' a :
        (rho, sigma) s≡ (rho', sigma') -> (rho, subst_attack sigma a) a≡ (rho', subst_attack sigma' a).
      Proof.
        intros Hsubs. destruct a; constructor; eauto using subst_equiv_form.
        2, 3: intros d'; now apply subst_equiv_form, subst_equiv_up_term_term.
        change (Pred P (Vector.map (subst_term ?s) ?t)) with (subst_form s (Pred P t)).
        now apply (subst_equiv_form (Pred P t)).
      Qed.

      Lemma subst_equiv_attack_ids rho rho' sigma a :
        (rho, ids) s≡ (rho', sigma) -> (rho, a) a≡ (rho', subst_attack sigma a).
      Proof with apply subst_equiv_attack.
        setoid_rewrite subst_attack_ids at 1...
      Qed.

      Lemma subst_equiv_attack_sym rho rho' f sigma a a' :
         (forall rho, (rho, ids) s≡ (f rho, sigma)) -> (rho, a) a≡ (rho', a') ->
         (f rho, subst_attack sigma a) a≡ (f rho', subst_attack sigma a').
      Proof.
        intros Hsubs Heq. etransitivity; [etransitivity|]. 2: exact Heq. 1: symmetry.
        all: now apply subst_equiv_attack_ids.
      Qed.

      Lemma equiv_win rho A C :
        win (rho, A, C) -> forall rho' A' C', (rho, A) A≡ (rho', A') -> (rho, C) C≡ (rho', C') -> win (rho', A', C').
      Proof.
        enough (forall s, win s -> forall rho A C rho' A' C', s = (rho, A, C) -> (rho, A) A≡ (rho', A') ->
                                                   (rho, C) C≡ (rho', C') -> win (rho', A', C')).
        1: intros; eapply H; [apply H0 | | | ]; intuition. clear rho A C.
        induction 1. intros ? ? ? ? ? ? -> HA HC. inv H.
        - transport H7. transport H8. apply (WS (rho', A', C') (PA a')). apply (PAtk _ _ Hphi'1 Ha'1).
          intros ? Ho; inv Ho.
          + transport H9. transport H10. symmetry in Hc'2.
            eapply H1; [apply (OCnt _ _ _ Hphi0'1 Hc'1) | reflexivity | eauto | eauto].
          + transport H9. transport H10. destruct d; inv Hd'2; cbn.
            * symmetry in H3. eapply H1; [apply (ODef _ _ Hd'1 H10') | reflexivity | eauto | eauto].
            * eapply H1; [apply (ODef _ _ Hd'1 H10') | reflexivity | constructor; [easy | ] | ].
              all: apply list_equiv_map; [auto | | auto]; intros ? ?. 1: now apply subst_equiv_form_ids.
              now apply subst_equiv_attack_ids.
            * eapply H1; [apply (ODef _ _ Hd'1 H10') | reflexivity | eauto | eauto ].
            * eapply H1; [apply (ODef _ _ Hd'1 H10') | reflexivity | eauto | eauto ].
        - transport H5. transport H8. transport H9. apply (WS (pdef d' (rho', A', C')) (defmove d')).
          apply (PDef _ Hc'1 Hd'1 H9'). intros ? Ho; inv Ho. 2: destruct d'; discriminate H3.
          + destruct d'; try discriminate H3. all: inv Hd'2; inv H3; inv H2. 2: specialize (H7 d0).
            all: transport H4; symmetry in Hc0'2; eapply H1;
              [apply (OAtk _ _ _ Hc0'1) | reflexivity | eauto | eauto].
            1: capply forms_equiv_acons. 2: capply LECons. all: apply list_equiv_map; [auto | | auto]; intros ? ?.
            1: now apply subst_equiv_form_ids. now apply subst_equiv_attack_ids.
          + destruct d'; discriminate H3.
      Qed.

      Ltac atk a :=
        lazymatch goal with
        | |- win ?s =>
          apply (WS s (PA a)); [econstructor 1; [| reflexivity]; intuition |
                                              let Hs := fresh in intros ? Hs; inv Hs; [
                                                lazymatch goal with
                                                | [H' : admission _ = Some _ |- _ ] => inv H'
                                                end |
                                                lazymatch goal with
                                                | [H' : _ ⥼ a |- _ ] => inv H'
                                                end
                                              ]
                               ]; cbn
        end.

      Ltac probe H :=
        lazymatch goal with
        |[ H' : forall delta, delta el _ -> exists a, _ /\ _ /\ _ |- win ?s] =>
         destruct (H' _ H) as ([] & Hc & Hc2 & Hadm); inv Hc2
        end.

      Ltac def d :=
        lazymatch goal with
        | _ : ?a ⩥ _ |- win (?rho, ?A, ?C) =>
          lazymatch goal with
          | H : ?a el _ |- _ =>
            apply (WS (pdef d (rho, A, C)) (defmove d));
            [econstructor 2; [repeat right; exact H | cbn in *; try eexists; intuition | cbn in *; intuition] |
              let H'' := fresh "Hs" in intros ? H''; inv H'']
          end
        end.

      Lemma acons_sub a A :
        A <<= @acons domain a A.
      Proof. unfold acons; destruct (admission a); intuition. Qed.

      Ltac unroll_A :=
        lazymatch goal with
        | |- _ <<= _ a:: _ => etransitivity; [ | apply acons_sub]; unroll_A
        | |- ?a :: _ <<= ?a :: _ => apply incl_shift; unroll_A
        | |- map _ _ <<= map _ _ => apply incl_map; unroll_A
        | |- _ => intuition
        end.

      Ltac unroll_C HC H :=
        lazymatch type of H with
        | _ el ?d :: _ => destruct H as [<- | H]; [
                         lazymatch goal with
                         | [ H' : ?c ⩥ d  |- _ ] =>
                           exists c; repeat split; [intuition | exact H' |
                              unfold acons; intros ? ->; repeat apply acons_sub; intuition ]
                         end
                       | unroll_C HC H]
        | _ el map ?f _ =>
          let a := fresh in apply in_map_iff in H; destruct H as (? & <- & H);
          let H1 := fresh in destruct (HC _ H) as (a & ? & ? & H1); exists (subst_attack ↑ a); repeat split;
          [repeat right; now apply in_map | now apply subst_attack_attacks |
           let H2 := fresh in intros ? (? & -> & H2) % subst_attack_admission; repeat (apply acons_sub || right);
                              apply in_map; now apply H1
          ]
        | _ el nil => destruct H
        | _ el _ =>
          let H1 := fresh in let H2 := fresh in let H3 := fresh in
          destruct (HC _ H) as (H1 & ? & H2 & H3); exists H1; repeat split; [intuition | exact H2 |
           lazymatch type of H3 with
           | forall _, _ -> _ el ?A =>
             lazymatch goal with
             | |- forall _, _ -> _ el ?B =>
               let H4 := fresh in
               assert (H4 : A <<= B); [unroll_A | intros ? ?; now apply H4, H3]
             end
           end]
        end.

      Ltac use_IH IH := apply IH; [
          lazymatch goal with
          | [ HC : forall _, _ el _ -> exists _, _ /\ _ /\ _ |- _ ] =>
            let H := fresh in intros ? H; unroll_C HC H
          end | unroll_A
        ].


      Lemma satisfaction_sound G D :
        G ⇒ D -> forall rho A C,
          (forall delta, delta el D -> exists a, a el C /\ a ⩥ delta /\ forall psi, admission a = Some psi -> psi el A) ->
          G <<= A -> win (rho, A, C).
      Proof.
        induction 1; intros rho A C HC HA.
        - atk (@AFal domain). contradiction H7.
        - atk (@APred domain P v). probe H0. def (@Dmat domain P v).
        - atk (@AImpl domain phi psi); [use_IH IHkprv1 | use_IH IHkprv2].
        - probe H. def (@Dadm domain psi). use_IH IHkprv.
        - atk (@AConj domain false phi psi). atk (@AConj domain true phi psi).
          use_IH IHkprv.
        - probe H. destruct b.
          + def (@Dadm domain phi). use_IH IHkprv1.
          + def (@Dadm domain psi). use_IH IHkprv2.
        - atk (@ADisj domain phi psi); [use_IH IHkprv1 | use_IH IHkprv2].
        - probe H. def (@Dadm domain psi). def (@Dadm domain phi). use_IH IHkprv.
        - atk (@AAll domain (eval rho t) phi). shelve.
        - probe H. def (Dwit d phi). use_IH IHkprv.
        - atk (@AEx domain phi). use_IH IHkprv.
        - probe H. def (Dwit (eval rho t) phi). shelve.
        (* Equivalence transformations *) Unshelve.
        + eapply (@equiv_win rho (phi[t..] :: A) C). 1: use_IH IHkprv.
          * constructor. 1: symmetry; apply subst_equiv_form_ids; now intros [].
            apply list_equiv_map'; intros ? ?; now apply subst_equiv_form_ids.
          * apply list_equiv_map'; intros ? ?; now apply subst_equiv_attack_ids.
        + assert ((eval rho t .: rho, phi) ≡ (rho, phi[t..])) by (apply subst_equiv_form_ids; now intros []).
          transport H6. eapply (@equiv_win rho (c' a:: A) (c' :: C)). use_IH IHkprv.
          * apply forms_equiv_acons. 1: now symmetry.
            apply list_equiv_map'; intros ? ?; now apply subst_equiv_form_ids.
          * constructor. now symmetry.
            apply list_equiv_map'; intros ? ?; apply subst_equiv_attack_ids; now intros [].
      Qed.
    End Satisfaction.

    Theorem mvalid_sound G phi :
      G ⇒ [phi] -> mvalid G phi.
    Proof.
      intros Hk D I rho a Ha. apply (satisfaction_sound Hk). 2: apply acons_sub.
      intros ? [<- | []]. exists a; repeat split. 1, 2: intuition. unfold acons; now intros ? ->.
    Qed.
  End Soundness.

  Section QuasiCompleteness.
    Section Satisfaction.
      Context {domain : Type}.
      Context {I : interp domain}.
      Hypothesis (Hclass : classical I).
      Hypothesis (Hexp : exploding I).

      Definition sem_def (rho : env domain) (d : defense) :=
        match d with
        | Dadm phi => rho ⊨ phi
        | Dwit d phi => (d .: rho) ⊨ phi
        | @Dmat _ P v => rho ⊨ Pred P v
        | Dfal => rho ⊨ ⊥
        end.

      Fixpoint venv n (v : vector domain n) rho :=
        match v with
        | Vector.nil => rho
        | Vector.cons d v' => d .: venv v' rho
        end.

      Definition nshift n x := var_term (n + x).
      Lemma venv_nshift n (v : vector domain n) rho :
        forall x, eval (venv v rho) (nshift n x) = rho x.
      Proof.
        induction v; cbn; auto.
      Qed.

      Fixpoint sshift n :=
        match n with
        | O => ↑
        | S n' => up_term_term (sshift n')
        end.
      Lemma venv_sshift n (v : vector domain n) d rho :
        forall x, eval (venv v (d .: rho)) (sshift n x) = (venv v rho) x.
      Proof.
        induction v; comp. 1: reflexivity. intros [].
        reflexivity. cbn. rewrite <- IHv. unfold ">>". now rewrite eval_shift.
      Qed.

      Definition twin p :=
        match p with
          (rho, A, C) => (forall phi, phi el A -> rho ⊨ phi) -> forall n (v : vector domain n) alpha,
              (forall c d, c el C -> d ⥼ c -> sem_def rho d -> (venv v rho) ⊨ alpha) -> (venv v rho) ⊨ alpha
        end.

      Ltac build_venv :=
        lazymatch goal with
        | |- (?d .: ?rho) ⊨ _ => change (d .: rho) with (venv (Vector.cons d Vector.nil) rho)
        | |- venv _ _ ⊨ _ => idtac
        | |- ?rho ⊨ _ => change rho with (venv (Vector.nil) rho)
        end.

      Ltac use_def H a := let Hd := fresh "Hdef" in let Hd' := fresh "Hsem" in
        build_venv; refine (H a _ _ _ _ _ _); [unfold attacks; intuition | intuition
                      | intros ? ? [<- |] Hd Hd'].

      Ltac first_alpha H := eapply H; [now left | reflexivity | cbn].
      Ltac peirce := let H' := fresh "Hneg" in  apply (@Hclass _ _ ⊥); fold sat; intros H'.

      Ltac shift_goal d :=
        lazymatch type of d with
          | domain =>
          lazymatch goal with
            | |- (d .: ?rho) ⊨ subst_form ↑ ?phi => rewrite <- (@sat_subst _ _ _ (d .: rho) rho ↑ phi); [| reflexivity]
            | |- @venv ?n ?v (d .: ?rho) ⊨ subst_form (sshift ?n) ?phi =>
              erewrite <- (@sat_subst _ _ _ (venv v (d .: rho)) (venv v rho) (sshift n) phi);
              [| apply (venv_sshift v d rho)]
            | |- @venv ?n ?v ?rho ⊨ ?phi =>
              erewrite (@sat_subst _ _ _ (venv v (d .: rho)) (venv v rho) (sshift n) phi);
              [| apply (venv_sshift v d rho)]
            | |- ?rho ⊨ ?phi => rewrite (@sat_subst _ _ _ (d .: rho) rho ↑ phi); [| reflexivity]
          end
          | vector _ _ =>
            lazymatch goal with
            | |- venv ?v ?rho ⊨ subst_form (nshift ?n) ?phi => erewrite <- sat_subst; [| apply venv_nshift]
            | |- ?rho ⊨ ?phi => erewrite sat_subst; [| apply (venv_nshift d)]
            end
        end.

      Lemma twin_defend rho A C phi :
        (forall c, c ⩥ phi -> twin (rho, c a:: A, c :: C)) -> twin (rho, A, AConj true phi phi :: C).
      Proof.
        destruct phi; intros H HA n v alpha Halpha.
        - use_def H (@AFal domain). rewrite Hdef in Hsem; apply Hexp, Hsem. apply (Halpha c d); intuition.
        - use_def H (@APred domain _ t). 2: apply (Halpha c d); intuition.
          unfold defends in Hdef; subst. first_alpha Halpha. exact Hsem.
        - peirce. first_alpha Halpha. intros Hphi1'.
          use_def H (@AImpl domain phi1 phi2).
          + unfold acons in *; cbn in *; intuition; subst; intuition.
          + now rewrite Hdef in Hsem.
          + apply Hexp, Hneg. refine (Halpha c d _ Hdef Hsem). intuition.
        - assert (Hphi1 : venv v rho ⊨ (alpha ∨ subst_form (nshift n) phi1)) by
              (use_def H (@AConj domain true phi1 phi2);
          [rewrite Hdef in Hsem; right; shift_goal v; apply Hsem | left; apply (Halpha c d); intuition ]).
          assert (Hphi2 : venv v rho ⊨ (alpha ∨ subst_form (nshift n) phi2)) by
              (use_def H (@AConj domain false phi1 phi2);
          [rewrite Hdef in Hsem; right; shift_goal v; apply Hsem | left; apply (Halpha c d); intuition ]).
          destruct Hphi1, Hphi2; intuition. first_alpha Halpha. split; now shift_goal v.
        - use_def H (@ADisj domain phi1 phi2). 2: apply (Halpha c d); intuition.
          destruct Hdef as [-> | ->]; first_alpha Halpha; intuition.
        - peirce. first_alpha Halpha. intros d. use_def H (@AAll domain d phi).
          + rewrite Hdef in Hsem. apply Hsem.
          + apply Hexp, Hneg. apply (Halpha c d0); [now right | |]; intuition.
        - enough (Ha : venv v rho ⊨ (alpha ∨ subst_form (nshift n) (∃ phi))) by
            (destruct Ha; intuition; first_alpha Halpha; change (rho ⊨ ∃ phi); now shift_goal v).
          use_def H (@AEx domain phi). 2: left; apply (Halpha c d); intuition.
          destruct Hdef; subst; right; shift_goal v; eexists; exact Hsem.
      Qed.

      Ltac defend d :=
        lazymatch goal with
        | H : forall _, oturn _ (PA ?a) _ -> twin _ |- _ =>
          refine (H _ (@ODef _ _ _ _ _ a d _ _) _ _ _ _ _); [unfold defends | unfold just | |]; intuition
        end.

      Lemma halpha_shift rho n (v : vector domain n) s C alpha :
        (forall c d, c el C -> d ⥼ c -> sem_def rho d -> venv v rho ⊨ alpha) -> forall c d,
          c el map (subst_attack ↑) C -> d ⥼ c -> sem_def (s .: rho) d ->
          venv v (s .: rho) ⊨ subst_form (sshift n) alpha.
      Proof.
        setoid_rewrite in_map_iff. intros Halpha x d (c & <- & Hc) Hd Hsem.
        destruct (subst_attack_defends Hd) as (d' & -> & Hd'). shift_goal s.
        apply (Halpha c d' Hc Hd'). destruct d'.
        - now cbn in *; shift_goal s.
        - cbn in Hsem. cbn. rewrite <- (@sat_subst _ _ _ (d .: (s .: rho)) (d .: rho) (up_term_term ↑) f) in Hsem.
          2: intros []; reflexivity. easy.
        - change (sem_def rho (Dmat t)) with (rho ⊨ Pred P t). shift_goal s. apply Hsem.
        - apply Hsem.
      Qed.

      Lemma win_twin p :
        win p -> twin p.
      Proof.
        induction 1. inv H.
        - destruct a; unfold attacks in H3; cbn in H3; subst; intros HA n v alpha Halpha.
          + apply Hexp, (HA _ H2).
          + defend (@Dmat domain P t). now apply (HA (Pred P t)).
          + peirce. defend (@Dadm domain f0). destruct H3 as [<- |]. 2: intuition.
              apply (HA _ H2); fold sat. build_venv. refine (@twin_defend rho A C f _ HA _ _ _ _).
              -- intros c Hc. apply (H1 _ (@OCnt _ _ rho A C (AImpl f f0) _ _ eq_refl Hc)).
              -- intros ? ? [<- |] Hd Hd'. 1: rewrite Hd in Hd'; apply Hd'. apply Hexp, Hneg.
                 apply (Halpha c d H3 Hd Hd').
          + destruct (HA _ H2). destruct b; [defend (@Dadm domain f) | defend (@Dadm domain f0)];
            destruct H5 as [<- |]; intuition.
          + destruct (HA _ H2); [defend (@Dadm domain f) | defend (@Dadm domain f0)];
            destruct H4 as [<- |]; intuition.
          + shift_goal d. defend (@Dwit domain d f).
            * destruct H3 as [<- | H3]. 1: apply (HA _ H2). rewrite in_map_iff in H3.
              destruct H3 as (? & <- & H3). shift_goal d. apply (HA _ H3).
            * apply (halpha_shift Halpha H3 H4 H5).
          + destruct (HA _ H2) as [d H3]. shift_goal d. defend (@Dwit domain d f). 1: now exists d.
            * destruct H4 as [<- | H4]. 1: exact H3. rewrite in_map_iff in H4. destruct H4 as (? & <- & H4).
              shift_goal d. now apply (HA _ H4).
            * apply (halpha_shift Halpha H4 H5 H6).
        - intros HA n v alpha Halpha. destruct d.
          + cbn in H1. refine (@twin_defend rho A C f _ HA _ _ _ _).
            * intros a Ha. refine (H1 _ (OAtk rho A C Ha)).
            * intros ? ? [<- |]. 2: intuition. intros -> Hd. apply (Halpha c _ H2 H3 Hd).
          + cbn in H1. shift_goal d. refine (@twin_defend (d .: rho) (map (subst_form form_shift) A)
                                                (map (subst_attack form_shift) C) f _ _ _ _ _ _).
            * intros a Ha. apply (H1 _ (OAtk _ _ _ Ha)).
            * setoid_rewrite in_map_iff. intros ? (phi & <- & Hphi). shift_goal d. now apply HA.
            * intros ? ? [<- |]. 1: intros -> Hd; shift_goal d; apply (Halpha c _ H2 H3 Hd).
              apply (halpha_shift Halpha H5).
          + destruct c; cbn in H3; intuition; congruence.
          + contradiction H4.
      Qed.

      Theorem msat_ssat A phi rho :
        msat rho A phi -> (forall phi, phi el A -> rho ⊨ phi) -> rho ⊨ phi.
      Proof.
        intros Hm HA. refine (@twin_defend rho A nil phi _ HA 0 Vector.nil phi _).
        - intros c Hc; now apply win_twin, Hm.
        - now intros c d [<- | []] ->.
      Qed.
    End Satisfaction.

    Corollary mvalid_valid_L A phi :
      mvalid A phi -> valid_L exp A phi.
    Proof.
      intros Hm D I [Hexp Hclass] rho. refine (msat_ssat Hexp Hclass _). apply Hm.
    Qed.
  End QuasiCompleteness.

  Hypothesis DMforth : forall phi, kprv (phi :: nil) (DM phi :: nil).
  Hypothesis DMback : forall phi, kprv (DM phi :: nil) (phi :: nil).

  Section FragmentEquivalence.
    Context {domain : Type}.
    Context {I : interp domain}.

    Lemma Dadm_size a phi psi : a ⩥ phi -> (@Dadm domain psi) ⥼ a -> size psi < size phi.
    Proof.
      destruct a; intros <-; cbn; auto; try congruence; try destruct b.
      1-3: intros [= ->]. 4: intros [[= ->] | [= ->]]. 6: intros [? [= ->]].
      all: omega.
    Qed.

    Lemma Dwit_wf a phi s psi : a ⩥ phi -> (@Dwit domain s psi) ⥼ a -> size psi < size phi.
    Proof.
      destruct a; intros <-; cbn; try destruct b; auto; try congruence.
      1: intros []; congruence. 1: intros [= -> ->]. 2: intros [? [= -> ->]]. all: omega.
    Qed.

    Lemma admission_size a phi psi : a ⩥ phi -> @admission domain a = Some psi -> size psi < size phi.
    Proof.
      destruct a; intros <-; cbn; intros [= ->]; omega.
    Qed.

    Lemma acons_incl (c : @attack domain) C C' :
      C <<= C' -> c a:: C <<= c a:: C'.
    Proof.
      unfold acons; destruct (admission c); intuition.
    Qed.

    Definition rem phi A := remove (dec_form eq_dec_Funcs eq_dec_Preds) phi A.

    Lemma in_rem_split phi psi A :
      phi el A -> phi = psi \/ phi el rem psi A.
    Proof.
      induction A. 1: inversion 1. intros [-> | [-> | H] % IHA]; cbn. 2: now left.
      - destruct (dec_form eq_dec_Funcs eq_dec_Preds psi phi); [now left | now right].
      - destruct (dec_form eq_dec_Funcs eq_dec_Preds psi a); [now right | now (right; right)].
    Qed.

    Lemma in_triplet_split X (a b : X) A B :
      a el A ++ b :: B -> a = b \/ a el A ++ B.
    Proof.
      induction A.
      - intros [-> | H]; [now left | now right].
      - intros [-> | [-> | H] % IHA]. 1: now (right; left). 1: now left.
        right. now right.
    Qed.

    Fixpoint repshift n phi :=
      match n with
      | O => phi
      | S n' => subst_form form_shift (repshift n' phi)
      end.

    Lemma repshift_size n phi :
      size (repshift n phi) = size phi.
    Proof.
      induction n; cbn; [reflexivity | now rewrite subst_size].
    Qed.

    Lemma rem_match x A :
      rem x (x :: A) = rem x A.
    Proof.
      cbn. destruct (dec_form eq_dec_Funcs eq_dec_Preds x x). 1: reflexivity. congruence.
    Qed.

    Lemma rem_sub x A :
      rem x A <<= A.
    Proof.
      intros y. induction A.
      - easy.
      - cbn. destruct (dec_form eq_dec_Funcs eq_dec_Preds x a).
        1: intros H % IHA; now right. intros [-> | H % IHA]; [now left | now right].
    Qed.

    Lemma rem_cons x y A :
      rem x (y :: A) <<= y :: rem x A.
    Proof.
      intros z. cbn. destruct (dec_form eq_dec_Funcs eq_dec_Preds x y). 1: now right.
      intros [-> | H]; intuition.
    Qed.

    Lemma rem_acons x (a : @attack domain) A :
      rem x (a a:: A) <<= a a:: rem x A.
    Proof.
      unfold acons. destruct (admission a) eqn:H. 1: apply rem_cons. reflexivity.
    Qed.

    Lemma acons_append (a : @attack domain) A B :
      a a:: (A ++ B) = (a a:: A) ++ B.
    Proof.
      unfold acons; destruct (admission a); reflexivity.
    Qed.

    Lemma app_sub X (A B B' : list X) :
      B <<= B' -> A ++ B <<= A ++ B'.
    Proof.
      intros H ? [HA | HB] % in_app_or; apply in_or_app; [left | right]; auto.
    Qed.

    Ltac unroll_A' :=
      lazymatch goal with
      | |- _ a:: _ <<= _ a:: _ => apply acons_incl; unroll_A'
      | |- ?A ++ ?B <<= ?A ++ ?B' => apply app_sub; unroll_A'
      | |- ?a :: _ <<= ?a :: _ => apply incl_shift; unroll_A'
      | |- ?A <<= ?a :: ?A => apply incl_tl; reflexivity
      | |- ?A <<= ?a a:: ?A => apply acons_sub
      | |- map _ _ <<= map _ _ => apply incl_map; unroll_A'
      | |- _ => intuition
      end.

    Ltac unroll_A := repeat rewrite <- acons_append; repeat rewrite map_app; unroll_A'.

    Lemma win_weak rho A A' C C' :
      win (rho, A, C) -> A <<= A' -> C <<= C' -> win (rho, A', C').
    Proof.
      enough (forall p, win p -> forall rho A A' C C', p = (rho, A, C) -> A <<= A' -> C <<= C' -> win (rho, A', C')).
      1: intros Hw ? ? ; eapply (H _ Hw); [reflexivity | auto | auto ]. clear rho A A' C C'.
      intros p. induction 1. intros rho A A' C C' -> HA HC. inv H.
      - eapply (WS _ _ (PAtk rho C' (HA _ H7) H8)). intros ? Hs''; inv Hs''.
        + eapply H1. 1: apply (OCnt rho A C H9 H10). 1: reflexivity. all: unroll_A.
        + destruct d; cbn. all: eapply H1; [apply (ODef A C H9 H10) | reflexivity | unroll_A | unroll_A].
      - eapply (WS _ _ (PDef A' (HC _ H5) H8 H9)). destruct d; intros ? Hs''; inv Hs''.
        all: eapply H1; [apply (OAtk _ _ _ H10) | reflexivity | unroll_A | unroll_A].
    Qed.

    Definition win' p :=
      match p with
        (rho, A, C, phi) => forall c, c ⩥ phi -> win (rho, c a:: A, c :: C)
      end.
    Definition Cut phi :=
      forall rho A A' C, win (rho, A ++ phi :: A', C) -> win' (rho, A ++ A', C, phi) -> win (rho, A ++ A', C).

    Lemma defense_weak c rho A C A' C' :
      (forall d, d ⥼ c -> just rho d -> win (odef d (rho, A, C))) -> A <<= A' -> C <<= C' ->
      (forall d, d ⥼ c -> just rho d -> win (odef d (rho, A', C'))).
    Proof.
      intros Hd HA HC [] Hd' Hjust; cbn. all:  eapply win_weak; [apply (Hd _ Hd' Hjust) | unroll_A | unroll_A].
    Qed.

    Lemma defense_shift c s rho A C :
      (forall d, d ⥼ c -> just rho d -> win (odef d (rho, A, C))) -> (forall d, d ⥼ (subst_attack form_shift c) ->
        just (s .: rho) d -> win (odef d (s .: rho, map (subst_form form_shift) A, map (subst_attack form_shift) C))).
    Proof.
      intros Hd [] Hd' Hjust; cbn.
      - destruct (subst_attack_defends Hd') as ([] & H & Hd''); try (cbn in H; discriminate H).
        injection H; intros ->. eapply defense_equiv_just in Hjust as Hjust'.
        2: apply EqDadm; symmetry; apply subst_equiv_form_ids with (rho0 := rho); intros ?; reflexivity.
        apply (equiv_win (Hd _ Hd'' Hjust')). apply LECons. 1: apply subst_equiv_form_ids; intros x.
        2, 3: apply list_equiv_map'; intros a b. 2: apply subst_equiv_form_ids; intros x.
        3: apply subst_equiv_attack_ids; intros x. all: reflexivity.
      - destruct (subst_attack_defends Hd') as ([] & H & Hd''); try (cbn in H; discriminate H).
        injection H; intros ->. eapply defense_equiv_just in Hjust as Hjust'.
        2: apply EqDwit; intros d'; symmetry; apply subst_equiv_form_ids with (rho0 := d' .: rho);
        intros []; reflexivity. intros <-. apply (equiv_win (Hd _ Hd'' Hjust')). apply LECons.
        1: apply subst_equiv_form_ids; intros []; reflexivity. all: rewrite map_map.
        + apply list_equiv_map''. intros y; comp; apply subst_equiv_form; intros ?; reflexivity.
        + apply list_equiv_map''. intros y; comp. rewrite subst_attack_stacks. apply subst_equiv_attack.
          intros ?; reflexivity.
      - destruct (subst_attack_defends Hd') as ([] & H & Hd''); try (cbn in H; discriminate H).
        injection H; intros ? ->. resolve_existT. eapply defense_equiv_just in Hjust as Hjust'.
        2: apply EqDmat; symmetry; change (Pred P0 (Vector.map (subst_term form_shift) t0)) with
        (subst_form form_shift (Pred P0 t0)); apply subst_equiv_form_ids with (rho0 := rho) (phi := Pred P0 t0);
        intros ?; reflexivity. apply (equiv_win (Hd _ Hd'' Hjust')).
        all: apply list_equiv_map'; intros a b. 1: apply subst_equiv_form_ids; intros x.
        2: apply subst_equiv_attack_ids; intros x. all: reflexivity.
      - contradiction Hjust.
    Qed.

    Lemma attack_weak rho A C A' C' psi :
      win' (rho, A, C, psi) -> A <<= A' -> C <<= C' -> win' (rho, A', C', psi).
    Proof.
      intros Hw HA HC c Hc. eapply win_weak. apply (Hw _ Hc). all: unroll_A.
    Qed.

    Lemma attack_shift s rho A C psi :
      win' (rho, A, C, psi) ->
      win' (s .: rho, map (subst_form form_shift) A, map (subst_attack form_shift) C, subst_form form_shift psi).
    Proof.
      intros Hw c Hc. destruct (subst_attack_attack Hc) as (c' & <- & Hc').
      apply (equiv_win (Hw _ Hc')); [apply forms_equiv_acons | apply LECons].
      1, 3: apply subst_equiv_attack_ids; intros ?; reflexivity. all: apply list_equiv_map'; intros ? ?.
      1: apply subst_equiv_form_ids. 2: apply subst_equiv_attack_ids. all: intros ?; reflexivity.
    Qed.

    Section DialogicalCut.
      Variable (phi : form).
      Hypothesis (HCadm : forall c n psi, c ⩥ repshift n phi -> (@Dadm domain psi) ⥼ c -> Cut psi).
      Hypothesis (HCwit : forall c n psi d, c ⩥ repshift n phi -> (@Dwit domain d psi) ⥼ c -> Cut psi).
      Hypothesis (HCcnt : forall c n psi, c ⩥ repshift n phi -> @admission domain c = Some psi -> Cut psi).

      Lemma defense_cut rho A C1 c C2 n :
        win (rho, A, C1 ++ c :: C2) -> c ⩥ repshift n phi ->
        (forall d, d ⥼ c -> just rho d -> win (odef d (rho, A, C1 ++ C2))) -> win (rho, A, C1 ++ C2).
      Proof.
        intros H. remember (rho, A, C1 ++ c :: C2). induction H in rho, A, C1, c, C2, n, Heqp |-*.
        intros Hc Hd; subst; inv H.
        - apply (WS _ _ (PAtk rho (C1 ++ C2) H7 H8)). intros ? Hs''; inv Hs''.
          + refine (H1 _ _ rho (c0 a:: A) (c0 :: C1) c C2 n eq_refl Hc _).
            1: apply (OCnt _ _ _ H9 H10). eapply (defense_weak Hd); unroll_A.
          + destruct d; cbn. 1, 3: refine (H1 _ _ rho _ C1 c C2 n eq_refl Hc _);
            [ apply (ODef _ _ H9 H10) | eapply (defense_weak Hd); unroll_A ].
            rewrite map_app. refine (H1 _ _ _ _ _ (subst_attack form_shift c) _ (S n) eq_refl _ _).
            replace ((map (subst_attack form_shift) C1) ++ (subst_attack form_shift c) ::
                      (map (subst_attack form_shift) C2)) with (map (subst_attack form_shift) (C1 ++ c :: C2))
              by now rewrite map_app. 1: apply (ODef _ _ H9 H10). 1: cbn; now apply subst_attack_attacks.
            specialize (@defense_shift _ d _ _ _ Hd) as Hspec. eapply (defense_weak Hspec).
            2: rewrite map_app. all: unroll_A. contradiction H10.
        - destruct (in_triplet_split H5) as [-> | H6].
          + specialize (Hd _ H8 H9) as Hdef. destruct d; cbn in Hdef.
            * apply (@HCadm _ _ _ Hc H8 rho nil A _ Hdef); cbn. intros c' Hc'.
              refine (H1 _ _ rho (c' a:: A) (c' :: C1) c C2 n eq_refl Hc _).
              apply (OAtk _ _ _ Hc'). apply (defense_weak Hd); unroll_A.
            * eapply equiv_win. apply (@HCwit _ _ _ _ Hc H8 _ nil _ _ Hdef). cbn.
              intros c' Hc'. rewrite map_app. refine (H1 _ _ _ _ (c' :: map (subst_attack form_shift) C1)
              (subst_attack form_shift c) _ (S n) eq_refl _ _). cbn. replace (map (subst_attack form_shift) C1
              ++ subst_attack ↑ c :: map (subst_attack form_shift) C2) with ([subst_attack ↑ p | p ∈ (C1 ++ c :: C2)]).
              2: now rewrite map_app. apply (OAtk _ _ _ Hc'). apply (subst_attack_attacks form_shift Hc).
              eapply (defense_weak (@defense_shift _ d _ _ _ Hd)). 2: rewrite map_app. 1,2: unroll_A.
              all: cbn; symmetry; apply list_equiv_map'; intros ? ?. 1: apply subst_equiv_form_ids.
              2: apply subst_equiv_attack_ids. all: intros ?; reflexivity.
            * apply Hdef.
            * contradiction H9.
          + eapply (WS _ _ (PDef _ H6 H8 H9)). intros ? Hs''; destruct d; inv Hs''.
            * refine (H1 _ _ rho (c1 a:: A) (c1 :: C1) c C2 n eq_refl Hc _). apply (OAtk _ _ _ H11).
              apply (defense_weak Hd); cbn; unroll_A.
            * rewrite map_app. refine (H1 _ _ _ _ (c1 :: map (subst_attack form_shift) C1)
                                        (subst_attack form_shift c) (map (subst_attack form_shift) C2)
                                        (S n) eq_refl _ _).
              2: cbn; now apply subst_attack_attacks. 1: cbn; rewrite map_app; cbn; apply (OAtk _ _ _ H11).
              eapply (defense_weak (@defense_shift _ d _ _ _ Hd)). 2: rewrite map_app. all: unroll_A.
      Qed.

      Lemma attack_cut rho n A A' C :
        win (rho, A ++ repshift n phi :: A', C) -> win' (rho, A ++ A', C, repshift n phi) -> win (rho, A ++ A', C).
      Proof.
        intros H. remember (rho, A ++ repshift n phi :: A', C). induction H in rho, n, A, A', C, Heqp |-*.
        intros Hphi. inv H.
        - inv H4. clear H4. destruct (in_triplet_split H2) as [-> | H5].
          + refine (@defense_cut rho (A ++ A') nil a C n _ H3 _).
            1: specialize (Hphi _ H3) as Hspec; cbn; unfold acons in Hspec; destruct (admission a) eqn:Had.
            * eapply win_weak. apply (@HCcnt _ _ _ H3 Had _ nil _ _ Hspec); cbn.
              intros c Hc. eapply win_weak. eapply H1. eapply (OCnt _ _ _ Had Hc).
              rewrite acons_append; reflexivity. apply (attack_weak Hphi). all: unroll_A.
            * assumption.
            * intros [] Hd Hjust; cbn.
              -- eapply win_weak. eapply H1. apply (ODef _ _ Hd Hjust).
                 1: cbn; change (f :: A ++ ?E) with ((f :: A) ++ E); reflexivity.
                 apply (attack_weak Hphi). all: unroll_A.
              -- eapply win_weak. eapply H1. apply (ODef _ _ Hd Hjust).
                 1: cbn; rewrite map_app; cbn; change (f :: ?A ++ ?E) with ((f :: A) ++ E);
                 change (subst_form ?s (repshift n phi)) with (repshift (S n) phi); reflexivity.
                 apply (attack_weak (@attack_shift d _ _ _ _ Hphi)). all: unroll_A.
              -- eapply win_weak. eapply H1. apply (ODef _ _ Hd Hjust). reflexivity. apply Hphi. all: unroll_A.
              -- contradiction Hjust.
          + eapply (WS _ _ (PAtk rho C H5 H3)). intros ? Hs''; inv Hs''.
            * eapply win_weak. eapply H1. 5: reflexivity. eapply (OCnt _ _ _ H10 H11). rewrite acons_append.
              reflexivity. apply (attack_weak Hphi). all: unroll_A.
            * destruct d; cbn.
              -- eapply win_weak; [eapply H1; [eapply (ODef _ _ H10 H11) | | ] | | reflexivity].
                 1: cbn; change (f :: A ++ ?B) with ((f :: A) ++ B); reflexivity. apply (attack_weak Hphi).
                 all: unroll_A.
              -- eapply win_weak; [eapply H1; [eapply (ODef _ _ H10 H11) | | ] | | reflexivity].
                 cbn; rewrite map_app; cbn; change (f :: ?A ++ ?B) with ((f :: A) ++ B).
                 change (subst_form ?s (repshift n phi)) with (repshift (S n) phi). reflexivity.
                 apply (attack_weak (@attack_shift d _ _ _ _ Hphi)). all: unroll_A.
              -- eapply win_weak; [eapply H1; [eapply (ODef _ _ H10 H11) | | ] | | reflexivity].
                 reflexivity. apply Hphi. unroll_A.
              -- contradiction H11.
        - inv H5. eapply (WS _ _ (PDef _ H2 H3 H4)). destruct d; intros ? Hs''; inv Hs''.
          -- eapply win_weak; [eapply H1; [eapply (OAtk _ _ _ H11) | | ] | | reflexivity].
             rewrite acons_append; reflexivity. apply (attack_weak Hphi). all: unroll_A.
          -- eapply win_weak; [eapply H1; [eapply (OAtk _ _ _ H11) | | ] | | reflexivity].
             rewrite map_app, acons_append; cbn. change (subst_form ?s (repshift n phi)) with (repshift (S n) phi).
             reflexivity. apply (attack_weak (@attack_shift d _ _ _ _ Hphi)). all: unroll_A.
      Qed.
    End DialogicalCut.

    Lemma win_cut phi :
      Cut phi.
    Proof.
      induction phi using (@size_induction _ size). intros rho A A' C H1 H2.
      apply attack_cut with (phi := phi) (n := 0). 4: exact H1. 4: exact H2.
      - intros c n psi Hc Hadm. apply H. rewrite <- (repshift_size n phi). now apply (Dadm_size Hc).
      - intros c n psi d Hc Hwit. apply H. rewrite <- (repshift_size n phi). now apply (Dwit_wf Hc Hwit).
      - intros c n psi Hc Had. apply H. rewrite <- (repshift_size n phi). now apply (admission_size Hc Had).
    Qed.

    Lemma win_DM_ctx rho A C phi :
      win' (rho, A, C, phi) -> win' (rho, map DM A, C, phi).
    Proof.
      enough (forall A', win' (rho, A' ++ A, C, phi) -> win' (rho, A' ++ map DM A, C, phi)) by apply (H nil).
      induction A; cbn; intros A' H c Hc. 1: auto.
      replace (A' ++ DM a :: (map DM A)) with ((A' ++ (DM a :: nil)) ++ (map DM A)).
      2: now rewrite <- app_assoc. refine (IHA _ _ c Hc). intros c' Hc'. rewrite <- app_assoc, acons_append; cbn.
      apply (@win_cut a rho (c' a:: A') (DM a :: A) (c' :: C)). specialize (H c' Hc').
      eapply win_weak; [apply H | unroll_A | reflexivity]. intros c'' Hc''. eapply win_weak.
      apply (mvalid_sound (DMback a)). exact Hc''. all: unroll_A.
      unfold acons; destruct (admission c'); intuition.
    Qed.

    Lemma win_DM_claim rho A C phi :
      win' (rho, A, C, phi) -> win' (rho, A, C, DM phi).
    Proof.
      intros Hw c Hc. apply (@win_cut phi rho nil (c a:: A) (c :: C)); cbn.
      - eapply win_weak. apply (mvalid_sound (DMforth phi)). exact Hc.
        unfold acons; destruct (admission c). all: intuition.
      - apply (attack_weak Hw); unroll_A.
    Qed.
  End FragmentEquivalence.

  Lemma mvalid_DM A phi :
    mvalid A phi -> mvalid (map DM A) (DM phi).
  Proof.
    intros Hv D I rho. apply win_DM_claim, win_DM_ctx, Hv.
  Qed.
End MaterialDialogues.
