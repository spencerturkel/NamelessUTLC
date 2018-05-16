Require Export NamelessUTLC.Language.

Fixpoint unshift (t: term) :=
  match t return term with
  | var n => n.-1
  | abs t => [fun unshift t]
  | app fn arg => unshift fn @ unshift arg
  end.

Theorem unshift_bounded {n t} : bounded n t -> bounded n (unshift t).
Proof. elim=> //=. move=> {n t} ? k lt. constructor. by case: k lt. Qed.

Fixpoint reduce (t: term) : seq term :=
  match t with
  | var n => [::]
  | abs t => map abs (reduce t)
  | app fn arg =>
    (if fn is abs body
     then [:: unshift (substitute (shift 1 arg) 0 body)]
     else [::]) ++ map (app ^~ arg) (reduce fn) ++ map (app fn) (reduce arg)
  end.

Fixpoint normal_step (t: term) : option term :=
  match t with
  | var n => None
  | abs t => fmap abs (normal_step t)
  | app (abs body) arg => Some (unshift (substitute (shift 1 arg) 0 body))
  | app fn arg => fmap (app ^~ arg) (normal_step fn)
  end.

Fixpoint cbn_step (t: term) : option term :=
  match t with
  | var n => None
  | abs t => None
  | app (abs body) arg => Some (unshift (substitute (shift 1 arg) 0 body))
  | app fn arg => fmap (app ^~ arg) (cbn_step fn)
  end.

Fixpoint cbv_step (t: term) : option term :=
  match t with
  | var n => None
  | abs t => None
  | app [fun body] [fun argbody] =>
    Some (unshift (substitute (shift 1 [fun argbody]) 0 body))
  | app fn arg => fmap (app ^~ arg) (cbv_step fn)
  end.

Lemma option_fmap_Some {A B f} {mx: option A} {y: B}
  : fmap f mx = Some y -> {x | mx = Some x /\ f x = y}.
Proof. case: mx => //= ?. by case. Qed.

Theorem cbv_in_reduce : forall t t', (cbv_step t == Some t') ==> (t' \in reduce t).
Proof. elim=> //= fn IHfn arg _ t.
  have H: match fn with
           | [ fun body] =>
             match arg with
             | [ fun argbody] => Some (unshift (substitute (shift 1 [ fun argbody]) 0 body))
             | _ => fmap (app^~ arg) (cbv_step fn)
             end
           | _ => fmap (app^~ arg) (cbv_step fn)
          end == Some t ->
          (exists body, fn = [fun body] /\
                   (exists argbody, arg = [fun argbody] /\
                                unshift (substitute (shift 1 [ fun argbody]) 0 body) = t))
          \/ (exists fn', cbv_step fn == Some fn' /\ fn' @ arg = t).
  {
    case: fn {IHfn} => //.
    - move=> ?. case: arg => //. move=> ?. by case/eqP.
    - move=> ? ? /eqP/option_fmap_Some-[fn' ?]. right. exists fn'. by split; [apply/eqP|].
  }
  apply/implyP.
  move/H=> {H}. case.
  - move=> [? [-> [? [-> ->]]]] /=. by rewrite in_cons eq_refl.
  - move=> [fn' [H <-]]. move/(_ fn'): IHfn. rewrite {}H /= mem_cat => ?.
    apply/orP. right. rewrite mem_cat. apply/orP. left.
    by apply: map_f.
Qed.

Corollary reduce_nil_cbv_None t : nilp (reduce t) ==> ~~ cbv_step t.
Proof. rewrite implybN. apply/implyP=> H.
  case H: (cbv_step t) H => _ //.
  move/eqP/(implyP (cbv_in_reduce _ _)): H.
  by case: (reduce t).
Qed.

Theorem cbn_in_reduce : forall t t', (cbn_step t == Some t') ==> (t' \in reduce t).
Proof. elim=> //= fn IHfn arg _ t.
  have H: (match fn with
           | [ fun body] => Some (unshift (substitute (shift 1 arg) 0 body))
           | _ => fmap (app^~ arg) (cbn_step fn)
           end == Some t) ->
          (exists body, fn = [fun body] /\ unshift (substitute (shift 1 arg) 0 body) = t)
          \/ (fmap (app^~ arg) (cbn_step fn) = Some t).
  {
    case: fn {IHfn} => //.
    - move=> ?. by case/eqP.
    - move=> fn arg'. by move/eqP/option_fmap_Some=> [? [-> <-]].
  }
  apply/implyP. move/H=> {H}. case.
  - move=> [body [-> <-]]. by rewrite in_cons eq_refl.
  - move=> H. move/option_fmap_Some: H IHfn => {t}[t [-> <-]].
    move/(_ t)/implyP/(_ (eq_refl _)) => H.
    rewrite mem_cat. apply/orP. right. rewrite mem_cat. apply/orP. left.
    by apply: map_f.
Qed.

Theorem normal_in_reduce : forall t t', (normal_step t == Some t') ==> (t' \in reduce t).
Proof. elim=> //=.
  - move=> t IH t'. apply/implyP=> /eqP/option_fmap_Some-H.
    move: H IH => [body [-> <-]] /(_ body)/implyP/(_ (eq_refl _)).
    by apply: map_f.
  - move=> fn IHfn arg IHarg t.
    have H: (match fn with
             | [ fun body] => Some (unshift (substitute (shift 1 arg) 0 body))
             | _ => fmap (app^~ arg) (normal_step fn)
             end == Some t) ->
            (exists body, fn = [fun body] /\
                     t = unshift (substitute (shift 1 arg) 0 body))
            \/ (exists fn', normal_step fn = Some fn' /\ t = app fn' arg).
    {
      case: fn IHfn => //.
      - move=> ? _. by case/eqP.
      - move=> fn arg' IHfn H.
        move: H IHfn => /eqP/option_fmap_Some-[t' [-> <-]] /(_ t').
        by rewrite eq_refl.
    }
    apply/implyP. case/H=> {H} H.
    + move: H => [? [-> ->]]. by rewrite mem_cat in_cons eq_refl.
    + move: H IHfn => [fn' [-> ->]] /(_ fn').
      rewrite eq_refl /= => /(map_f (app^~ arg)). by rewrite !mem_cat.
Qed.

Theorem reduce_nil_normal_None : forall t, nilp (reduce t) ==> ~~ normal_step t.
Proof. elim=> //=.
  - move=> t. case: (reduce t) => //=. by case: (normal_step t).
  - case=> //.
    + move=> * /=. exact: implybT.
    + move=> fn arg IHapp arg' IHarg'. apply/implyP=> H.
      case: (normal_step (fn @ arg)) IHapp => ? //.
      simpl (fmap _ _). simpl (~~ Some _). rewrite implybF.
      apply/implyP. rewrite implybF. apply/negPn.
      rewrite /cat -/cat in H. apply/nilP/size0nil.
      move/nilP: H. move/(f_equal size).
      rewrite /size -/size size_cat. move/eqP. rewrite addn_eq0 => /andP-[H _].
      move/eqP: H. by rewrite size_map.
Qed.
