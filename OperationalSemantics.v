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

Theorem reduce_nil_cbn_None : forall t t', (cbn_step t == Some t') ==> (t' \in reduce t).
Proof.
Admitted.