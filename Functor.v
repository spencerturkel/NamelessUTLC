Require Export Coq.Classes.Morphisms.

Require Export NamelessUTLC.Core.

Class FunctorMap (F: Type -> Type) := fmap: forall {A B}, (A -> B) -> F A -> F B.
Arguments fmap F FunctorMap A B f !x /.

Unset Implicit Arguments.
Class Functor (F: Type -> Type) `{FunctorMap_F: FunctorMap F}
      `{Proper_fmap: forall {A B}, Proper ((@eqfun B A) ==> eq ==> eq) fmap} :=
  { fmap_id: forall {A}, left_id (@id A) fmap;
    fmap_comp: forall {A B C} (f: B -> C) (g: A -> B) x, fmap f (fmap g x) = fmap (f \o g) x }.

Lemma comp_rw : forall {A B C} {f: B -> C} {g: A -> B} {x}, f (g x) = (f \o g) x.
Proof. done. Qed.

Instance option_FunctorMap : FunctorMap option := omap.

Instance omap_proper {A B} : Proper ((@eqfun B A) ==> eq ==> eq) (@omap A B).
Proof. move=> f g eq x y {y} <-. by case: x => /=. Qed.

Instance option_Functor : Functor option.
Proof. split.
  - move=> ?. by case.
  - move=> ? ? ? ? ?. by case.
Qed.

Instance const_FunctorMap A : FunctorMap (fun _ => A) := fun _ _ _ => id.

Instance const_fmap_Proper A B C : Proper (@eqfun B C ==> @eq A ==> @eq A) (fun _ => id).
Proof. by move=> _ _ _ ? _ <-. Qed.

Instance const_Functor A : Functor (fun _ => A).
Proof. split.
  - move=> ? ?. by rewrite /fmap /const_FunctorMap.
  - move=> *. by rewrite /fmap /const_FunctorMap.
Qed.
