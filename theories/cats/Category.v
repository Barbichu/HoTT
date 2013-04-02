(** Categories, by Cyril Cohen <cohen@crans.org>
  and Benedikt Ahrens <benedikt.ahrens@gmx.net> *)

Require Import HoTT.

Set Implicit Arguments.
(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

Delimit Scope cat_scope with cat.

Section HSet.

Polymorphic Record HSet := mkHSet {
  HSetType :> Type;
  _ : IsHSet HSetType
}.

Global Instance HSetP (S : HSet) : IsHSet S.
Proof. by case S. Qed.

End HSet.

Section PrecatDefs.

Polymorphic Record precat_mixin_of {obj : Type} (hom : obj -> obj -> Type) := 
  PrecatMixin {
  hom_refl_op : forall x, hom x x
    where "1" := (@hom_refl_op _);
  hom_comp_op : forall x y z, hom x y -> hom y z -> hom x z
    where "f * g" := (@hom_comp_op _ _ _ f g);
  _ : forall x y, IsHSet (hom x y);
  _ : forall x y (f : hom x y), 1 * f = f;
  _ : forall x y (f : hom x y), f * 1 = f;
  _ : forall x y z t (f : hom x y) (g : hom y z) (h : hom z t), 
        f * (g * h) = (f * g) * h
}.
Arguments PrecatMixin {obj hom _ _} _ _ _ _.

Definition precat_class_of := @precat_mixin_of.
Arguments precat_class_of {obj} hom.

Polymorphic Record precat := Precat {
  obj :> Type;
  hom :> obj -> obj -> Type;
  _ : precat_class_of hom
}.

Definition precat_class (C : precat) : precat_class_of (hom C) :=
  match C with Precat _ _ c => c end.

End PrecatDefs.

Definition hom_refl {C : precat} := hom_refl_op (precat_class C).
Definition hom_comp {C : precat} := hom_comp_op (precat_class C).
Arguments hom_comp {C x y z} _ _.

Local Open Scope cat_scope.
Notation "1" := (@hom_refl _ _) : cat_scope.
Notation "f * g" := (hom_comp f g) : cat_scope.
Arguments PrecatMixin {obj hom _ _} _ _ _ _.
Arguments precat_class_of {obj} hom.

Section PrecatTheory.

Implicit Type C : precat.

Lemma hom_IsHSet {C} (x y : C) : IsHSet (C x y).
Proof. by revert x y; case C; intros C0 CHom []. Qed.

Definition hSet_hom {C} (x y : C) :=
  @mkHSet (C x y) (@hom_IsHSet C x y).
(* BUG: Cannot make this a Canonical Structure man ! *)
(* Canonical Structure hSet_hom. *)

Lemma comp1c {C} x y (f : C x y) : 1 * f = f.
Proof. by revert x y f; case C; intros ? ? []. Qed.

Lemma compc1 {C} x y (f : C x y) : f * 1 = f.
Proof. by revert x y f; case C; intros ? ? []. Qed.

Lemma compcA {C} x y z t (f : C x y) (g : C y z) (h : C z t) :
  f * (g * h) = (f * g) * h.
Proof. by revert x y z t f g h; case C; intros ? ? []. Qed.

Definition is_iso {C} {x y} (f : C x y) := {g | f * g = 1 /\ g * f = 1}.
Definition iso {C} x y := {f : C x y | is_iso f}.

End PrecatTheory.

(* Definition homtype (C : precat) := {x : C * C & hom x.1 x.2}. *)
(* Definition refl_hom (C : precat) (x : C) : homtype C := ((x, x); 1). *)
(* Definition to_hom (C : precat) (x y : C) (f : C x y) : homtype C := ((x, y); f). *)

Section FuncPrecat.
Context {C D : precat}.
Context `{funext : Funext}.

Record functor := Functor {
  functor_obj :> C -> D;
  functor_hom : forall {x y} (h : C x y), D (functor_obj x) (functor_obj y);
  _ : forall x, functor_hom (1 : C x x) = 1;
  _ : forall x y z (h : C x y) (k : C y z),
      functor_hom (h * k) = (functor_hom h) * (functor_hom k)
}.
Notation "F ^*" := (@functor_hom F _ _) (at level 2, format "F ^*").
Notation "C --> D" := (functor C D)
  (at level 99, D at level 200, format "C --> D").

Definition is_nattrans {F G : functor} (u : forall x : C, D (F x) (G x)) := 
  forall x y (f : C x y), (F^* f) * (u y) = (u x) * (G^* f).

Lemma is_nattrans_IsHProp (F G : functor) (u : forall x : C, D (F x) (G x)) :
  IsHProp (is_nattrans u).
Proof.
apply hprop_forall; intro x.
apply hprop_forall; intro y.
apply hprop_forall; intro f.
by simpl; apply hom_IsHSet.
Qed.
(* Canonical is_nattrans_HProp : HProp := .... *)

Record nattrans (F G : functor) := NatTrans {
  nattrans_fun :> forall x : C, D (F x) (G x);
  _ : is_nattrans nattrans_fun
}.
(* Canonical nattrans_subType := [subType of nattrans by nattrans_rect]. *)

Lemma nattransP (F G : functor) (u : nattrans F G) : is_nattrans u.
Proof. by case u. Qed.

Definition id_nattrans (F : functor) := (fun x => 1 : D (F x) (F x)).

Lemma id_is_nattrans F x y (f : C x y) : (F^* f) * 1 = 1 * (F^* f).
Proof. by rewrite compc1, comp1c. Qed.

Definition nattrans_id F :=
  @NatTrans F F (id_nattrans F) (id_is_nattrans _).
(* Canonical Structure nattrans_id. (* Mouahah *) *)

Definition comp_nattrans F G H (u : nattrans F G) (v : nattrans G H) :=
  fun x : C => u x * v x.  

Lemma comp_is_nattrans F G H (u : nattrans F G) (v : nattrans G H) :
  is_nattrans (comp_nattrans u v).
Proof.
intros x y f; unfold comp_nattrans.
by rewrite <- compcA, <- nattransP, 2 compcA, nattransP.
Qed.

Definition nattrans_comp F G H (u : nattrans F G) (v : nattrans G H) :=
  @NatTrans F H (comp_nattrans u v) (comp_is_nattrans _ _).
(* Canonical Structure nattrans_comp. (* Mouahah *) *)

Lemma nattrans_eq F G (u v : nattrans F G) :
   (forall x, u x = v x) -> u = v.
Proof.
intro eq_uv; apply funext in eq_uv.
(* apply: val_inj. *)
Admitted.

Lemma comp_1_nattrans F G (u : nattrans F G) :
  nattrans_comp (nattrans_id _) u = u.
Proof. by apply nattrans_eq; intro a; apply comp1c. Qed.

Lemma comp_nattrans_1 F G (u : nattrans F G) :
  nattrans_comp u (nattrans_id _) = u.
Proof. by apply nattrans_eq; intro a; apply compc1. Qed.

Lemma comp_nattransA F G H I
  (u : nattrans F G) (v : nattrans G H) (w : nattrans H I) :
  nattrans_comp u (nattrans_comp v w) = nattrans_comp (nattrans_comp u v) w.
Proof. by apply nattrans_eq; intro a; apply compcA. Qed.

Lemma nattrans_isset F G : IsHSet (nattrans F G).
Proof. Admitted.

Definition functor_precatMixin : precat_mixin_of nattrans
  := PrecatMixin nattrans_isset comp_1_nattrans comp_nattrans_1 comp_nattransA.
Definition functor_precat := @Precat functor nattrans functor_precatMixin.
(* Canonical Structure functor_precat. *)

End FuncPrecat.

Notation "F ^*" := (@functor_hom _ _ F _ _) (at level 2, format "F ^*").
Notation "C --> D" := (@functor _ _ C D)
  (at level 99, D at level 200, format "C --> D").

Section CatDefs.

Definition saturated (C : precat) := forall x y : C, iso x y -> x = y.

End CatDefs.