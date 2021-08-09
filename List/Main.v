Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y := 
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

Compute map (fun x => x + 10) [1; 2; 3].

Definition id {X : Type} (x : X) : X := x.

Theorem map_id : forall (X : Type) (l : list X), map id l = l.
Proof.
  intros X l.
  induction l as [| x l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.

Definition compose {X Y Z : Type} (f : Y -> Z) (g : X -> Y) (x : X) : Z := f (g x).

Theorem map_comp : 
  forall (X Y Z : Type) (f : Y -> Z) (g : X -> Y) (l : list X)
  , map f (map g l) = map (compose f g) l.
Proof.
  intros X Y Z f g l.
  induction l as [| x l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. 
Qed.

Fixpoint len {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ xs => 1 + len xs
  end.

Theorem map_preserves_len :
  forall {X Y : Type} (f : X -> Y) (l : list X)
  , len (map f l) = len l.
Proof.
  intros X Y f l.
  induction l as [| x l' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.
