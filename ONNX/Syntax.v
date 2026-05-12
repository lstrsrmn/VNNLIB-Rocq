From Stdlib Require Import List.
From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference.
From HB Require Import structures.

Open Scope ring_scope.

Inductive seq1 (A : Type) : Type :=
| nil1 : A -> seq1 A
| cons : A -> seq1 A -> seq1 A.

HB.howto eqType.
HB.about eqType.

Fixpoint seq1Eq {T : eqType} : rel (seq1 T) :=
  fun s1 s2 =>
  match s1, s2 with
  | nil1 x, nil1 y => x == y
  | cons x xs, cons y ys => (x == y) && seq1Eq xs ys
  | _, _ => false
  end.

HB.about hasDecEq.Build.
Definition seq1_eqP {Types : eqType} : Equality.axiom (@seq1Eq Types).
Proof.
move=> xs ys.
apply: (iffP idP).
move: xs.
elim: ys => y.
case => // x.
by rewrite /seq1Eq => /eqP ->.
move=> ys IH xs.
by case: xs => //= x xs /andP [] /eqP -> /(IH _) ->.
move=> ->.
elim: ys => //= y ys H.
apply/andP.
by split.
Qed.

HB.instance Definition _ (Types : eqType) := hasDecEq.Build (seq1 Types) seq1_eqP.

Fixpoint seq1_to_seq {T : Type} (s : seq1 T) : seq T :=
  match s with
  | nil1 x => [:: x]
  | cons x x0 => x :: seq1_to_seq x0
  end.

Coercion seq1_to_seq : seq1 >-> seq.

Fixpoint map1 {T1 T2 : Type} (f : T1 -> T2) (s : seq1 T1) : seq1 T2 :=
  match s with
  | nil1 x => nil1 T2 (f x)
  | cons x x0 => cons T2 (f x) (map1 f x0)
  end.

Section Syntax.

Record TensorType (Types : eqType) : Type :=
  tensorType {
      tensorTypes : Types;
      tensorDims : {k : nat & k.-tuple {posnum nat}};  (* ^ k}; *)
    }.

Definition TensorTypeEq {Types : eqType} : rel (TensorType Types) :=
  fun t1 t2 =>
    match t1, t2 with
    | tensorType t1 d1, tensorType t2 d2 => (t1 == t2) && (d1 == d2)
    end.

Definition TensorTypeEqP {Types : eqType} : Equality.axiom (@TensorTypeEq Types).
Proof.
move=> xs ys.
apply: (iffP idP) => [| ->].
(* move=> H. *)
case: xs.
case: ys.
by move=> t1 d1 t2 d2 /= /andP [] /eqP -> /eqP ->.
case: ys => t d.
by apply/andP.
Qed.

HB.instance Definition _ (Types : eqType) := hasDecEq.Build (TensorType Types) TensorTypeEqP.

Definition TensorShapesMatch {Types1 Types2 : eqType}
  (d1 : TensorType Types1) (d2 : TensorType Types2) : bool :=
  tensorDims _ d1 == tensorDims _ d2.

Definition InputTypes (Types : eqType) : Type :=
  seq1 (TensorType Types).

Definition HiddenNodeTypes (Types : eqType) : Type :=
  seq (TensorType Types).

Definition OutputTypes (Types : eqType) : Type :=
  seq1 (TensorType Types).

Record NetworkType (Types : eqType) : Type :=
  networkType {
      inputs : InputTypes Types;
      outputs : OutputTypes Types
    }.
(* HB.about Equality.type. *)
(* (* HB.about NetworkType. *) *)

(* HB.howto NetworkType Equality.type. *)
(* HB.about hasDecEq.Build. *)

Definition NetworkTypeEq {Types : eqType} : rel (NetworkType Types) :=
  fun n1 n2 =>
  match n1, n2 with
  | networkType inputs1 outputs1, networkType inputs2 outputs2 => (inputs1 == inputs2) && (outputs1 == outputs2)
  end.

Definition NetworkTypeEqP {Types : eqType} : Equality.axiom (@NetworkTypeEq Types).
Proof.
move=> xs ys.
apply: (iffP idP) => [| ->].
case: xs.
by case: ys => i1 o1 i2 o2 /andP [] /eqP -> /eqP ->.
case: ys => i o.
apply/andP.
by split.
Qed.

HB.instance Definition _ (Types : eqType) := hasDecEq.Build (NetworkType Types) NetworkTypeEqP.

(* TODO: Should this have some guard against mismatched lengths of inputs and outputs? *)
Definition NetworkShapesMatch {Types1 Types2 : eqType}
  (n1 : NetworkType Types1) (n2 : NetworkType Types2) : bool :=
  match n1, n2 with
    | networkType inputs1 outputs1, networkType inputs2 outputs2 =>
        all (uncurry TensorShapesMatch) (zip inputs1 inputs2) &&
          all (uncurry TensorShapesMatch) (zip outputs1 outputs2)
    end.

Definition NetworkTypesMatch {Types : eqType} (y1 : NetworkType Types)
  (y2 : NetworkType Types) : bool :=
  y1 == y2.

Record NetworkTheorySyntax := {
    ElementType : eqType;
    TheoryTensor : TensorType ElementType -> Set;
    Model : NetworkType ElementType -> Set;
    NodeOutputName : Set;
    NodeOutput : forall {y}, Model y -> NodeOutputName -> TensorType ElementType -> Type;
    modelOutputs : forall {y} (m : Model y) {d},
      In d (outputs ElementType y) -> {u : NodeOutputName & NodeOutput m u d};

    iso : forall {y1 y2}, Model y1 -> NetworkShapesMatch y1 y2 -> Model y2 -> bool;
    equal : forall {y1 y2}, Model y1 -> NetworkTypesMatch y1 y2 -> Model y2 -> bool;
  }.
End Syntax.
