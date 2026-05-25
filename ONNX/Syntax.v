From Stdlib Require Import List.
From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
Require Import Stdlib.Program.Equality.
Open Scope ring_scope.

Inductive All {T : Type} (P : T -> Type) : seq T -> Type :=
| nil : All P [::]
| cons : forall {x xs}, P x -> All P xs -> All P (x :: xs).

Fixpoint All_map {T : Type} {P Q : T -> Type} (f : forall {x : T}, P x -> Q x) {xs : seq T} (H : All P xs) : All Q xs :=
  match H with
  | nil => Syntax.nil Q
  | cons x xs' Px Pxs => Syntax.cons Q (@f _ Px) (All_map (fun x => @f x) Pxs)
  end.

Fixpoint All_mapf {T U : Type} {P : U -> Type} {xs : seq T} {f : T -> U} (H : All (P \o f) xs) : All P (map f xs) :=
  match H with
  | nil => (nil P : All P [seq f i | i <- [::]])
  | cons x xs Px Pxs => Syntax.cons P Px (All_mapf Pxs)
  end.

Definition All_inv {T : Type} {P : T -> Type} {x xs}
(H : All P (x :: xs)) : P x * All P xs :=
  match H with
  | cons x xs Px Pxs => (Px, Pxs)
  end.

Lemma All_in {T : eqType} {P : T -> Type} {xs : seq T} {x : T} : x \in xs -> All P xs -> P x.
Proof.
elim: xs => //= x' xs IH.
rewrite in_cons.
case: (x == x') / eqP => [<- /= _ /All_inv [] // | _ /= H /All_inv [_]]; by apply/IH.
Qed.

Fixpoint All_zipWith {T : Type} {P Q V : T -> Type} {xs : seq T}
(f : forall {x}, (P x * Q x) -> V x)
(H : All P xs * All Q xs) {struct xs} : All V xs := (* . *)
  match xs as xs' return All P xs' * All Q xs' -> All V xs' with
  | List.cons x xs => fun H =>
      let (Px, Pxs) := All_inv H.1 in
      let (Qx, Qxs) := All_inv H.2 in
      cons V (f (Px, Qx)) (All_zipWith (fun x => @f x) (Pxs, Qxs))
  | _ => fun _ => Syntax.nil V
  end H.

Section seq1.
Definition seq1 (A : Type) := {x : seq A | (0 < size x)%nat}.
Variables (A : eqType).

Definition mem_seq1 (s : seq1 A) := mem_seq (sval s).

Definition seq1_eqclass := seq1 A.
Identity Coercion seq1_of_eqclass : seq1_eqclass >-> seq1.
Coercion pred_of_seq1 (s : seq1_eqclass) : {pred A} := mem_seq1 s.

Canonical seq1_predType := PredType (pred_of_seq1 : seq1 A -> pred A).
End seq1.

Definition seq1_to_seq {T : Type} (s : seq1 T) : seq T := sval s.

Coercion seq1_to_seq : seq1 >-> seq.

Definition map1 {T1 T2 : Type} (f : T1 -> T2) (s : seq1 T1) : seq1 T2.
case: s => x H.
exists (map f x).
by rewrite size_map.
Qed.

Section Syntax.

Record TensorType (Types : eqType) : Type :=
  tensorType {
      tensorTypes : Types;
      tensorDims : {k : nat & {posnum nat} ^ k};
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

Identity Coercion InputTypes_is_seq1 : InputTypes >-> seq1.

Definition HiddenNodeTypes (Types : eqType) : Type :=
  seq (TensorType Types).

Identity Coercion InputTypes_is_seq : HiddenNodeTypes >-> seq.

Definition OutputTypes (Types : eqType) : Type :=
  seq1 (TensorType Types).

Identity Coercion OutputTypes_is_seq1 : OutputTypes >-> seq1.

Record NetworkType (Types : eqType) : Type :=
  networkType {
      inputs : InputTypes Types;
      outputs : OutputTypes Types
    }.

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

Definition NetworkShapesMatch {Types1 Types2 : eqType}
  (n1 : NetworkType Types1) (n2 : NetworkType Types2) : bool :=
  match n1, n2 with
    | networkType inputs1 outputs1, networkType inputs2 outputs2 =>
        [&& all (uncurry TensorShapesMatch) (zip inputs1 inputs2),
          all (uncurry TensorShapesMatch) (zip outputs1 outputs2),
          (size inputs1 == size inputs2) &
          (size outputs1 == size outputs2)]
    end.

Definition NetworkTypesMatch {Types : eqType} (y1 : NetworkType Types)
  (y2 : NetworkType Types) : bool :=
  y1 == y2.

Record NetworkTheorySyntax := {
    ElementType : eqType;
    TheoryTensor : TensorType ElementType -> eqType;
    Model : NetworkType ElementType -> eqType;
    NodeOutputName : eqType;
    NodeOutput : forall {y}, Model y -> NodeOutputName -> TensorType ElementType -> eqType;
    modelOutputs : forall {y} (m : Model y),
      All (fun d => {u : NodeOutputName & NodeOutput m u d}) (outputs _ y);
      (* All (fun d => d \in (outputs ElementType y)) {u : NodeOutputName & NodeOutput m u d}; *)

    iso : forall {y1 y2}, Model y1 -> NetworkShapesMatch y1 y2 -> Model y2 -> bool;
    equal : forall {y1 y2}, Model y1 -> NetworkTypesMatch y1 y2 -> Model y2 -> bool;
  }.
End Syntax.
