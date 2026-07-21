From Stdlib Require Import List.
From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference.
From HB Require Import structures.
From Coq Require Import Strings.String.
From ONNX Require Import Syntax.

Open Scope ring_scope.

Open Scope tensor_scope.

Definition Name : Set := string.
Identity Coercion Name_to_string : Name >-> string.

Section Decls.
Context {n : NetworkTheorySyntax}.

Record InputDeclaration : Type :=
  declareInput {
      inputName : Name;
      inputType : TensorType (ElementType n)
    }.

Definition InputDeclarationEq : rel InputDeclaration :=
  fun d1 d2 =>
match d1, d2 with
| declareInput inputName1 inputType1,
  declareInput inputName2 inputType2 =>
    eqb inputName1 inputName2 && (inputType1 == inputType2)
end.

Lemma InputDeclarationEqP : Equality.axiom InputDeclarationEq.
Proof.
move=> d1 d2.
apply: (iffP idP).
case: d1.
case: d2 => // n1 t1 n2 t2.
by rewrite /InputDeclarationEq => /andP [] /eqb_spec -> /eqP ->.
move=> <-.
case: d1 => n1 t1.
rewrite /InputDeclarationEq.
apply/andP.
split => //.
by apply/eqb_spec.
Qed.

HB.instance Definition _ := hasDecEq.Build InputDeclaration InputDeclarationEqP.

Record HiddenDeclaration : Type :=
  declareHidden {
      hiddenName : Name;
      hiddenType : TensorType (ElementType n);
      nodeOutputName : NodeOutputName n
    }.
Definition HiddenDeclarationEq : rel HiddenDeclaration :=
  fun d1 d2 =>
    match d1, d2 with
    | declareHidden hiddenName1 hiddenType1 nodeOutputName1,
      declareHidden hiddenName2 hiddenType2 nodeOutputName2 =>
        [&& eqb hiddenName1 hiddenName2,
          hiddenType1 == hiddenType2 &
          nodeOutputName1 == nodeOutputName2]
    end.

Lemma HiddenDeclarationEqP : Equality.axiom HiddenDeclarationEq.
Proof.
move=> d1 d2.
apply: (iffP idP).
case: d1.
case: d2 => // n1 t1 nn1 n2 t2 nn2.
by rewrite /InputDeclarationEq => /and3P [] /eqb_spec -> /eqP -> /eqP ->.
move=> <-.
case: d1 => n1 t1 nn1.
rewrite /InputDeclarationEq.
apply/and3P.
split => //.
by apply/eqb_spec.
Qed.

HB.instance Definition _ := hasDecEq.Build HiddenDeclaration HiddenDeclarationEqP.

Record OutputDeclaration : Type :=
  declareOutput {
      outputName : Name;
      outputType : TensorType (ElementType n)
    }.

Definition OutputDeclarationEq : rel OutputDeclaration :=
  fun d1 d2 =>
match d1, d2 with
| declareOutput outputName1 outputType1,
  declareOutput outputName2 outputType2 =>
    eqb outputName1 outputName2 && (outputType1 == outputType2)
end.

Lemma OutputDeclarationEqP : Equality.axiom OutputDeclarationEq.
Proof.
move=> d1 d2.
apply: (iffP idP).
case: d1.
case: d2 => // n1 t1 n2 t2.
by rewrite /OutputDeclarationEq => /andP [] /eqb_spec -> /eqP ->.
move=> <-.
case: d1 => n1 t1.
rewrite /OutputDeclarationEq.
apply/andP.
split => //.
by apply/eqb_spec.
Qed.

HB.instance Definition _ := hasDecEq.Build OutputDeclaration OutputDeclarationEqP.

End Decls.

Module NetworkEquivalence.
Inductive NetworkEquivalence : Set :=
| none : NetworkEquivalence
| equal_to : Name -> NetworkEquivalence
| isomorphic_to : Name -> NetworkEquivalence.

Definition NetworkEquivalenceEq : rel NetworkEquivalence :=
  fun n1 n2 =>
    match n1, n2 with
    | none, none => true
    | equal_to name1, equal_to name2 => eqb name1 name2
    | isomorphic_to name1, isomorphic_to name2 => eqb name1 name2
    | _, _ => false
    end.

Definition NetworkEquivalenceEqP : Equality.axiom NetworkEquivalenceEq.
Proof.
move=>x y.
apply: (iffP idP).
case: x;
case: y => //=;
by move=> n m => /eqb_spec ->.
move=> ->.
case: y => //=;
move=> n;
by apply/eqb_spec.
Qed.

HB.instance Definition _ := hasDecEq.Build NetworkEquivalence NetworkEquivalenceEqP.

End NetworkEquivalence.
Import NetworkEquivalence.

Section Decls.
Context {n : NetworkTheorySyntax}.
Record NetworkDeclaration : Type :=
  declareNetwork {
      networkName : Name;
      inputDeclarations : seq1 (@InputDeclaration n);
      hiddenDeclarations : seq (@HiddenDeclaration n);
      outputDeclarations : seq1 (@OutputDeclaration n);
      equivalence : NetworkEquivalence
  }.

Definition NetworkDeclarationEq : rel NetworkDeclaration :=
  fun n1 n2 =>
match n1, n2 with
| declareNetwork networkName1 inputDeclarations1
    hiddenDeclarations1 outputDeclarations1 equivalence1,
  declareNetwork networkName2 inputDeclarations2
    hiddenDeclarations2 outputDeclarations2 equivalence2 =>
    [&& eqb networkName1 networkName2,
      inputDeclarations1 == inputDeclarations2,
      hiddenDeclarations1 == hiddenDeclarations2,
      outputDeclarations1 == outputDeclarations2 &
      equivalence1 == equivalence2]
end.

Lemma NetworkDeclarationEqP : Equality.axiom NetworkDeclarationEq.
Proof.
move=> d1 d2.
apply: (iffP idP).
case: d1.
case: d2 => //.
move=> n1 i1 h1 o1 e1 n2 i2 h2 o2 e2.
rewrite /NetworkDeclarationEq => /and5P [] /eqb_spec ->.
by repeat move=> /eqP ->.
move=> <-.
case: d1 => n1 i1 h1 o1 e1.
rewrite /NetworkDeclarationEq.
apply/and5P.
split => //.
by apply/eqb_spec.
Qed.

HB.instance Definition _ := hasDecEq.Build NetworkDeclaration NetworkDeclarationEqP.

Definition typeOfInputs (d : NetworkDeclaration) : InputTypes (ElementType n) :=
  map1 inputType (inputDeclarations d).

Definition typeOfHiddenNodes (d : NetworkDeclaration) : HiddenNodeTypes (ElementType n) :=
  map hiddenType (hiddenDeclarations d).

Definition typeOfOutputs (d : NetworkDeclaration) : OutputTypes (ElementType n) :=
  map1 outputType (outputDeclarations d).

Definition typeOfNetwork (d : NetworkDeclaration) : NetworkType (ElementType n) :=
  networkType _ (typeOfInputs d) (typeOfOutputs d).

Definition NetworkDeclarations := seq NetworkDeclaration.
Identity Coercion NetworkDeclarations_to_seq : NetworkDeclarations >-> seq.

Definition NetworkPredicate := NetworkDeclaration -> bool.

Definition HasInputDeclarationMatching (type : TensorType (ElementType n)) :
  NetworkPredicate :=
  fun network : NetworkDeclaration => type \in (typeOfInputs network).

Definition HasHiddenDeclarationMatching (type : TensorType (ElementType n)) :
  NetworkPredicate :=
  fun network : NetworkDeclaration => type \in (typeOfHiddenNodes network).

Definition HasOutputDeclarationMatching (type : TensorType (ElementType n)) :
  NetworkPredicate :=
  fun network : NetworkDeclaration => type \in (typeOfOutputs network).

Definition HiddenNodePairCompatible (h1 h2 : HiddenDeclaration) : bool :=
  (nodeOutputName h1 != nodeOutputName h2) && (@hiddenType n h1 == hiddenType h2).
End Decls.

Module ValidEqualToTarget.
Section Decls.
Context {n : NetworkTheorySyntax}.
Record ValidEqualToTarget (name : Name) (d target : NetworkDeclaration) : Prop :=
  validEqualTo {
      targetIsNotAnEquivalence : equivalence target = none;
      targetTypesMatch : NetworkTypesMatch (typeOfNetwork d) (typeOfNetwork target);
      targetNamesMatch : name = @networkName n target;
      targetHiddenNodesCompatible :
      ((size (hiddenDeclarations d)) == (size (hiddenDeclarations target)))
      && all (uncurry HiddenNodePairCompatible)
           (zip (hiddenDeclarations d) (hiddenDeclarations target))
    }.

Definition is_valid_equal_to_target (name : Name) (d target : NetworkDeclaration) : bool :=
  [&& (equivalence target == none),
    NetworkTypesMatch (typeOfNetwork d) (typeOfNetwork target),
    eqb name (@networkName n target),
    size (hiddenDeclarations d) == size (hiddenDeclarations target) &
     all (uncurry HiddenNodePairCompatible)
       (zip (hiddenDeclarations d) (hiddenDeclarations target))].

Lemma ValidEqualToTargetP  name d target :
  reflect (ValidEqualToTarget name d target) (is_valid_equal_to_target name d target).
Proof.
apply: (iffP idP) => [ /and5P [H1 H2 H3 H4 H5] | [H1 H2 H3 /andP [H4 H5]]].
  split => //.
  - by apply/eqP.
  - by apply/eqb_spec.
  - apply/andP.
    by split.
apply/and5P.
split => //.
by apply/eqP.
by apply/eqb_spec.
Qed.
End Decls.
End ValidEqualToTarget.
Import ValidEqualToTarget.
Section Decls.
Context {n : NetworkTheorySyntax}.

(* TODO: Drop to bool *)
Record ValidIsomorphicToTarget (name : Name) (d target : NetworkDeclaration) : Prop :=
  validIsomorphicTo {
      targetIsNotAnEquivalence : equivalence target = none;
      targetShapesMatch : NetworkShapesMatch (@typeOfNetwork n d) (typeOfNetwork target);
      targetNamesMatch : name = @networkName n target
    }.

Definition is_valid_isomorphic_to_target (name : Name)
  (d target : NetworkDeclaration) : bool :=
  [&& (equivalence target == none),
    NetworkShapesMatch (@typeOfNetwork n d) (typeOfNetwork target) &
    eqb name (@networkName n target)].

Lemma ValidIsomorphicToTargetP name d target :
  reflect (ValidIsomorphicToTarget name d target) (is_valid_isomorphic_to_target name d target).
Proof.
apply: (iffP idP) => [ /and3P [H1 H2 H3] | [H1 H2 H3] ].
split => //.
by apply/eqP.
by apply/eqb_spec.
apply/and3P.
split => //.
by apply/eqP.
by apply/eqb_spec.
Qed.

Inductive ValidNetworkEquivalence (G : NetworkDeclarations)
  (d : NetworkDeclaration)
  : NetworkEquivalence -> Type :=
| none : ValidNetworkEquivalence G d none
| equal_to : forall {name}, has (is_valid_equal_to_target name d) G ->
                       ValidNetworkEquivalence G d (equal_to name)
| isomorphic_to : forall {name}, has (is_valid_isomorphic_to_target name d) G ->
                            ValidNetworkEquivalence G d (isomorphic_to name).
End Decls.

Module ValidNetworkEquivalences.
Inductive ValidNetworkEquivalences {n} : @NetworkDeclarations n -> Type :=
| nil : ValidNetworkEquivalences [::]
| cons : forall {d ds}, ValidNetworkEquivalence ds d (equivalence d) ->
                   ValidNetworkEquivalences ds ->
                   ValidNetworkEquivalences (d :: ds).
End ValidNetworkEquivalences.
Import ValidNetworkEquivalences.
Section Decls.
Context {n : NetworkTheorySyntax}.

Definition TensorVariableType :=
  @NetworkDeclarations n -> TensorType (ElementType n) -> eqType.

Definition InputVariable : TensorVariableType :=
  fun G d => {d' : NetworkDeclaration | (d' \in G) && HasInputDeclarationMatching d d'}.

Definition HiddenVariable : TensorVariableType :=
  fun G d => {d' : NetworkDeclaration | (d' \in G) && HasHiddenDeclarationMatching d d'}.
Definition OutputVariable : TensorVariableType :=
  fun G d => {d' : NetworkDeclaration | (d' \in G) && HasOutputDeclarationMatching d d'}.
End Decls.

Section Decls.
Context {n : NetworkTheorySyntax}.

Record ElementVariable (TensorVariable : TensorVariableType)
                       (G : NetworkDeclarations)
                       (t : ElementType n) :=
  elementVar {
      shape : {k : nat & {posnum nat}^k} ;  (* ^ k}; *)
      node : TensorVariable G (tensorType _ t shape);
      indices : 'I_(\prod_(i < projT1 shape) ((projT2 shape) i)%:posnum)
    }.

Definition InputElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable InputVariable.

Definition HiddenElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable HiddenVariable.

Definition OutputElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable OutputVariable.

(* TODO: Update tensor library and replace with [dims] notation *)
(* This didnt work *)
Local Notation "[ 'dims' ]" := (finfun_of_tuple [tuple]).
Definition NumericLiteral (t : ElementType n) : eqType :=
  (* TheoryTensor n (tensorType _ t (existT _ 0 [tuple])). *)
(* TheoryTensor n (tensorType _ t (existT _ 0 (finfun_of_tuple [tuple]))). *)
  TheoryTensor n (tensorType _ t (existT _ 0 [dims])).

Inductive ArithExpr (G : NetworkDeclarations) (t : ElementType n) :=
| constant : NumericLiteral t -> ArithExpr G t
| negate : ArithExpr G t -> ArithExpr G t
| inputVar : InputElementVariable G t -> ArithExpr G t
| hiddenVar : HiddenElementVariable G t -> ArithExpr G t
| outputVar : OutputElementVariable G t -> ArithExpr G t
| add : ArithExpr G t -> seq (ArithExpr G t) -> ArithExpr G t
| sub : ArithExpr G t -> seq (ArithExpr G t) -> ArithExpr G t
| mul : ArithExpr G t -> seq (ArithExpr G t) -> ArithExpr G t.

Inductive CompExpr (G : NetworkDeclarations) (t : ElementType n) :=
| greaterThan : ArithExpr G t -> ArithExpr G t -> CompExpr G t
| lessThan : ArithExpr G t -> ArithExpr G t -> CompExpr G t
| greaterEqual : ArithExpr G t -> ArithExpr G t -> CompExpr G t
| lessEqual : ArithExpr G t -> ArithExpr G t -> CompExpr G t
| notEqual : ArithExpr G t -> ArithExpr G t -> CompExpr G t
| equal : ArithExpr G t -> ArithExpr G t -> CompExpr G t.

Inductive BoolExpr (G : NetworkDeclarations) :=
| literal : bool -> BoolExpr G
| comparason : forall {t}, CompExpr G t -> BoolExpr G
(* | and : seq1 (BoolExpr G) -> BoolExpr G *)
| and : BoolExpr G -> seq (BoolExpr G) -> BoolExpr G
(* | or : seq1 (BoolExpr G) -> BoolExpr G. *)
| or : BoolExpr G -> seq (BoolExpr G) -> BoolExpr G.
(* TODO: For these, I would prefer to use seq1, but I get an error I dont understand *)

Inductive Assertion (G : NetworkDeclarations) : Type :=
| assert : BoolExpr G -> Assertion G.

Record Query : Type :=
  query {
      networks : NetworkDeclarations;
      assertions : seq (Assertion networks);
      equivalences : ValidNetworkEquivalences networks;
    }.

Definition CorrespondingHiddenNode
  {y} (model : Model n y) (h : HiddenDeclaration) : Type :=
  NodeOutput n model (nodeOutputName h) (hiddenType h).

Record NetworkImplementation (d : NetworkDeclaration) : Type :=
  networkImplementation {
      model : Model n (typeOfNetwork d);
      hiddenNodeMapping : forall i : 'I_(size (hiddenDeclarations d)),
        CorrespondingHiddenNode model (tnth (in_tuple (hiddenDeclarations d)) i);
    }.

Definition NetworkImplementations (I : NetworkDeclarations) : Type :=
  forall i : 'I_(size I), NetworkImplementation (tnth (in_tuple I) i).

Definition ModelsEqual {name : Name} {d1 d2 : NetworkDeclaration}
  (current : NetworkImplementation d1)
  (pair : NetworkImplementation d2 * ValidEqualToTarget name d1 d2)
  : bool :=
  Syntax.equal n (model d1 current) (targetTypesMatch _ _ _ pair.2) (model d2 pair.1).

Definition ModelsIsomorphic {name : Name} {d1 d2 : NetworkDeclaration}
  (current : NetworkImplementation d1)
  (pair : NetworkImplementation d2 * ValidIsomorphicToTarget name d1 d2)
  : bool := iso n (model d1 current) (targetShapesMatch _ _ _ pair.2) (model d2 (fst pair)).

Fixpoint find_implementation (G : NetworkDeclarations) (I : NetworkImplementations G) (d : NetworkDeclaration) (H : d \in G)
                          : NetworkImplementation d.
(*   := *)
(* match G with *)
(* | List.nil => False_rect _ _ *)
(* | List.cons x xs => *)
(*     match x == d as H' with *)
(*     | true => _ *)
(*     | false => find_implementation xs _ d H *)
(*     end *)
(* end. *)
(* (* Obligations. *) *)

Proof.
elim: G H I => // d' G' IH.
rewrite in_cons.
case E: (d == d').
move=> /= _ H.
move/eqP: E ->.
by have := H ord0; rewrite (tnth_nth d').
move=> /= H' H.
apply: (IH H') => i.
by have := H (lift ord0 i); rewrite !(tnth_nth d').
Qed.

Definition ModelsEquivalent {G} {d} (models : NetworkImplementations G)
  (i : NetworkImplementation d) {e : NetworkEquivalence}
  (v : ValidNetworkEquivalence G d e) : bool.
Proof.
case: v.
exact: true.
move=> name networkVar.
have d1 := nth d G (find (is_valid_equal_to_target name d) G).
have/ValidEqualToTargetP P := nth_find d1 networkVar.
apply/(ModelsEqual i (_, P)).
apply/(find_implementation G models).
apply/mem_nth.
by rewrite -has_find.
move=> name networkVar.
have d1 := nth d G (find (is_valid_isomorphic_to_target name d) G).
have/ValidIsomorphicToTargetP P := nth_find d1 networkVar.
apply/(ModelsIsomorphic i (_, P)).
apply/(find_implementation G models).
apply/mem_nth.
by rewrite -has_find.
Qed.
End Decls.

(* At every position of the equivalence telescope, the declared equivalence *)
(* holds of the corresponding model, relative to the models of the          *)
(* remaining declarations.                                                  *)
Fixpoint ImplementationsRespectEquivalences {n : NetworkTheorySyntax}
    {G : @NetworkDeclarations n} (es : ValidNetworkEquivalences G) {struct es} :
    NetworkImplementations G -> Type.
Proof.
case: G / es => [|d ds e es'].
  exact (fun _ : NetworkImplementations [::] => unit).
move=> Is.
have Ids : NetworkImplementations ds.
  by move=> i; have := Is (lift ord0 i); rewrite !(tnth_nth d).
exact: ((ModelsEquivalent Ids (Is ord0) e) *
        (ImplementationsRespectEquivalences n ds es' Ids))%type.
Defined.
Section Decls.
Context {n : NetworkTheorySyntax}.

Record QueryModels (q : Query) : Type :=
  queryModels {
      networkImplementations : NetworkImplementations (networks q);
      implementationsRespectEquivalences : @ImplementationsRespectEquivalences n _ (equivalences q) networkImplementations
    }.

(* Logically, this is not a predicate *)
Definition InputAssignment (d : NetworkDeclaration) : Type :=
  forall i : 'I_(size (typeOfInputs d)),
    TheoryTensor n (tnth (in_tuple (typeOfInputs d)) i).

Definition InputAssignments (ds : NetworkDeclarations) : Type :=
  forall i : 'I_(size ds), InputAssignment (tnth (in_tuple ds) i).

End Decls.
