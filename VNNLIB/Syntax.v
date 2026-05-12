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

Record HiddenDeclaration : Type :=
  declareHidden {
      hiddenName : Name;
      hiddenType : TensorType (ElementType n);
      nodeOutputName : NodeOutputName n
    }.

Record OutputDeclaration : Type :=
  declareOutput {
      outputName : Name;
      outputType : TensorType (ElementType n)
    }.
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

Definition typeOfInputs (d : NetworkDeclaration) : InputTypes (ElementType n) :=
  map1 inputType (inputDeclarations d).

Definition typeOfHiddenNodes (d : NetworkDeclaration) : HiddenNodeTypes (ElementType n) :=
  map hiddenType (hiddenDeclarations d).

Definition typeOfOutputs (d : NetworkDeclaration) : OutputTypes (ElementType n) :=
  map1 outputType (outputDeclarations d).

Definition typeOfNetwork (d : NetworkDeclaration) : NetworkType (ElementType n) :=
  networkType _ (typeOfInputs d) (typeOfOutputs d).

Definition NetworkDeclarations := seq NetworkDeclaration.

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
End Decls.

Module ValidEqualToTarget.
Record ValidEqualToTarget {n} (name : Name) (d target : NetworkDeclaration) : Prop :=
  validEqualTo {
      targetIsNotAnEquivalence : equivalence target = none;
      targetTypesMatch : NetworkTypesMatch (typeOfNetwork d) (typeOfNetwork target);
      targetNamesMatch : name = @networkName n target;
    }.
Definition is_valid_equal_to_target {n} (name : Name) (d target : NetworkDeclaration) : bool :=
  [&& (equivalence target == none),
    NetworkTypesMatch (typeOfNetwork d) (typeOfNetwork target) &
    eqb name (@networkName n target)].
Lemma ValidEqualToTargetP  {n} name d target :
  reflect (ValidEqualToTarget name d target) (@is_valid_equal_to_target n name d target).
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

(* Pointer into the context/nn *)
Inductive ValidNetworkEquivalence (G : NetworkDeclarations)
  (d : NetworkDeclaration)
  : NetworkEquivalence -> Type :=
| none : ValidNetworkEquivalence G d none
| equal_to : forall {name}, Existance (ValidEqualToTarget name d) G ->
                       ValidNetworkEquivalence G d (equal_to name)
| isomorphic_to : forall {name}, Existance (ValidIsomorphicToTarget name d) G ->
                            ValidNetworkEquivalence G d (isomorphic_to name).
End Decls.

Module ValidNetworkEquivalences.
Inductive ValidNetworkEquivalences {n} : @NetworkDeclarations n -> Type :=
| nil : ValidNetworkEquivalences nil
| cons : forall {d ds}, ValidNetworkEquivalence ds d (equivalence d) ->
                   ValidNetworkEquivalences ds ->
                   ValidNetworkEquivalences (d :: ds).
End ValidNetworkEquivalences.
Import ValidNetworkEquivalences.
Section Decls.
Context {n : NetworkTheorySyntax}.

Definition TensorVariableType :=
  @NetworkDeclarations n -> TensorType (ElementType n) -> Set.

Definition InputVariable : TensorVariableType :=
  fun G d => Exists (HasInputDeclarationMatching d) G.

Definition HiddenVariable : TensorVariableType :=
  fun G d => Exists (HasHiddenDeclarationMatching d) G.

Definition OutputVariable : TensorVariableType :=
  fun G d => Exists (HasOutputDeclarationMatching d) G.
End Decls.

(* Indices should inhabited by something that can index the tensor *)
Section Decls.
Context {n : NetworkTheorySyntax}.
Record ElementVariable (TensorVariable : TensorVariableType)
                       (G : NetworkDeclarations)
                       (t : ElementType n) :=
  elementVar {
      shape : {k : nat & k.-tuple {posnum nat}} ;  (* ^ k}; *)
      node : TensorVariable G (tensorType _ t shape);
      (* indices : All (fun x => ordinal (x%:num)) (projT2 shape) *)
      indices : 'I_(\prod_(i <- projT2 shape) i%:posnum)
    }.

Definition InputElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable InputVariable.

Definition HiddenElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable HiddenVariable.

Definition OutputElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable OutputVariable.

(* TODO: Update tensor library and replace with [dims] notation *)
(* This didnt work *)
Definition NumericLiteral (t : ElementType n) : eqType :=
  TheoryTensor n (tensorType _ t (existT _ 0 ([tuple] : 0.-tuple {posnum nat}))).

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
| and : BoolExpr G -> seq (BoolExpr G) -> BoolExpr G
| or : BoolExpr G -> seq (BoolExpr G) -> BoolExpr G.
(* TODO: For these, I would prefer to use seq1, but I get an error I dont understand *)

(* TODO: This may cause issues *)
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

(* TODO: Check this *)
Record NetworkImplementation (d : NetworkDeclaration) : Type :=
  networkImplementation {
      model : Model n (typeOfNetwork d);
      hiddenNodeMapping : \big[prod/Set]_(i <- hiddenDeclarations d) (CorrespondingHiddenNode model i);
    }.

Definition NetworkImplementations (I : NetworkDeclarations) : Type :=
  \big[prod/Set]_(i <- I) (NetworkImplementation i).

Program Definition ModelsEqual {name : Name} {d1 d2 : NetworkDeclaration}
  (current : NetworkImplementation d1)
  (pair : NetworkImplementation d2 * ValidEqualToTarget name d1 d2)
  : bool :=
  model d1 current == model d2 pair.1.
Next Obligation.
Proof.
case: H => _.
case.
by rewrite /typeOfNetwork => -> ->.
Qed.

(* TODO: This is wrong, but I dont know what it should be for now *)
Program Definition ModelsIsomorphic {name : Name} {d1 d2 : NetworkDeclaration}
  (current : NetworkImplementation d1)
  (pair : NetworkImplementation d2 * ValidIsomorphicToTarget name d1 d2)
  := iso n (model d1 current) (_) (model d2 (fst pair)).
Next Obligation.
Proof.
by case: v => _.
Qed.

Lemma All_cons {T : Type} (P : T -> Type) (xs : seq T) (x : T) : All P (x :: xs) = (P x * All P xs)%type.
Proof.
Admitted.

Lemma lookupAny {T U : Type} {xs : seq T} {P : T -> Type} {Q : T -> Prop} :
  All P xs -> Existance Q xs -> Existance (fun x => P x * Q x)%type xs.
Proof.
Admitted.

Definition ModelsEquivalent {G} {d} (models : NetworkImplementations G)
  (i : NetworkImplementation d) {e : NetworkEquivalence}
  (abcdef : ValidNetworkEquivalence G d e) : Prop :=
  (* True. *)
match abcdef with
| none => True
| equal_to name networkVar => True (* ModelsEqual i (lookupAny models networkVar) *)
| isomorphic_to name networkVar => True  (* ModelsIsomorphic i ((iffLR (Exists_exists _ _) x)) *)
end.

End Decls.

Module ImplementationsRespectEquivalences.
Inductive ImplementationsRespectEquivalences {n : NetworkTheorySyntax} : forall {G}, ValidNetworkEquivalences G ->
                                                NetworkImplementations G -> Type :=
| nil : ImplementationsRespectEquivalences ValidNetworkEquivalences.nil (All.nil NetworkImplementation)
| cons : forall {G} {d} {e : ValidNetworkEquivalence G d (equivalence d)}
           {es : ValidNetworkEquivalences G}
           {i : NetworkImplementation d}
           {Is : NetworkImplementations G},
    ModelsEquivalent Is i e ->
ImplementationsRespectEquivalences es Is ->
ImplementationsRespectEquivalences (@ValidNetworkEquivalences.cons n _ _ e es) (All.cons _ i Is).
End ImplementationsRespectEquivalences.
Import ImplementationsRespectEquivalences.
Section Decls.
Context {n : NetworkTheorySyntax}.

Record QueryModels (q : Query) : Type :=
  queryModels {
      networkImplementations : NetworkImplementations (networks q);
      implementationsRespectEquivalences : @ImplementationsRespectEquivalences n _ (equivalences q) networkImplementations
    }.

(* Logically, this is not a predicate *)
Definition InputAssignment : NetworkDeclaration -> Type :=
  fun d => All1 (TheoryTensor n) (typeOfInputs d).

Definition InputAssignments (ds : NetworkDeclarations) :  Type :=
  All InputAssignment ds.

End Decls.
