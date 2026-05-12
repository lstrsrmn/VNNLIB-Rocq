From Stdlib Require Import List.
From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference.
From Coq Require Import Strings.String.
From ONNX Require Import Syntax.

Open Scope ring_scope.

Open Scope tensor_scope.

Definition Name : Set := string.

Section Decls.
Context {n : NetworkTheorySyntax}.

Record InputDeclaration :=
  declareInput {
      inputName : Name;
      inputType : TensorType (ElementType n)
    }.

Record HiddenDeclaration :=
  declareHidden {
      hiddenName : Name;
      hiddenType : TensorType (ElementType n);
      nodeOutputName : NodeOutputName n
    }.

Record OutputDeclaration :=
  declareOutput {
      outputName : Name;
      outputType : TensorType (ElementType n)
    }.
End Decls.

Module NetworkEquivalence.
Inductive NetworkEquivalence :=
| none : NetworkEquivalence
| equal_to : Name -> NetworkEquivalence
| isomorphic_to : Name -> NetworkEquivalence.
End NetworkEquivalence.
Import NetworkEquivalence.

Section Decls.
Context {n : NetworkTheorySyntax}.
Record NetworkDeclaration :=
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

Definition NetworkPredicate := NetworkDeclaration -> Prop.

Definition HasInputDeclarationMatching (type : TensorType (ElementType n)) :
  NetworkPredicate :=
  fun network : NetworkDeclaration => In type (typeOfInputs network).

Definition HasHiddenDeclarationMatching (type : TensorType (ElementType n)) :
  NetworkPredicate :=
  fun network : NetworkDeclaration => In type (typeOfHiddenNodes network).

Definition HasOutputDeclarationMatching (type : TensorType (ElementType n)) :
  NetworkPredicate :=
  fun network : NetworkDeclaration => In type (typeOfOutputs network).
End Decls.

Module ValidEqualToTarget.
Record ValidEqualToTarget {n} (name : Name) (d target : NetworkDeclaration) :=
  validEqualTo {
      targetIsNotAnEquivalence : equivalence target = none;
      targetTypesMatch : NetworkTypesMatch (typeOfNetwork d) (typeOfNetwork target);
      targetNamesMatch : name = @networkName n target;
    }.
End ValidEqualToTarget.
Import ValidEqualToTarget.
Section Decls.
Context {n : NetworkTheorySyntax}.

Record ValidIsomorphicToTarget (name : Name) (d target : NetworkDeclaration) :=
  validIsomorphicTo {
      targetIsNotAnEquivalence : equivalence target = none;
      targetShapesMatch : NetworkShapesMatch (@typeOfNetwork n d) (typeOfNetwork target);
      targetNamesMatch : name = @networkName n target
    }.

Inductive Existance {A : Type} (P : A -> Type) : seq A -> Type :=
| here : forall {x} {xs} (Px : P x), Existance P (x :: xs)
| there : forall {x} {xs} (Pxs : Existance P xs), Existance P (x :: xs).

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

Module All.
Inductive All {A : Type} (P : A -> Type) : seq A -> Type :=
| nil : All P [::]
| cons : forall {x} {xs} (px : P x) (pxs : All P xs), All P (x :: xs).
End All.
Import All.

Module All1.
Inductive All1 {A : Type} (P : A -> Type) : seq1 A -> Type :=
| nil : forall {x} (Px : P x), All1 P (nil1 _ x)
| cons : forall {x} {xs} (px : P x) (pxs : All1 P xs), All1 P (Syntax.cons _ x xs).
End All1.
Import All1.

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

Goal forall {R : realFieldType} (t : 'nT[R]_([tuple])), R.
Proof.
Proof.
move=> R t.
exact: t.[::].
Qed.

Axiom TEMP : forall {T}, T.

Axiom stupid : forall {a b : nat}, (a.+1 < b -> a < b)%nat.
Program Fixpoint dropt {T} {n} (k : 'I_n) (t : n.-tuple T) {struct k} : (n - k).-tuple T :=
  match k with
  | Ordinal m H =>
      match m with
      | 0 => (tcast (esym (subn0 n)) t)
      | S m' => TEMP (* @dropt T n (@Ordinal n m' _) (@Tuple _ _ (behead t) _) *)
      end
  end.
(* Next Obligation. *)
(* Proof. *)
(* Admitted. *)

(* Fixpoint plus (m n : nat) {struct n} : nat := *)
(*   if n is S p then S (plus m p) else m. *)

(* Axiom plus_ind : *)
(*   forall [m : nat] [P : nat -> nat -> Prop], *)
(*     (forall n p : nat, n = S p -> P p (m + p) -> P (S p) (S (m + p))) -> *)
(* (forall n _x : nat, *)
(*     n = _x -> match _x with *)
(*               | 0 => True *)
(*               | S _ => False *)
(*               end -> P _x m) -> *)
(* forall n : nat, P n (m + n). *)

(* Lemma test x y z : plus (plus x y) z = plus x (plus y z). *)
(* Proof. *)
(* elim/plus_ind: {z} (plus _ z). *)

Program Fixpoint index_tensor {n} {k : 'I_n} {R : realFieldType} {shape : n.-tuple {posnum nat}} (t : 'nT[R]_(shape))
       (index : 'I_(\prod_(i < k) (shape i)%:posnum)) : ' :=
  match 
Next Obligation.
apply (tensor_index index).
(* Next Obligation. *)
(* Proof. *)
(* elim: k shape0 t index. *)
(* move=> shape0. *)
(* rewrite tuple0. *)
(* move=> t index. *)
(* apply/tensor_nil/t. *)
(* admit. *)
(* (* by apply/(t.[::])/t. *) *)
(* move=> k IH shape t i. *)
(* apply/IH. *)
(* apply/nindex. *)
(* apply (castmx _ t). *)
(* have H := (tuple_eta shape). *)
(* apply/castmx. *)
(* shelve. *)
(* move: (cast_ord H i). *)
(* apply cast_ord. *)
(* case: shape t i H =>  /=xs Hi t i H. *)
(* rewrite -tensormx_cast in i. *)
(* apply/tensormx_cast. *)
(* apply (castmx _ t). *)
(* rewrite castmx. *)
(* shelve. *)
(* move: i. *)
(* rewrite (tuple_eta shape) /=. *)
(* rewrite big_cons => /fst i. *)
(* Unshelve. *)
(* shelve. *)
(* shelve. *)
(* case/tupleP: shape t i => /= x shape _ _. *)
(* apply/shape. *)
(* shelve. *)
(* case/tupleP: shape t => /= x shape _. *)
(* apply/x. *)
(* Unshelve. *)
(* rewrite /=. *)



  (* match k with *)
  (*   | 0 => tensor_nil t *)
  (*   | S n => index_tensor (t^^(tnth n shape)) *)
  (*   end. *)

Definition InputElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable InputVariable.

Definition HiddenElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable HiddenVariable.

Definition OutputElementVariable : NetworkDeclarations -> ElementType n -> Type :=
  ElementVariable OutputVariable.

(* TODO: Update tensor library and replace with [dims] notation *)
(* This didnt work *)
Definition NumericLiteral (t : ElementType n) :=
  TheoryTensor n (tensorType _ t (existT _ 0 ([tuple] : 0.-tuple {posnum nat}))).

Inductive ArithExpr (G : NetworkDeclarations) (t : ElementType n) :=
| constant : NumericLiteral t -> ArithExpr G t
| negate : ArithExpr G t -> ArithExpr G t
| inputVar : InputElementVariable G t -> ArithExpr G t
| hiddenVar : HiddenElementVariable G t -> ArithExpr G t
| outputVar : OutputElementVariable G t -> ArithExpr G t
| add : seq1 (ArithExpr G t) -> ArithExpr G t
| sub : seq1 (ArithExpr G t) -> ArithExpr G t
| mul : seq1 (ArithExpr G t) -> ArithExpr G t.

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
| and : seq1 (BoolExpr G) -> BoolExpr G
| or : seq1 (BoolExpr G) -> BoolExpr G.

(* TODO: This may cause issues *)
Inductive Assertion (G : NetworkDeclarations) :=
| assert : BoolExpr G -> Assertion G.

Record Query :=
  query {
      networks : NetworkDeclarations;
      assertions : seq (Assertion networks);
      equivalences : ValidNetworkEquivalences networks;
    }.

Definition CorrespondingHiddenNode
  {y} (model : Model n y) (h : HiddenDeclaration) :=
  NodeOutput n model (nodeOutputName h) (hiddenType h).

Record NetworkImplementation (d : NetworkDeclaration) :=
  networkImplementation {
      model : Model n (typeOfNetwork d);
      hiddenNodeMapping : All (CorrespondingHiddenNode model) (hiddenDeclarations d);
    }.

(* Definition NetworkImplementation (d : NetworkDeclaration) : Prop := *)
(*   (* exists model : Model n (typeOfNetwork d), Forall (CorrespondingHiddenNode model) (hiddenDeclarations d). *) *)

Definition NetworkImplementations (I : NetworkDeclarations) :=
  All NetworkImplementation I.

Program Definition ModelsEqual {name : Name} {d1 d2 : NetworkDeclaration}
  (current : NetworkImplementation d1)
  (* (pair : NetworkImplementation d2 * ValidEqualToTarget name d1 d2) *)
  (* : Prop := *)
  (* model d1 current = model d2 (fst pair). *)
(I : NetworkImplementation d2)
  (H :  ValidEqualToTarget name d1 d2)
  : Prop :=
  model d1 current = model d2 I.
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
