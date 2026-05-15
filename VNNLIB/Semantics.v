From Stdlib Require Import List.
From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference.
From Coq Require Import Strings.String.
From ONNX Require Import Syntax Semantics.
From VNNLIB Require Import Syntax.
Require Import Stdlib.Program.Equality.

Open Scope ring_scope.

(* Parameter G : NetworkDeclarations. *)
Parameter n : NetworkTheorySyntax.
Parameter n' : NetworkTheorySemantics n.

Definition InputValues (d : NetworkDeclaration) :=
  All (TensorSemantics (elementType _ n')) (typeOfInputs d).

Definition HiddenValues (d : NetworkDeclaration) :=
  All (TensorSemantics (elementType n n')) (typeOfHiddenNodes d).

Definition OutputValues (d : NetworkDeclaration) :=
  All (TensorSemantics (elementType n n')) (typeOfOutputs d).

Record NetworkVariableValues (d : NetworkDeclaration) :=
  variableValues {
      inputs : InputValues d;
      hidden : HiddenValues d;
      outputs : OutputValues d;
    }.

Definition createNetworkVariableValues {d} (i : NetworkImplementation d)
(ia : InputAssignment d) : NetworkVariableValues d :=
  match i with
  | networkImplementation network hiddenNodeMapping =>
      let inputs := All_map (fun _ => theoryTensor n n') ia in
      let hidden := All_mapf (All_map (fun x => Semantics.model n n' network inputs) hiddenNodeMapping) in
      let outputs := All_map (fun _ (x : {u : NodeOutputName n & NodeOutput n network u _})
                              => (Semantics.model n n' network inputs (projT2 x))) (modelOutputs n network) in
      variableValues d inputs hidden outputs
  end.

Definition Environment : NetworkDeclarations -> Type :=
  All (fun d : NetworkDeclaration => NetworkVariableValues d).

Definition createEnvironment {G} (xs : NetworkImplementations G) (ys : InputAssignments G) : Environment G :=
    All_zipWith (fun _ => uncurry createNetworkVariableValues) (xs, ys).

Fixpoint lookupNetwork {G} {P : NetworkDeclaration -> Type} {Q : @NetworkPredicate n} (PG : All P G) (QG : has Q G) : {d : NetworkDeclaration & P d * Q d}.
Proof.
case: G PG QG => //= d G PG;
                dependent destruction PG.
case E: (Q d) => /= QG.
by exists d.
by apply/(lookupNetwork G P Q PG QG).
Qed.

Section Decls.
Context (G : NetworkDeclarations) (D : Environment G).

Definition constant (t : ElementType n) : eqType :=
  TensorSemantics (elementType n n') (tensorType _ t (existT (fun k => {posnum nat} ^ k)%type 0%nat [tuple])).

Definition inputVar {t} (e : InputElementVariable G t) : constant t.
Proof.
case: e => shape inputNode indices.
rewrite /constant /=.
suff t' : 'nT[(elementType n n' t)]_(projT2 shape).
by apply/const_t/(\val t' indices (cast_ord prod_nil ord0)).
move: inputNode.
rewrite /InputVariable => [[/= d /andP [dinG H]]].
have H' : has (HasInputDeclarationMatching {| tensorTypes := t; tensorDims := shape |}) G.
apply/hasP.
by exists d.
have [d' [[inputs _ _]] ] := lookupNetwork D H'.
rewrite /HasInputDeclarationMatching => a.
exact: All_in a inputs.
Qed.

Definition hiddenVar {t} (e : HiddenElementVariable G t) : constant t.
Proof.
case: e => shape hiddenNode indices.
rewrite /constant /=.
suff t' : 'nT[(elementType n n' t)]_(projT2 shape).
by apply/const_t/(\val t' indices (cast_ord prod_nil ord0)).
move: hiddenNode.
rewrite /HiddenVariable => [[/= d /andP [dinG H]]].
have H' : has (HasHiddenDeclarationMatching {| tensorTypes := t; tensorDims := shape |}) G.
apply/hasP.
by exists d.
have [d' [[_ hidden _]] ] := lookupNetwork D H'.
rewrite /HasHiddenDeclarationMatching => a.
exact: All_in a hidden.
Qed.

Definition outputVar {t} (e : OutputElementVariable G t) : constant t.
Proof.
case: e => shape outputNode indices.
rewrite /constant /=.
suff t' : 'nT[(elementType n n' t)]_(projT2 shape).
by apply/const_t/(\val t' indices (cast_ord prod_nil ord0)).
move: outputNode.
rewrite /OutputVariable => [[/= d /andP [dinG H]]].
have H' : has (HasOutputDeclarationMatching {| tensorTypes := t; tensorDims := shape |}) G.
apply/hasP.
by exists d.
have [d' [[_ _ outputs]] ] := lookupNetwork D H'.
rewrite /HasOutputDeclarationMatching => a.
exact: All_in a outputs.
Qed.

Fixpoint arithExpr {t : ElementType n} (e : ArithExpr G t) {struct e} : constant t :=
  let d := (tensorType _ t (existT (fun k => {posnum nat} ^ k)%type 0%nat [tuple])) in
  let fix arithExprList {t} (op : constant t -> constant t -> constant t) (e : constant t) (es : seq (ArithExpr G t)) {struct es} : constant t :=
    match es with
    | List.nil => e
    | List.cons x xs => op (arithExpr x) (arithExprList op e xs)
    end in
  match e with
  | Syntax.constant a => theoryTensor n n' a
  | Syntax.inputVar x => inputVar x
  | Syntax.hiddenVar x => hiddenVar x
  | Syntax.outputVar x => outputVar x
  | negate x => @neg n n' d (arithExpr x)
  | add x xs => arithExprList (@Semantics.add n n' d) (arithExpr x) xs
  | sub x xs => @neg n n' d (arithExprList (@Semantics.add n n' d) (@neg n n' d (arithExpr x)) xs)
  | mul x xs => arithExprList (@Semantics.mul n n' d) (arithExpr x) xs
  end.

Definition compExpr {t} (e : CompExpr G t) : bool :=
  let d := (tensorType _ t (existT (fun k => {posnum nat} ^ k)%type 0%nat [tuple])) in
  match e with
  | greaterThan x y => @ge n n' d (arithExpr x) (arithExpr y)
  | lessThan x y => @lt n n' d (arithExpr x) (arithExpr y)
  | greaterEqual x y => @ge n n' d (arithExpr x) (arithExpr y)
  | lessEqual x y => @le n n' d (arithExpr x) (arithExpr y)
  | notEqual x y => @neq n n' d (arithExpr x) (arithExpr y)
  | equal x y => @eq n n' d (arithExpr x) (arithExpr y)
  end.

Fixpoint boolExpr (e : BoolExpr G) : bool :=
  let fix boolExprList (op : bool -> bool -> bool) (e : bool) (xs : seq (BoolExpr G)) : bool :=
    match xs with
    | List.nil => e
    | List.cons x xs => op (boolExpr x) (boolExprList op e xs)
    end in
  match e with
  | literal x => x
  | comparason t' x => compExpr x
  | and x xs => boolExprList andb (boolExpr x) xs
  | or x xs => boolExprList orb (boolExpr x) xs
  end.

Definition assertion (a : Assertion G) : bool :=
 match a with
 | assert x => boolExpr x
 end.

Definition assertionList (xs : seq (Assertion G)) : bool :=
  all assertion xs.

Definition QuerySemantics : Type :=
  forall (q : Query), @QueryModels n q -> Prop.

End Decls.

Definition query : QuerySemantics :=
  fun q m =>
match q, m with
| query networks assertions _, queryModels models _ =>
    exists (assignment : InputAssignments networks),
    assertionList networks (createEnvironment models assignment) assertions
end.

