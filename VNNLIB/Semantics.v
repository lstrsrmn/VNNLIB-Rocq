From Stdlib Require Import List.
From mathcomp Require Import all_boot all_algebra all_order.
From mathcomp Require Import interval_inference.
From Coq Require Import Strings.String.
From ONNX Require Import Syntax Semantics.
From VNNLIB Require Import Syntax.

Open Scope ring_scope.

(* Parameter G : NetworkDeclarations. *)
Parameter n : NetworkTheorySyntax.
Parameter n' : NetworkTheorySemantics n.
Import All1.
Import All.

Definition InputValues (d : NetworkDeclaration) :=
  All1 (TensorSemantics (elementType _ n')) (typeOfInputs d).

Definition HiddenValues (d : NetworkDeclaration) :=
  All (TensorSemantics (elementType n n')) (typeOfHiddenNodes d).

Definition OutputValues (d : NetworkDeclaration) :=
  All1 (TensorSemantics (elementType n n')) (typeOfOutputs d).

Record NetworkVariableValues (d : NetworkDeclaration) :=
  variableValues {
      inputs : InputValues d;
      hidden : HiddenValues d;
      outputs : OutputValues d;
    }.

Definition mapAll1 {A B : Type} (f : A -> B) (xs : seq1 A) (a : All 

Definition CreateNetworkVariableValues {d} (i : NetworkImplementation d)
  (ia : InputAssignment d) : NetworkVariableValues d :=
match i with
| networkImplementation network hiddenNodeMapping =>
    let inputs := map1 (theoryTensor n n') ia in
    let hidden := map (map1 (model network inputs) hiddenNodeMapping) in
    let outputs := map (fun u z => model network inputs z) (modelOutputs network) in
    variableValues inputs hidden outputs
end.


createNetworkVariableValues :
  NetworkImplementation d →
  InputAssignment d →
  NetworkVariableValues d 
createNetworkVariableValues (networkImplementation network hiddenNodeMapping) inputs = do
  let ⟦inputs⟧ = All⁺.map ⟦theoryTensor⟧ inputs
  let ⟦hidden⟧ = All.map⁺ (All.map (⟦model⟧ network ⟦inputs⟧) hiddenNodeMapping)
  let ⟦outputs⟧ = All⁺.map (λ (u , z) → ⟦model⟧ network ⟦inputs⟧ z) (modelOutputs network)
  variableValues ⟦inputs⟧ ⟦hidden⟧ ⟦outputs⟧
