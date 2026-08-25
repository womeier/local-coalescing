From Wasm Require Import datatypes datatypes_properties.
From Coq Require Import FMapAVL OrderedTypeEx List Lia.

From ExtLib.Structures Require Import Monads.
From ExtLib Require Import OptionMonad.
From Equations Require Import Equations.

Import MonadNotation Bool ssreflect BinNat ListNotations MonadNotation.

Module M := FMapAVL.Make (N_as_OT).

Notation "x |-> y" := (M.add x y M.empty) (at level 60, no associativity).
Notation "x !! i" := (M.find i x) (at level 60, no associativity).

Definition local_map := M.t localidx.
Definition empty := M.empty localidx.


Fixpoint bi_size (instr : basic_instruction) :=
  let bis_size := fun instrs => List.fold_right (fun i s => s + bi_size i) 0 instrs
  in
  match instr with
  | BI_block _ b => 1 + bis_size b
  | BI_if _ b1 b2 => 1 + bis_size b1 + bis_size b2
  | BI_loop _ b => 1 + bis_size b
  | _ => 1
  end.

Definition bis_size (instrs : list basic_instruction) :=
  List.fold_right (fun i s => s + bi_size i) 0 instrs.

Lemma bi_size_gt_0 : forall i, bi_size i > 0.
Proof.
  induction i; intros; cbn; auto; try lia.
Qed.

Program Fixpoint uses_localidx (idx : localidx) (instrs : list basic_instruction) {measure (bis_size instrs)} : bool :=
  match instrs with
  | [] => false
  | x::xs =>
    match x with
    | BI_local_set i => N.eqb i idx || (uses_localidx idx xs)
    | BI_local_get i => N.eqb i idx || (uses_localidx idx xs)
    | BI_local_tee i => N.eqb i idx || (uses_localidx idx xs)
    | BI_block _ b => uses_localidx idx b
    | BI_loop _ b => uses_localidx idx b
    | BI_if _ b1 b2 => uses_localidx idx b1 || uses_localidx idx b2
    | _ => false
    end
  end.
Admit Obligations.
(* cbn; unfold bis_size; try lia. *)


(* (* intermediate instr *)
Inductive ir :=
| IR_block     : list ir -> ir
| IR_local_set : localidx -> ir
| IR_local_get : localidx -> ir
| IR_local_tee : localidx -> ir
| IR_if        : list ir -> list ir -> ir
.

Fixpoint transform (bi : basic_instruction) : list ir :=
  match bi with
  | BI_local_get idx => [IR_local_get idx]
  | BI_local_set idx => [IR_local_set idx]
  | BI_local_tee idx => [IR_local_tee idx]
  | BI_if _ b1 b2 =>
     let b1' := List.fold_left (fun acc i => transform i ++ acc) b1 [] in
     let b2' := List.fold_left (fun acc i => transform i ++ acc) b2 [] in
     [IR_if b1' b2']
  | BI_block _ b =>
     let b' := List.fold_left (fun acc i => acc ++ transform i) b [] in
     [IR_block b']
  | _ => []
  end.

Definition example := BI_block (BT_valtype None) [BI_local_get 0%N; BI_local_set 0%N; BI_call 1%N;
 BI_if (BT_valtype None) [] []].
Compute (transform example).


Fixpoint validate_instrs (phi : local_map) (orig opt : list ir) : bool :=
  match orig with
  | (IR_local_get idx) :: xs => true
  | (IR_local_set idx) :: xs => true
  | _ => false
  end. *)


Program Fixpoint validate_instrs (phi : local_map) (orig opt : list basic_instruction) { measure (bis_size orig) } : bool :=
  match orig with
  | [] => match opt with | [] => true | _ => false end
  | x::xs =>
    match opt with
    | [] => false
    | y::ys => validate_instrs phi xs ys &&
(*****)
match x with
(* local.set *)
| BI_local_set i =>
  match y with
  | BI_local_set j => true
  | _ => false
  end
(* local.get *)
| BI_local_get i => true
(* local.tee TODO *)
| BI_local_tee i => false
(* block *)
| BI_block tb1 b1 =>
  match y with
  | BI_block tb2 b2 => validate_instrs phi b1 b2 && block_type_eqb tb1 tb2
  | _ => false
  end
(* catch all: others not modified *)
| _ => basic_instruction_eqb x y
end
(****)
    end
  end.
Next Obligation.
cbn. have H := bi_size_gt_0 x. lia.
Defined.
Next Obligation.
unfold bis_size. cbn. lia.
Defined.
Next Obligation.
do 3 (split; first now intro). now intro.
Defined.
Admit Obligations.

Compute (validate_instrs empty [] []).

Check validate_instrs.
Print 

Program Fixpoint validate_instrs (phi : local_map) (orig opt : list basic_instruction) { struct orig } : bool :=
  match orig with
  | [] => match opt with | [] => true | _ => false end
  | x::xs =>
    match opt with
    | [] => false
    | y::ys => validate_instrs phi xs ys &&
(*****)
match x with
(* local.set *)
| BI_local_set i =>
  match y with
  | BI_local_set j => true
  | _ => false
  end
(* local.get *)
| BI_local_get i => true
(* local.tee TODO *)
| BI_local_tee i => false
(* block *)
| BI_block tb1 b1 =>
  match y with
  | BI_block tb2 b2 => validate_instrs phi b1 b2 && block_type_eqb tb1 tb2
  | _ => false
  end
(* catch all: others not modified *)
| _ => basic_instruction_eqb x y
end
(****)
    end
  end.

  match hdOrig with
  (* local.set *)
  | BI_local_set i =>
    match hdOpt with
    | BI_local_set j =>
      match (phi !! i) with
      | None => false
      | Some i' => N.eqb i' j && uses_localidx i tlOrig
      end
    | _ => false
    end
  (* local.get *)
  | BI_local_get i =>
    match hdOrig with
    | BI_local_get j =>
      match (phi !! i) with
      | Some i' => N.eqb i' j
      | None => false
      end
    | _ => false
    end
  (* local.tee ? TODO *)
  | BI_block t b =>
    match hdOpt with
    | BI_block t' b' => validate_instr_list phi b b' && block_type_eqb t t'
    | _ => false
    end
  | _ => basic_instruction_eqb hdOrig hdOpt
  end

  | x::xs =>
    match instrsOpt with
    | y::ys => validate_instr phi x xs y ys && 
    | _ => false
    end
  end.