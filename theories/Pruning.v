(* Reducing ITT terms *)

(* We're only reducing the decorations that are induced by translation, not the
   usual redexes. *)

From Coq Require Import Bool String List BinPos Compare_dec Omega Bool_nat.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast utils LiftSubst Typing.
From Translation Require Import SAst SLiftSubst SCommon Equality ITyping
                                ITypingLemmata ITypingAdmissible.

Fixpoint prune (t : sterm) : sterm :=
  match t with
  | sRel n => sRel n
  | sSort s => sSort s
  | sProd n A B =>
    let A' := prune A in
    let B' := prune B in
    sProd n A' B'
  | sLambda nx A B t =>
    let A' := prune A in
    let B' := prune B in
    let t' := prune t in
    sLambda nx A' B' t'
  | sApp u A B v =>
    let u' := prune u in
    let A' := prune A in
    let B' := prune B in
    let v' := prune v in
    sApp u' A' B' v'
  | sSum n A B =>
    let A' := prune A in
    let B' := prune B in
    sSum n A' B'
  | sPair A B u v =>
    let A' := prune A in
    let B' := prune B in
    let u' := prune u in
    let v' := prune v in
    sPair A' B' u' v'
  | sPi1 A B p =>
    let A' := prune A in
    let B' := prune B in
    let p' := prune p in
    sPi1 A' B' p'
  | sPi2 A B p =>
    let A' := prune A in
    let B' := prune B in
    let p' := prune p in
    sPi2 A' B' p'
  | sEq A u v =>
    let A' := prune A in
    let u' := prune u in
    let v' := prune v in
    sEq A' u' v'
  | sRefl A u =>
    let A' := prune A in
    let u' := prune u in
    sRefl A' u'
  | sJ A u P w v p =>
    let A' := prune A in
    let u' := prune u in
    let P' := prune P in
    let w' := prune w in
    let v' := prune v in
    let p' := prune p in
    sJ A' u' P' w' v' p'
  | sTransport T1 T2 p t =>
    let T1' := prune T1 in
    let T2' := prune T2 in
    let p' := prune p in
    let t' := prune t in
    if eq_term T1' T2' then t' else sTransport T1' T2' p' t'
    (*    match p' with *)
    (* | sRefl _ _ => t' *)
    (* | _ => *)
    (*   let T1' := prune T1 in *)
    (*   let T2' := prune T2 in *)
    (*   sTransport T1' T2' p' t' *)
    (* end *)
  | sHeq A a B b =>
    let A' := prune A in
    let a' := prune a in
    let B' := prune B in
    let b' := prune b in
    sHeq A' a' B' b'
  | sHeqToEq p =>
    let p' := prune p in
    match p' with
    | sHeqRefl A a => sRefl A a
    | sEqToHeq a => a
    | _ => sHeqToEq p'
    end
  | sHeqRefl A a =>
    let A' := prune A in
    let a' := prune a in
    sHeqRefl A' a'
  | sHeqSym p =>
    let p' := prune p in
    match p' with
    | sHeqRefl A a => sHeqRefl A a
    | _ => sHeqSym p'
    end
  | sHeqTrans p q =>
    let p' := prune p in
    let q' := prune q in
    match p' with
    | sHeqRefl A a =>
      match q' with
      | sHeqRefl _ _ => sHeqRefl A a
      | _ => q'
      end
    | _ =>
      match q' with
      | sHeqRefl _ _ => p'
      | _ => sHeqTrans p' q'
      end
    end
  | sHeqTransport p t =>
    let p' := prune p in
    let t' := prune t in
    match p' with
    (* bad version of Théo !! *)
    (* | sRefl A a => sHeqRefl A a *)
    | sRefl s A => sHeqRefl A t'
    | _ =>
      sHeqTransport p' t'
    end
  | sCongProd B1 B2 pA pB =>
    let pA' := prune pA in
    let pB' := prune pB in
    let B1' := prune B1 in
    let B2' := prune B2 in
    match pA', pB' with
    | sHeqRefl (sSort s) A', sHeqRefl (sSort z) B' =>
      (* We use nAnon here because we don't care! *)
      sHeqRefl (sSort (max_sort s z)) (sProd nAnon A' B')
    | _,_ => sCongProd B1' B2' pA' pB'
    end
  | sCongLambda B1 B2 t1 t2 pA pB pt =>
    let pA' := prune pA in
    let pB' := prune pB in
    let pt' := prune pt in
    let B1' := prune B1 in
    let B2' := prune B2 in
    let t1' := prune t1 in
    let t2' := prune t2 in
    match pA', pB', pt' with
    | sHeqRefl _ A', sHeqRefl _ _, sHeqRefl _ _ =>
      sHeqRefl (sProd nAnon A' B1') (sLambda nAnon A' B1' t1')
    | _,_,_ => sCongLambda B1' B2' t1' t2' pA' pB' pt'
    end
  | sCongApp B1 B2 pu pA pB pv =>
    let pA' := prune pA in
    let pB' := prune pB in
    let pu' := prune pu in
    let pv' := prune pv in
    let B1' := prune B1 in
    let B2' := prune B2 in
    match pA', pB', pu', pv' with
    | sHeqRefl _ A', sHeqRefl _ _, sHeqRefl _ u', sHeqRefl _ v' =>
      sHeqRefl (B1'{ 0 := v' }) (sApp u' A' B1' v')
    | _,_,_,_ => sCongApp B1' B2' pu' pA' pB' pv'
    end
  | sCongSum B1 B2 pA pB =>
    let pA' := prune pA in
    let pB' := prune pB in
    let B1' := prune B1 in
    let B2' := prune B2 in
    match pA', pB' with
    | sHeqRefl (sSort s) A', sHeqRefl (sSort z) B' =>
      (* We use nAnon here because we don't care! *)
      sHeqRefl (sSort (max_sort s z)) (sSum nAnon A' B')
    | _,_ => sCongSum B1' B2' pA' pB'
    end
  | sCongPair B1 B2 pA pB pu pv =>
    let pA' := prune pA in
    let pB' := prune pB in
    let pu' := prune pu in
    let pv' := prune pv in
    let B1' := prune B1 in
    let B2' := prune B2 in
    match pA', pB', pu', pv' with
    | sHeqRefl _ A', sHeqRefl _ B', sHeqRefl _ u', sHeqRefl _ v' =>
      sHeqRefl (sSum nAnon A' B') (sPair A' B' u' v')
    | _,_,_,_ => sCongPair B1' B2' pA' pB' pu' pv'
    end
  | sCongPi1 B1 B2 pA pB pp =>
    let pA' := prune pA in
    let pB' := prune pB in
    let pp' := prune pp in
    let B1' := prune B1 in
    let B2' := prune B2 in
    match pA', pB', pp' with
    | sHeqRefl _ A', sHeqRefl _ B', sHeqRefl _ p' =>
      sHeqRefl A' (sPi1 A' B' p')
    | _,_,_ => sCongPi1 B1' B2' pA' pB' pp'
    end
  | sCongPi2 B1 B2 pA pB pp =>
    let pA' := prune pA in
    let pB' := prune pB in
    let pp' := prune pp in
    let B1' := prune B1 in
    let B2' := prune B2 in
    match pA', pB', pp' with
    | sHeqRefl _ A', sHeqRefl _ B', sHeqRefl _ p' =>
      sHeqRefl (B'{ 0 := sPi1 A' B' p'}) (sPi2 A' B' p')
    | _,_,_ => sCongPi2 B1' B2' pA' pB' pp'
    end
  | sCongEq pA pu pv =>
    let pA' := prune pA in
    let pu' := prune pu in
    let pv' := prune pv in
    match pA', pu', pv' with
    | sHeqRefl S' A', sHeqRefl _ u', sHeqRefl _ v' =>
      sHeqRefl S' (sEq A' u' v')
    | _,_,_ => sCongEq pA' pu' pv'
    end
  | sCongRefl pA pu =>
    let pA' := prune pA in
    let pu' := prune pu in
    match pA', pu' with
    | sHeqRefl _ A', sHeqRefl _ u' =>
      sHeqRefl (sEq A' u' u') (sRefl A' u')
    | _,_ => sCongRefl pA' pu'
    end
  | sEqToHeq p =>
    let p' := prune p in
    match p' with
    | sRefl A' x' => sHeqRefl A' x'
    | _ => sEqToHeq p'
    end
  | sHeqTypeEq A B p =>
    let A' := prune A in
    let B' := prune B in
    let p' := prune p in
    (* Not enough annotation. *)
    (* match p' with *)
    (* | sHeqRefl A' x' => sHeqRefl A' x' *)
    (* | _ => sHeqTypeEq p' *)
    (* end *)
    sHeqTypeEq A' B' p'
  | sPack A1 A2 =>
    let A1' := prune A1 in
    let A2' := prune A2 in
    sPack A1' A2'
  | sProjT1 p =>
    let p' := prune p in
    sProjT1 p'
  | sProjT2 p =>
    let p' := prune p in
    sProjT2 p'
  | sProjTe p =>
    let p' := prune p in
    sProjTe p'
  | sAx id => sAx id
  end.
