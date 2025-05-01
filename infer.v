(**********************************************************************)
(* Copyright 2025 Barry Jay                                           *)
(*                                                                    *) 
(* Permission is hereby granted, free of charge, to any person        *) 
(* obtaining a copy of this software and associated documentation     *) 
(* files (the "Software"), to deal in the Software without            *) 
(* restriction, including without limitation the rights to use, copy, *) 
(* modify, merge, publish, distribute, sublicense, and/or sell copies *) 
(* of the Software, and to permit persons to whom the Software is     *) 
(* furnished to do so, subject to the following conditions:           *) 
(*                                                                    *) 
(* The above copyright notice and this permission notice shall be     *) 
(* included in all copies or substantial portions of the Software.    *) 
(*                                                                    *) 
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,    *) 
(* EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF *) 
(* MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND              *) 
(* NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT        *) 
(* HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,       *) 
(* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, *) 
(* OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER      *) 
(* DEALINGS IN THE SOFTWARE.                                          *) 
(**********************************************************************)

(**********************************************************************)
(*                        Type Inference                              *)
(*                                                                    *)
(*                         Barry Jay                                  *)
(*                                                                    *)
(**********************************************************************)



Require Import String Arith Lia Bool List Nat Datatypes.
Require Import Recdef.   
Require Import Program.Equality.

Require Import sk types.

Open Scope string_scope.
Open Scope nat_scope.

Set Default Proof Using "Type".

  
(*** Type inference *) 


Lemma app_ty_is_functional: forall ty uty vty, app_ty ty uty vty -> forall vty2, app_ty ty uty vty2 -> vty2 = vty.
Proof.
  intros ty uty vty s; induction s; intros; subst; try discriminate; try inv_out H; auto; try (inv_out H0; auto_t; congruence); invapp; auto;
  try (cut False; [  tauto | eapply H; eapply con_tagged; fail]); try (cut False; [  tauto | eapply H1; eapply con_tagged; fail]). 
  - assert(ty5 = ty3) by (eapply IHs2; eauto); subst;  assert(vty0 = vty) by (eapply IHs1; eauto); subst; eapply IHs3; eauto.
  - assert(ty3 = ty2) by (eapply IHs1; eauto); subst; eapply IHs2; eauto. 
  - f_equal; auto. 
Qed.



Theorem unique_types: forall gamma M ty, derive gamma M ty -> forall ty2, derive gamma M ty2 -> ty2 = ty.
Proof.
  intros gamma M ty d; induction d; intros; auto_t;  try (inv_out H; auto; fail); inv_out H0. 
  rewrite H in H3; inv_out H3; auto.
  assert(uty0 = uty) by (eapply IHd2; eauto); subst; assert(ty0 = ty) by (eapply IHd1; eauto); subst; eapply app_ty_is_functional; eauto. 
Qed.

(* program types need type equality *)

       

Fixpoint equal_ty uty vty :=
  match uty with 
  | Sty => match vty with | Sty => true  | _ => false end 
  | S1ty uty1 => match vty with S1ty uty2 => equal_ty uty1 uty2 | _ => false end 
  | S2ty uty1 vty1 => match vty with
                        S2ty uty2 vty2 => equal_ty uty1 uty2 && equal_ty vty1 vty2
                      | _ => false end 
  | Kty => match vty with Kty => true | _ => false end 
  | K1ty uty1 => match vty with K1ty uty2 => equal_ty uty1 uty2 | _ => false end 
  | Data0 t1 =>  match vty with Data0 t2 => equal_ty t1 t2 | _ => false   end
  | Data1 t1 uty1 => match vty with
                       Data1 t2 vty1 => equal_ty t1 t2 && equal_ty uty1 vty1 
                     | _ => false end
  | Data2 t1 uty1 uty2 => match vty with
                            Data2 t2 vty1 vty2 => equal_ty t1 t2 && equal_ty uty1 vty1 && equal_ty uty2 vty2
                          | _ => false end
  end.


Lemma eq_equal_ty: forall ty, equal_ty ty ty = true.
Proof. induction ty; simpl; auto; rewrite IHty1; auto; rewrite IHty2; auto. Qed. 


Lemma equal_ty_neq: forall ty1 ty2, ty1 <> ty2 -> equal_ty ty1 ty2 = false.
Proof.
  induction ty1; simpl; intros; auto; caseEq ty2; intros; subst; auto; try congruence; 
    try (eapply IHty1; intro; subst; auto; fail).
  (assert(ty1_1 = d \/ ty1_1 <> d) by repeat decide equality; disjunction_tac; [ 
      rewrite eq_equal_ty; simpl; apply IHty1_2; intro; subst; tauto |
      rewrite IHty1_1; auto]).
  assert(ty1_1 = d \/ ty1_1 <> d) by repeat decide equality; disjunction_tac.
  rewrite eq_equal_ty.
  assert(ty1_2 = d0 \/ ty1_2 <> d0) by repeat decide equality; disjunction_tac.
  congruence. 
  rewrite IHty1_2; auto.
  rewrite IHty1_1; auto.
  assert(ty1_1 = d \/ ty1_1 <> d) by repeat decide equality; disjunction_tac.
  rewrite eq_equal_ty.
  assert(ty1_2 = d0 \/ ty1_2 <> d0) by repeat decide equality; disjunction_tac.
  rewrite eq_equal_ty.
  eapply IHty1_3. congruence. 
  rewrite IHty1_2; auto.
  rewrite IHty1_1; auto.
Qed.


Lemma equal_ty_eq: forall ty1 ty2, equal_ty ty1 ty2 = true -> ty1 = ty2.
Proof.
  intros; assert(ty1 = ty2 \/ ty1 <> ty2) by repeat decide equality; disjunction_tac; auto;
    rewrite equal_ty_neq in *; auto; discriminate.
Qed. 


Definition all_equal cs (sigma_opt: option (list (nat * dtype))) :=
  if forallb (fun p => equal_ty (fst p) (snd p)) cs then sigma_opt else None.


Definition unpack_wait2 ty :=
  match ty with
  | S2ty (S2ty (S2ty (K1ty ty1) (K1ty ty2)) (K1ty ty3)) (S2ty Kty Kty) => Some (ty1, ty2, ty3)
  | _ => None
  end.


Lemma unpack_wait2_some:
  forall ty ty1 ty2 ty3, unpack_wait2 ty = Some (ty1, ty2, ty3) ->  ty = wait2_ty ty1 ty2 ty3. 
Proof.
  intros ty ty1 ty2 ty3 H.
  caseEq ty; intros; subst; try discriminate.
  caseEq d; intros; subst; try discriminate.
  caseEq d1; intros; subst; try discriminate.
  caseEq d; intros; subst; try discriminate.
  caseEq d3; intros; subst; try discriminate.
  caseEq d2; intros; subst; try discriminate.
  caseEq d0; intros; subst; try discriminate.
  caseEq d2; intros; subst; try discriminate.
  caseEq d4; intros; subst; try discriminate.
  inv_out H; auto. 
Qed. 

                   
Function unpack_Zty ty :=
  match unpack_wait2 ty with
  | Some (ty1, ty2, ty3) => if equal_ty ty1 omega_z_ty && equal_ty ty2 omega_z_ty then Some ty3 else None
  | _ => None
  end.


Lemma unpack_Zty_some:
  forall ty fty, unpack_Zty ty = Some fty ->  ty = Zty fty. 
Proof.
  intros ty fty H; functional inversion H; subst.
  rewrite andb_true_iff in *; split_all.
  assert(ty = wait2_ty ty1 ty2 fty) by (eapply unpack_wait2_some; eauto). 
  assert(ty1 = omega_z_ty) by (eapply equal_ty_eq; eauto).
  assert(ty2 = omega_z_ty) by (eapply equal_ty_eq; eauto).
  subst; auto.
Qed.



Fixpoint infer_app r ty uty :=
  match r with
  | 0 => None
  | S r1 => 
      match ty with
      (* combinatory types *) 
      | Kty => Some (K1ty uty)
      | K1ty uty1 => Some uty1
      | Sty => Some (S1ty uty)
      | S1ty uty1 =>          
          let rty := S2ty uty1 uty in
          match unpack_constructor rty with
          | None => Some rty (* not the form of a constructor *)
          | Some (fty, tty) => (* may be a constructor *) 
              if equal_ty fty (p_type fstL) && equal_ty tty (S1ty Kty)
              then Some Bool else (* true *) 
                if equal_ty fty (p_type sndL) && equal_ty tty (S1ty Kty) then Some Bool else (* false *) 
                  if equal_ty fty (p_type fstL) && equal_ty tty Ity then Some Nat else (* zero *) 
                    if equal_ty fty (S2ty (p_type sndL) (K1ty Nat)) && equal_ty tty Ity then Some Nat else (* a successor *)
                      match tty with
                      | S1ty Sty => match fty with
                                    | S2ty (S2ty (S2ty Kty Kty) (K1ty uty3)) (K1ty vty3) => Some (Product uty3 vty3) (* a pair *)
                                    | _ => None
                                    end
                      | S2ty Kty Sty => (* a sum *) 
                          match fty with
                          | Data2 (S1ty Sty) (Data0 (S1ty Kty)) (Data2 (S1ty Sty) uty2 vty2) => Some (Sum uty2 vty2)
                          | _ => None
                          end
 
                      | K1ty uty2 => match infer_app r1 fty uty2 with
                                     | Some vty => Some (Funty uty2 vty) (* a function *) 
                                     | _ => None
                                     end
                      | S2ty (S1ty Sty) uty1 => (* a list *)
                          if equal_ty fty (p_type fstL) then Some (List uty1) else 
                          match fty with
                          | S2ty (S2ty (K1ty (S2ty (S2ty Kty Kty) (K1ty (K1ty (S2ty Kty Kty)))))
                                    (S2ty Kty Kty)) (K1ty (Data2 (S1ty Sty) uty2 uty3)) => 
                              if equal_ty uty3 (List uty2) && equal_ty uty2 uty1 then Some (List uty1) else None
                          | _ => None
                          end
                      | _ => match unpack_Zty fty with
                             | Some fty1 => if equal_ty tty Kty then Some (Rec fty1) (* a Z *) 
                                            else None
                             | _ => None (* unknown constructor *) 
                             end
                      end
          end
      | S2ty uty1 vty1 =>
          match infer_app r1 vty1 uty with
          | None => None
          | Some vty2 =>
              match infer_app r1 uty1 uty with 
              | None => None
              | Some ty2 =>
                  match infer_app r1 ty2 vty2 with
                  | None => None
                  | Some wty => Some wty
                  end
              end
          end
      (* product types *) 
      | Data2 (S1ty Sty) ty1 ty2 => 
          match infer_app r1 uty ty1 with
          | None => None
          | Some vty2 => infer_app r1 vty2 ty2
          end
      (* Bool *)
      | Data0 (S1ty Kty) =>
          match uty with
          | Data2 (S1ty Sty) uty1 vty1 => (* Product uty1 vty1 *) 
              if equal_ty uty1 vty1 then Some uty1 else None
          | _ => None
          end
      (* Nat *) 
      | Data0 (S2ty Kty Kty) =>
          match uty with
          | Data2 (S1ty Sty) uty1 vty1 =>
              match infer_app r1 vty1 Nat with
              | Some uty2 => if equal_ty uty1 uty2 then Some uty1 else None
              | _ => None
              end 
          | _ => None
          end
      (* sum types *)
      | Data2 (S2ty Kty Sty) uty1 vty1 =>
          infer_app r1 (Product Bool (Product uty1 vty1)) uty          
      (* function types *) 
      | Data2 (K1ty Kty) uty1 vty1 => 
          if equal_ty uty uty1 then Some vty1 else None
      (* recursive types *) 
      | Data1 Kty fty => 
          match uty with
          | Data2 (S1ty Sty) vty uty1 => (* Product vty uty1 *) 
              match infer_app r1 fty (Data2 (K1ty Kty) (Data2 (S1ty Sty) vty uty1) vty) with (* V1 * U1 -> V2 *)
              | None => None
              | Some ty2 =>
                  match infer_app r1 ty2 uty with
                  | None => None
                  | Some vty2 => if equal_ty vty2 vty then Some vty else None 
                  end
              end
          | _ => None
          end
      (* list types *)
      | Data1 (S2ty (S1ty Sty) Sty) uty1  =>
          match uty with
          | Data2 (S1ty Sty) vty1 vty2 => (* a product *) 
              match infer_app r1 vty2 (Product uty1 (List uty1)) with
              | Some vty3 => if equal_ty vty3 vty1 then Some vty1 else None
              | _ => None
              end
          | _ => None
          end
      | _ => None 
      end
  end.


Lemma infer_app_mono:
  forall r ty1 ty2 vty, infer_app r ty1 ty2 = Some vty -> forall r1, r <= r1 -> infer_app r1 ty1 ty2 = Some vty.
Proof.
  induction r; intros; auto_t; simpl in *; try discriminate; replace r1 with (S (pred r1)) by lia.
  caseEq ty1; intros; subst; simpl in *; try discriminate; auto_t; try (eapply IHr; eauto; lia).
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq d0; intros; subst; try discriminate; auto. 
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq ty2; intros; subst; try discriminate; auto. 
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq d2; intros; subst; try discriminate; auto. 
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq d3; intros; subst; try discriminate; auto. 
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq d0; intros; subst; try discriminate; auto. 
  caseEq (equal_ty d1 (p_type fstL) && equal_ty d (S1ty Kty));
    intros; rewrite H1 in *; auto; clear H1.
  caseEq (equal_ty d1 (p_type sndL) && equal_ty d (S1ty Kty));
    intros; rewrite H1 in *; auto; clear H1.
  caseEq(equal_ty d1 (p_type fstL) && equal_ty d Ity);
    intros; rewrite H1 in *; auto; clear H1.
  caseEq(equal_ty d1 (S2ty (p_type sndL) (K1ty Nat)) && equal_ty d Ity);
    intros; rewrite H1 in *; auto; clear H1.
  caseEq d; intros; subst; try discriminate; auto.
  caseEq (infer_app r d1 d0); intros; rewrite H1 in *; try discriminate. erewrite IHr; [ | eauto | lia]; auto. 
  (* 4 *) 
  caseEq (infer_app r d0 ty2); intros; rewrite H1 in *; try discriminate. erewrite IHr; [ | eauto | lia].
  caseEq (infer_app r d ty2); intros; rewrite H2 in *; try discriminate. erewrite IHr; [ | eauto | lia].
  caseEq (infer_app r d2 d1); intros; rewrite H3 in *; try discriminate. erewrite IHr; [ | eauto | lia]. auto.
  (* 3 *)
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq d0; intros; subst; try discriminate; auto.
  caseEq d1; intros; subst; try discriminate; auto. 
  caseEq ty2; intros; subst; try discriminate; auto.
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq d2; intros; subst; try discriminate; auto. 
  caseEq (infer_app r d1 Nat); intros; rewrite H1 in *; try discriminate. erewrite IHr; [ | eauto | lia]. auto. 
  (* 2 *)
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq ty2; intros; subst; try discriminate; auto.
  caseEq d; intros; subst; try discriminate; auto. 
  caseEq d3; intros; subst; try discriminate; auto. 
  caseEq (infer_app r d0 (Data2 (K1ty Kty) (Data2 (S1ty Sty) d1 d2) d1)); intros; rewrite H1 in *.  erewrite IHr; [ | eauto | lia].
  caseEq (infer_app r d (Data2 (S1ty Sty) d1 d2)); intros; rewrite H2 in *.  erewrite IHr; [ | eauto | lia].
  caseEq (equal_ty d3 d1); intros; rewrite H3 in *; auto.
  all: try discriminate.
  caseEq d1; intros; subst; try discriminate; auto.
  caseEq d2; intros; subst; try discriminate; auto. 
  caseEq ty2; intros; subst; try discriminate; auto. 
  caseEq d; intros; subst; try discriminate; auto.
  caseEq d1; intros; subst; try discriminate; auto.
  caseEq d; intros; subst; try discriminate; auto.
  caseEq (infer_app r d3 (Product d0 (List d0))); intros; rewrite H1 in *; try discriminate. erewrite IHr; [ | eauto | lia].
  caseEq (equal_ty d d2); intros; rewrite H2 in *; try discriminate. auto.
  (* 1 *)
  caseEq d; intros; subst; try discriminate; auto.
  caseEq d2; intros; subst; try discriminate; auto.
  caseEq (infer_app r ty2 d0); intros; rewrite H1 in *; try discriminate. erewrite IHr; [ | eauto | lia].
  erewrite IHr; [ | eauto | lia]; auto. 
  caseEq d2; intros; subst; try discriminate; auto.
  caseEq d3; intros; subst; try discriminate; auto.
  erewrite IHr; [ | eauto | lia]; auto. 
Qed.

 Ltac eq_tac :=
   rewrite ? andb_true_iff in *; split_all;
   match goal with | H : equal_ty ?ty1 ?ty2 = true |- _ => assert(ty1 = ty2) by (eapply equal_ty_eq; eauto); subst; clear H; eq_tac | _ => auto_t end.



Lemma infer_app_implies_appty: forall r ty uty vty, infer_app r ty uty = Some vty -> app_ty ty uty vty. 
Proof.
  induction r; intros; simpl in *; try discriminate; split_all.
  caseEq ty; intros; subst; try discriminate; inv_out H; auto_t.
  all: cycle 1.                
  - caseEq (infer_app r d0 uty); intros; rewrite H in *; try discriminate. 
    caseEq (infer_app r d uty); intros; rewrite H0 in *; try discriminate. 
    caseEq (infer_app r d2 d1); intros; rewrite H2 in *; try discriminate. inv_out H1.
    eapply app_s2; eapply IHr; eauto. 
  - caseEq d; intros; subst; try discriminate.
    caseEq d0; intros; subst; try discriminate.
    caseEq uty; intros; subst; try discriminate.
    caseEq d; intros; subst; try discriminate.
    caseEq d2; intros; subst; try discriminate.
    caseEq (equal_ty d0 d1); intros; rewrite H in *; try discriminate.
    inv_out H1.  assert(vty = d1) by (eapply equal_ty_eq; eauto); subst. auto_t. 
    caseEq d0; intros; subst; try discriminate.
    caseEq d1; intros; subst; try discriminate.
    caseEq uty; intros; subst; try discriminate.
    caseEq d; intros; subst; try discriminate.
    caseEq d2; intros; subst; try discriminate.
    caseEq (infer_app r d1 Nat); intros; rewrite H in *; try discriminate.
    caseEq (equal_ty d0 d); intros; rewrite H0 in *; try discriminate.
    inv_out H1.  assert(vty = d) by (eapply equal_ty_eq; eauto); subst. auto_t. 
  - caseEq d; intros; subst; try discriminate.
    caseEq uty; intros; subst; try discriminate.
    caseEq d; intros; subst; try discriminate.
    caseEq d3; intros; subst; try discriminate.
    caseEq (infer_app r d0 (Data2 (K1ty Kty) (Data2 (S1ty Sty) d1 d2) d1) ); intros; rewrite H in *; try discriminate. 
    caseEq(infer_app r d (Data2 (S1ty Sty) d1 d2) ); intros; rewrite H0 in *; try discriminate.
    caseEq (equal_ty d3 d1); intros; rewrite H2 in *; try discriminate.
    inv_out H1.  eq_tac. 
    caseEq d1; intros; subst; try discriminate.
    caseEq d; intros; subst; try discriminate.
    caseEq d2; intros; subst; try discriminate.
    caseEq uty; intros; subst; try discriminate.
    caseEq d; intros; subst; try discriminate.
    caseEq d3; intros; subst; try discriminate.
    caseEq (infer_app r d2 (Product d0 (List d0))); intros; rewrite H in *; try discriminate. 
    caseEq (equal_ty d d1); intros; rewrite H0 in *; try discriminate.
    inv_out H1.  eq_tac. 
  - caseEq d; intros; subst; inv_out H1; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d2; intros; subst; inv_out H0; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq (equal_ty uty d0); intros; rewrite H in *; try discriminate.
    inv_out H1.  eq_tac. 
    caseEq d2; intros; subst; inv_out H0; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq (infer_app r uty d0); intros; rewrite H in *; try discriminate.
    auto_t.
    caseEq d2; intros; subst; inv_out H0; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d3; intros; subst; try discriminate.
    assert(app_ty (Product Bool (Product d0 d1)) uty vty) by (eapply IHr; eauto). 
    inv_out H. eapply app_case. eapply app_pair_out; eauto.
    (* last case *) 
  - caseEq d; intros; subst; inv_out H1; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d0; intros; subst; inv_out H0; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d; intros; subst; inv_out H1; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq uty; intros; subst; inv_out H0; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d; intros; subst; inv_out H1; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d2; intros; subst; inv_out H0; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d; intros; subst; inv_out H1; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d3; intros; subst; inv_out H0; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d; intros; subst; inv_out H1; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq d0; intros; subst; inv_out H0; try (eapply app_s1; intro con; inv_out con; fail).
    caseEq (equal_ty d1 (p_type fstL) && equal_ty d (S1ty Kty));
      intros; rewrite H in *; auto; inv_out H1; eq_tac.
    caseEq (equal_ty d1 (p_type sndL) && equal_ty d (S1ty Kty));
      intros; rewrite H0 in *; inv_out H2; eq_tac. 
    caseEq(equal_ty d1 (p_type fstL) && equal_ty d Ity);
      intros; rewrite H1 in *; inv_out H3; eq_tac. 
    caseEq(equal_ty d1 (S2ty (p_type sndL) (K1ty Nat)) && equal_ty d Ity);
      intros; rewrite H2 in *; inv_out H4; eq_tac. 
    caseEq d; intros; subst; try discriminate; auto;
      try (caseEq (unpack_Zty d1); intros; rewrite H3 in *; [ 
          rewrite equal_ty_neq in H5 |];   discriminate). 
    (* 4 cases *)
    + caseEq (unpack_Zty d1); intros; rewrite H3 in *. 
      rewrite eq_equal_ty in *. inv_out H5. 
      assert(d1 = Zty d) by (eapply unpack_Zty_some; eauto); subst. eapply app_Z. 
      discriminate.
    + caseEq (infer_app r d1 d0); intros; rewrite H3 in*.
      inv_out H5.    eapply app_fun. eapply IHr; eauto.
      discriminate.
    + caseEq d0; intros; subst; try discriminate; auto;
        try (caseEq (unpack_Zty d1); intros; rewrite H3 in *; [ rewrite equal_ty_neq in H5 |]; discriminate). 
      caseEq d1; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d1; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d3; intros; subst; try discriminate; auto.
      caseEq d2; intros; subst; try discriminate; auto.
      caseEq d0; intros; subst; try discriminate; auto.
      inv_out H5.     eapply app_pair.
    + caseEq d0; intros; subst; try discriminate; auto;
        try (caseEq (unpack_Zty d1); intros; rewrite H3 in *; [ rewrite equal_ty_neq in H5 |]; discriminate).   
      caseEq d2; intros; subst; try discriminate; auto;
        try (caseEq (unpack_Zty d1); intros; rewrite H3 in *; [ rewrite equal_ty_neq in H5 |]; discriminate).
      caseEq d1; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d1; intros; subst; try discriminate; auto.
      caseEq d0; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d0; intros; subst; try discriminate; auto.
      caseEq d2; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
       caseEq d2; intros; subst; try discriminate; auto.
      inv_out H5. eapply app_sum.      
      caseEq d1; intros; subst; try discriminate; auto;
        try (caseEq d; intros; subst; try discriminate; auto; fail).
      caseEq d; intros; subst; try discriminate; auto; 
        try (caseEq (unpack_Zty (S2ty d0 d3)); intros; rewrite H3 in *; [ rewrite equal_ty_neq in H5 |]; discriminate).
      caseEq (equal_ty (S2ty d0 d3) (p_type fstL)); intros; rewrite H3 in *.
      inv_out H5. eq_tac.  rewrite H4. eapply app_nil.
      clear H H0 H1 H2.
      caseEq d0; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d0; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d0; intros; subst; try discriminate; auto.
      caseEq d5; intros; subst; try discriminate; auto.
      caseEq d4; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d0; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d4; intros; subst; try discriminate; auto.
      caseEq d1; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d0; intros; subst; try discriminate; auto.
      caseEq d3; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq d0; intros; subst; try discriminate; auto.
      caseEq d; intros; subst; try discriminate; auto.
      caseEq (equal_ty d3 (List d1) && equal_ty d1 d2); intros; rewrite H in *.
      inv_out H5. eq_tac. eapply app_cons.
      discriminate.
Qed.


Lemma app_ty_implies_infer_app:
  forall ty uty vty, app_ty ty uty vty -> exists r, infer_app (S r) ty uty = Some vty.
Proof.
  intros ty uty vty s; induction s; intros; subst; try (eexists; simpl; auto_t; fail); 
  try inv_out H; 
  try (exists 0; simpl; rewrite ? eq_equal_ty; eauto; fail).
  - exists 0; simpl.
    caseEq uty; intros; subst; try discriminate; auto. 
    caseEq d; intros; subst; try discriminate; auto. 
    caseEq d1; intros; subst; try discriminate; auto. 
    caseEq vty; intros; subst; try discriminate; auto. 
    caseEq d; intros; subst; try discriminate; auto. 
    caseEq d2; intros; subst; try discriminate; auto. 
    caseEq d; intros; subst; try discriminate; auto. 
    caseEq d3; intros; subst; try discriminate; auto. 
    caseEq d; intros; subst; try discriminate; auto. 
    caseEq d1; intros; subst; try discriminate; auto.
    caseEq (equal_ty d0 (p_type fstL) && equal_ty d (S1ty Kty));
      intros; eq_tac. cut False. tauto. eapply H; auto_t. 
    caseEq (equal_ty d0 (p_type sndL) && equal_ty d (S1ty Kty));
      intros; eq_tac. cut False. tauto. eapply H; auto_t. 
    caseEq (equal_ty d0 (p_type fstL) && equal_ty d Ity);
      intros; eq_tac. cut False. tauto. eapply H; auto_t. 
    caseEq (equal_ty d0 (S2ty (p_type sndL) (K1ty Nat)) && equal_ty d Ity); 
      intros; eq_tac. cut False. tauto. eapply H; auto_t. 
   caseEq d; intros; subst; try discriminate; auto; try (cut False; [ tauto | eapply H; auto_t]; fail).
  - split_all. exists (x + S x0 + S x1); simpl. do 3 (erewrite infer_app_mono; eauto; try lia).
  - eexists; simpl. rewrite ! andb_false_r; auto.
  - split_all. exists (x + S x0); simpl. do 2 (erewrite infer_app_mono; eauto; try lia).
  - split_all. eexists; simpl. erewrite H. rewrite eq_equal_ty; auto.
  - split_all. eexists; simpl. eauto.
  - split_all. eexists; simpl; rewrite ! andb_false_r. erewrite H; eauto.
  - split_all. eexists; simpl.  instantiate(1:= S x + x0); do 2 (erewrite infer_app_mono; eauto; try lia).
    rewrite eq_equal_ty; auto.
  - split_all. eexists; simpl.  erewrite H. rewrite eq_equal_ty; auto.
    Unshelve. all: try apply 0.
Qed. 



Fixpoint infer r gamma M :=
  match r with
  | 0 => None
  | S r1 => 
      match M with
      | Ref x => get x gamma
      | Sop => Some Sty
      | Kop => Some Kty
      | M1 @ M2 =>
          match infer r1 gamma M1, infer r1 gamma M2 with
          | Some ty, Some uty => infer_app r1 ty uty
          | _,_ => None
          end
      end
  end.

Lemma infer_mono: forall r gamma M ty, infer r gamma M = Some ty -> forall r1, r <= r1 -> infer r1 gamma M = Some ty.
Proof.
  induction r; intros; simpl in *; try discriminate.
  caseEq M; intros; subst; try discriminate;
    replace r1 with (S (pred r1)) by lia; inv_out H; simpl; auto.
  caseEq (infer r gamma s); intros; rewrite H in *; try discriminate. 
  caseEq (infer r gamma s0); intros; rewrite H1 in *; try discriminate. 
  erewrite IHr; eauto; try lia. 
  erewrite IHr; eauto; try lia. rewrite H2. eapply infer_app_mono; eauto; lia.
Qed.


  
Theorem infer_implies_derive: forall r gamma M ty, infer r gamma M = Some ty -> derive gamma M ty.
Proof.
  induction r; intros; simpl in *; try discriminate;
    caseEq M; intros; subst; try discriminate; auto_t; inv_out H; auto_t;
    caseEq (infer r gamma s); intros; rewrite H in *; try discriminate;
    caseEq (infer r gamma s0); intros; rewrite H0 in *; try discriminate;
    eapply derive_app; eauto.
  eapply infer_app_implies_appty; eauto. 
Qed.

Theorem derive_implies_infer: forall gamma M ty, derive gamma M ty -> exists r, infer r gamma M = Some ty.
Proof.
  intros gamma M ty d; induction d; intros; simpl in *; split_all; try (exists 1; repeat eexists; eauto; fail). 
cut (exists (r : nat), infer (S r) gamma (M @ N) = Some vty). 
  intros; split_all; auto_t. 
  eelim app_ty_implies_infer_app; intros; eauto. 
  eexists; simpl.
  erewrite infer_mono.       2: eauto.
  erewrite infer_mono.       2: eauto.
  erewrite infer_app_mono. eauto. eauto. 
  instantiate(1:= S x + x0 + x1).   all: lia. 
Qed.


