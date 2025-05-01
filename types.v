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
(*                        Types                                       *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

(*

support for fixpoints but no arithmetic or ADTs *) 

Require Import String Arith Lia Bool List Nat Datatypes.
Require Import Recdef.    (* for functional inversion - use this more widely when understood! *)
Require Import Program.Equality.

Require Import sk.

Open Scope string_scope.
Open Scope nat_scope.

Set Default Proof Using "Type".


Inductive dtype : Set :=
| Kty
| K1ty : dtype -> dtype
| Sty
| S1ty : dtype -> dtype
| S2ty : dtype -> dtype -> dtype
| Data0 : dtype -> dtype                   (* the first arg is the type of a tag *) 
| Data1 : dtype -> dtype -> dtype          (* the first arg is the type of a tag *) 
| Data2 : dtype -> dtype -> dtype -> dtype (* the first arg is the type of a tag *) 
. 

Global Hint Constructors dtype : TreeHintDb.


Fixpoint get x ps :=
  match ps with
  | nil => None
  | (y,uty) :: ps1 => if String.eqb y x then Some (uty: dtype) else get x ps1
  end.


Fixpoint pc_type gamma p := (* program_type is defined below *) 
  match p with
  | Sop => Sty
  | Kop => Kty
  | Sop @ p1 => S1ty (pc_type gamma p1)
  | Kop @ p1 => K1ty (pc_type gamma p1)
  | Sop @ p1 @ p2 => S2ty (pc_type gamma p1) (pc_type gamma p2)
  | Ref x => match get x gamma with | Some ty => ty | _ => Kty end
  | _ => Sty (* dummy value *) 
  end.


Definition p_type p := pc_type nil p. (* program_type is defined below *)

(*

copied from sk.v

Definition product_tag := Sop @ Sop.
Definition bool_tag := Sop @ Kop.
Definition nat_tag := Sop @ Kop @ Kop. 
Definition sum_tag := Sop @ Kop @ Sop.
Definition fun_tag dummy := Kop @ dummy. (* see also funty_tag for types *)
Definition Z_tag := Kop.
Definition list_tag u := Sop @ (Sop @ Sop) @ u.
 *)


Definition Product tty fty := Data2 (S1ty Sty) tty fty.
Definition Bool := Data0 (S1ty Kty).
Definition Nat := Data0 (S2ty Kty Kty).
Definition Sum tty fty := Data2 (S2ty Kty Sty) tty fty.
Definition Funty uty vty := Data2 (K1ty Kty) uty vty.
Definition Rec fty := Data1 Kty fty.
Definition List ty := Data1 (S2ty (S1ty Sty) Sty) ty. 

Definition Ity := S2ty Kty Kty.

Definition tagged_tyl fty := S1ty (S2ty (K1ty Kty) fty).
Definition tag_ty tty := S2ty (S2ty (K1ty Kty) (K1ty Kty)) (K1ty tty). 

Definition omega_z_ty := Eval cbv in (p_type omega_z).
Function wait2_ty mty nty pty := S2ty (S2ty (S2ty (K1ty mty) (K1ty nty)) (K1ty pty)) Ity. 
Function Zty fty := wait2_ty omega_z_ty omega_z_ty fty. 


Inductive constructor: dtype -> Prop :=
| con_tagged: forall fty tty, constructor (S2ty (S2ty (K1ty Kty) fty) (S2ty (S2ty (K1ty Kty) (K1ty Kty)) (K1ty tty)))
.

Global Hint Constructors constructor : TreeHintDb.

Function unpack_constructor ty :=
  match ty with
  | S2ty (S2ty (K1ty Kty) fty) (S2ty (S2ty (K1ty Kty) (K1ty Kty)) (K1ty tty)) => Some (fty, tty)
  | _ => None
  end.

Lemma unpack_constructor_some:
  forall ty fty tty, unpack_constructor ty = Some (fty, tty) ->
                     ty = S2ty (S2ty (K1ty Kty) fty) (S2ty (S2ty (K1ty Kty) (K1ty Kty)) (K1ty tty)). 
 Proof. intros ty fty tty H; functional inversion H; subst; reflexivity. Qed.

Lemma unpack_constructor_none: forall ty, unpack_constructor ty = None -> ~ constructor ty. 
Proof. intros ty H; intro con; inv_out con; functional inversion H; auto. Qed.



(*** Type Derivation *)



Inductive app_ty : dtype -> dtype -> dtype -> Prop :=
(* combinatory types *)
| app_k0 : forall uty, app_ty Kty uty (K1ty uty)
| app_k1 : forall uty vty, app_ty (K1ty uty) vty uty
| app_s0 : forall uty, app_ty Sty uty (S1ty uty)
| app_s1 : forall uty vty, ~ constructor (S2ty uty vty) -> app_ty (S1ty uty) vty (S2ty uty vty)
| app_s2 : forall ty1 ty2 ty3 uty vty wty,
    app_ty ty2 uty vty -> app_ty ty1 uty ty3 -> app_ty ty3 vty wty ->
    app_ty (S2ty ty1 ty2) uty wty
(* Product types *) 
| app_pair : forall uty vty, app_ty (tagged_tyl (S2ty (S2ty Ity (K1ty uty)) (K1ty vty))) (tag_ty (S1ty Sty)) (Product uty vty)
| app_pair_out: forall uty vty ty1 ty2 ty,
    app_ty ty1 uty ty2 -> app_ty ty2 vty ty -> app_ty (Data2 (S1ty Sty) uty vty) ty1 ty
(* Bool *) 
| app_true : app_ty (S1ty (S2ty (K1ty Kty) (p_type fstL))) (tag_ty (S1ty Kty)) Bool
| app_false : app_ty (S1ty (S2ty (K1ty Kty) (p_type sndL))) (tag_ty (S1ty Kty)) Bool
| app_cond: forall uty, app_ty Bool (Product uty uty) uty 
(* Nat *)
| app_zero : app_ty (S1ty (S2ty (K1ty Kty) (p_type fstL))) (tag_ty Ity) Nat
| app_succ : app_ty (S1ty (S2ty (K1ty Kty) (S2ty (p_type sndL) (K1ty Nat)))) (tag_ty Ity) Nat
| app_pred: forall uty vty, app_ty vty Nat uty -> app_ty Nat (Product uty vty) uty
(* Sum types *)
| app_sum : forall uty vty, app_ty (tagged_tyl (Product Bool (Product uty vty))) (tag_ty (S2ty Kty Sty)) (Sum uty vty) 
| app_case: forall uty vty ty1 ty2,  app_ty (Product Bool (Product uty vty)) ty1 ty2 -> app_ty (Sum uty vty) ty1 ty2
(* Function types *)
| app_fun : forall ty uty vty, app_ty ty uty vty -> app_ty (tagged_tyl ty) (tag_ty (K1ty uty)) (Funty uty vty)
| app_fun_out : forall uty vty, app_ty (Funty uty vty) uty vty                                                                              
(* Recursive types *)
| app_Z: forall fty, app_ty (tagged_tyl (Zty fty)) (tag_ty Kty) (Rec fty)                            
| app_Z_out: forall fty uty vty ty2,  app_ty fty (Funty (Product vty uty) vty) ty2 -> app_ty ty2 (Product vty uty) vty -> app_ty (Rec fty) (Product vty uty) vty
(* List types *)
| app_nil : forall uty, app_ty (tagged_tyl (p_type fstL)) (tag_ty (S2ty (S1ty Sty) uty)) (List uty)
| app_cons : forall uty, app_ty (tagged_tyl
                                   (S2ty (S2ty (K1ty (p_type sndL)) Ity) (K1ty (Data2 (S1ty Sty) uty (List uty)))))
                           (tag_ty (S2ty (S1ty Sty) uty))
                           (List uty)

| app_list_out : forall uty ty1 ty2, app_ty ty2 (Product uty (List uty)) ty1 -> app_ty (List uty) (Product ty1 ty2) ty1 
.


Inductive derive: list (string * dtype) -> SK -> dtype -> Prop :=
| derive_var: forall gamma x uty, get x gamma = Some uty -> derive gamma (Ref x) uty
| derive_s : forall gamma, derive gamma Sop Sty
| derive_k : forall gamma, derive gamma Kop Kty
| derive_app: forall gamma M N ty uty vty, derive gamma M ty -> derive gamma N uty -> app_ty ty uty vty ->
                                           derive gamma (M@N) vty
.

Global Hint Constructors app_ty derive : TreeHintDb.

 
Ltac invapp :=
  unfold Funty in *;
  match goal with
  | H: app_ty Sty _ _ |- _ => inv_out H; invapp
  | H: app_ty Kty _ _ |- _ => inv_out H; invapp
  | H: app_ty (K1ty _) _ _ |- _ => inv_out H; invapp
  | H: app_ty (S1ty _) _ _ |- _ => inv_out H; invapp
  | H: app_ty (S2ty _ _) _ _ |- _ => inv_out H; invapp
  | H: app_ty (Data0 _) _ _ |- _ => inv_out H; invapp
  | H: app_ty (Data2 _ _ _) _ _ |- _ => inv_out H; invapp
  | _ => idtac
  end.

Ltac app_s1_tac := (eapply app_s1; intro con; inversion con; fail) ||
                     eapply app_fun ||
                   (*   eapply app_Z || !! *) 
                     eapply app_pair ||
                     eapply app_true ||
                     eapply app_false ||
                     eapply app_zero ||
                     eapply app_succ ||
                     idtac.

Ltac apptac :=
  unfold Zty, wait2_ty, tag_ty, Ity, tag_ty; 
    match goal with
    | |- app_ty (S2ty _ _) _ _ => eapply app_s2; apptac
    | |- app_ty Kty _ _ => auto_t; apptac 
    | |- app_ty (K1ty _)  _ _ => auto_t; apptac 
    | |- app_ty Sty _ _ => auto_t; apptac
    | |- app_ty (S1ty _) _ _ => app_s1_tac
    | |- app_ty (Data0 _) _ _ => auto_t
    | |- app_ty (Data2 _ _ _) _ _ => auto_t
    | _ => idtac
    end.

 

Ltac dertac :=
  unfold Iop, tag_ty in *; 
  match goal with
  | H : derive _ Sop _ |- _  => inv_out H; dertac
  | H : derive _ Kop _ |- _  => inv_out H; dertac
  | H : derive _ (App _ _) _ |- _  => inv_out H; dertac
  | _ => invapp
  end.

Lemma app_s1_not_constructor :  forall uty vty ty, app_ty (S1ty uty) vty ty -> ~ constructor (S2ty uty vty) -> ty = S2ty uty vty.
Proof. intros; inv_out H; auto; try (cut False; [ tauto | eapply H0; cbv; auto_t]). Qed. 

Lemma app_tag: forall t uty, program t -> app_ty (tag_ty (p_type t)) uty Kty.    
Proof. intros; apptac. Qed.

(*
Set Printing Depth 10000.

Print omega_z_ty. 
*) 



Lemma app_ty_omega_z_ty: app_ty omega_z_ty omega_z_ty   (S2ty
       (S2ty (K1ty Sty)
          (S2ty (S2ty (K1ty Sty) (S2ty (K1ty Kty) (S2ty Kty Kty)))
             (S2ty
                (S2ty (K1ty Sty)
                   (S2ty (K1ty Kty)
                      (S2ty (K1ty Sty)
                         (S2ty (K1ty (S1ty (K1ty Kty)))
                            (S2ty
                               (S2ty (K1ty Sty)
                                  (S2ty (K1ty (S1ty (K1ty Kty)))
                                     (S2ty
                                        (S2ty (K1ty Sty)
                                           (S2ty
                                              (K1ty
                                                 (S1ty
                                                   (S2ty 
                                                   (K1ty omega_z_ty)
                                                   (K1ty omega_z_ty))))
                                              (S2ty (K1ty Kty) (S2ty Kty Kty))))
                                        (K1ty (S2ty Kty Kty)))))
                               (K1ty
                                  (S2ty (S2ty (K1ty Kty) (K1ty Kty)) (K1ty Kty))))))))
                (K1ty
                   (S2ty (K1ty (S1ty (S2ty (K1ty Kty) (K1ty Kty))))
                      (S2ty (K1ty Kty) (S2ty (K1ty Kty) (S2ty Kty Kty))))))))
                           (K1ty (S2ty Kty Kty))). 
Proof. cbv; apptac. Qed. 




Theorem reduction_preserves_typing:
  forall gamma M ty, derive gamma M ty -> forall N, sk_red1 M N -> derive gamma N ty. 
Proof.
  intros gamma M ty d; induction d; intros; try (inv_out H; fail); inv_out H0;
    try (eapply derive_app; eauto; fail); inv_out d1; inv_out H2; dertac;
    try (inv_out H; repeat eapply derive_app; [ auto_t | auto_t | | auto_t | auto_t | |]; cbv; apptac; eauto; fail).
  repeat eapply derive_app; auto_t.
  repeat eapply derive_app. 1,2,4,5: auto_t.  1-3: apptac; eauto. 
  inv_out H. repeat eapply derive_app. 1,2,4,5: auto_t.
  apptac; [ eapply app_ty_omega_z_ty | apptac; eapply app_Z | apptac; auto_t].  cbv; apptac.  apptac. 
  auto.
Qed.

  

(*** Expressive Power *)

(* combinators *)

Lemma derive_s_fun:
  forall gamma M N P ty1 ty2 ty3 uty vty wty,
    derive gamma M ty1 -> derive gamma N ty2 -> derive gamma P uty -> ~constructor (S2ty ty1 ty2) -> 
    app_ty ty2 uty vty -> app_ty ty1 uty ty3 -> app_ty ty3 vty wty ->
    derive gamma (Sop @ M @ N @ P) wty. 
Proof.  intros; repeat eapply derive_app; auto_t; inv_out H6; invapp; eapply app_pair_out; eauto. Qed.

Lemma derive_k_fun: forall gamma M N uty vty, derive gamma M uty -> derive gamma N vty -> derive gamma (Kop @ M @ N) uty. 
Proof. auto_t. Qed. 

Lemma derive_I: forall gamma, derive gamma Iop (S2ty Kty Kty).
Proof. intros; repeat eapply derive_app; auto_t; eapply app_s1; intro con; inv_out con; inv_out H. Qed. 



(* pairing and projection *)

Lemma derive_pairL: forall gamma, derive gamma pairL (p_type pairL).
Proof.
  intros; cbv; repeat eapply derive_app; (eapply derive_s || eapply derive_k || eapply app_k0 || eapply app_s0 || idtac);
    eapply app_s1; intro con; inv_out con; inv_out H.
Qed.
  
Lemma app_ty_pairL: forall uty, exists ty, app_ty (p_type pairL) uty ty /\ forall vty, app_ty ty vty (Product uty vty).
Proof.  intro; eexists; cbv; split; intros; apptac. Qed.

Lemma derive_fstL: forall gamma, derive gamma fstL (p_type fstL).
Proof. intros; cbv; repeat eapply derive_app; auto_t; apptac. Qed. 

Lemma app_ty_fstL: forall uty vty, app_ty (p_type fstL) (Product uty vty) uty. 
Proof. intros; cbv;  auto_t. Qed.
  
Lemma derive_sndL: forall gamma, derive gamma sndL (p_type sndL).
Proof. intros; cbv; repeat eapply derive_app; auto_t; apptac. Qed.
           
Lemma app_ty_sndL: forall uty vty, app_ty (p_type sndL) (Product uty vty) vty. 
Proof. intros; cbv;  auto_t. Qed.

(* Booleans *) 

Lemma derive_tt: forall gamma, derive gamma tt Bool. 
Proof.
  intros; cbv; repeat eapply derive_app; (eapply derive_s || eapply derive_k || idtac).
  1,2,3,5,6,9,10,11,12,14,15,16: auto_t. 
  1-5: eapply app_s1; intro con; inv_out con. 
  eapply app_true. 
Qed. 

Lemma derive_ff: forall gamma, derive gamma ff Bool. 
Proof. intros; cbv; repeat eapply derive_app; (eapply derive_s || eapply derive_k || eapply app_s0 || eapply app_k0 || idtac); apptac. Qed. 


Theorem app_ty_cond: exists ty, app_ty (p_type cond) Bool ty /\ forall uty, exists ty2, app_ty ty uty ty2 /\ app_ty ty2 uty uty.
Proof. repeat eexists; cbv; apptac. Qed. 
  
Theorem derive_cond: forall gamma b t1 t2 uty, derive gamma b Bool -> derive gamma t1 uty -> derive gamma t2 uty -> derive gamma (cond @ b @ t1 @ t2) uty.
Proof.
  intros.
  eapply derive_app; eauto. eapply derive_app; eauto. eapply derive_app; eauto.
  instantiate(1:= p_type cond); cbv. 
  repeat eapply derive_app; (eapply derive_s || eapply derive_k || apptac).
  all: cbv; apptac. 
Qed.


(* Sum types *)

Lemma derive_inl: forall gamma p uty vty, derive gamma p (Product uty vty) -> derive gamma (inl_c @ p) (Sum uty vty).
Proof.
  intros. eapply derive_app. 2: eauto.
  cbv; repeat eapply derive_app; ( eapply derive_s || eapply derive_k || apptac). apptac. eapply app_sum. 
Qed.

Lemma derive_inr: forall gamma p uty vty, derive gamma p (Product uty vty) -> derive gamma (inr_c @ p) (Sum uty vty).
Proof.
  intros. eapply derive_app. 2: eauto.
  cbv; repeat eapply derive_app; ( eapply derive_s || eapply derive_k || apptac). apptac. eapply app_sum. 
Qed.


Lemma app_ty_case_c:
  forall uty vty ty1 ty2 ty, app_ty ty1 uty ty -> app_ty ty2 vty ty ->
                             exists cty, app_ty (p_type case_c) (Product ty1 ty2) cty /\ app_ty cty (Sum uty vty) ty.
Proof. intros; repeat eexists; cbv; apptac; auto_t. Qed. 


(*** Lambda-abstraction *)


Lemma derive_occurs_false: forall x uty gamma M ty, derive ((x,uty):: gamma) M ty -> occurs x M = false -> derive gamma M ty.
Proof.
  cut(forall gamma1 M ty, derive gamma1 M ty -> forall x uty gamma, gamma1 = (x,uty):: gamma -> occurs x M = false -> derive gamma M ty). 
  intros; eauto.
  intros gamma1 M ty d; induction d; intros; subst; simpl in *; auto_t.
  - rewrite H1 in *; auto_t.
  - rewrite orb_false_iff in *; split_all; eapply derive_app; auto_t. 
Qed.

Lemma derive_occurs_false2: forall gamma M ty, derive gamma M ty -> forall x uty, occurs x M = false -> derive ((x,uty):: gamma) M ty .
Proof.
  intros gamma M ty d; induction d; intros; subst; simpl in *; auto_t.
  - eapply derive_var; simpl; rewrite H0; eauto. 
  - rewrite orb_false_iff in *; split_all; eapply derive_app; auto_t. 
Qed.


Lemma derive_star_not_skkkk : forall gamma x M, ~ derive gamma (\ x M) (S2ty (K1ty Kty) (K1ty Kty)).
Proof.
  intros; intro; caseEq M; intros; subst; simpl in *; dertac. 
  caseEq (x=?s)%string; intros; rewrite H0 in *; dertac.
  caseEq (occurs x s || occurs x s0); intros; rewrite H0 in *; dertac.
  caseEq s; intros; subst; simpl in *. 
  caseEq (x=?s1)%string; intros; rewrite H in *; dertac.
  caseEq s0; intros; subst; simpl in *; dertac. 
  rewrite H0 in *; dertac. 
  discriminate.
  rewrite H0 in *; dertac.
  dertac.
  caseEq s0; intros; subst; simpl in *; dertac.
  rewrite H0 in *; dertac. 
  discriminate.
  rewrite H0 in *; dertac.
  caseEq (occurs x s1 || occurs x s2); intros; rewrite H in *; dertac. 
  caseEq s0; intros; subst; simpl in *; dertac.
  rewrite H0 in *; dertac. 
  discriminate.
  rewrite H0 in *; dertac.
Qed. 

  
Lemma derive_star_not_tag: forall M x gamma tty, ~ derive gamma (\x M) (S2ty (S2ty (K1ty Kty) (K1ty Kty)) (K1ty tty)).
Proof.
  induction M; intros; intro; unfold tag in *; simpl in *; dertac. 
  - caseEq (x=?s)%string; intros; rewrite H0 in *; dertac. 
  - caseEq (occurs x M1 || occurs x M2); intros; rewrite H0 in *; dertac; eapply derive_star_not_skkkk; eauto.
Qed.



Theorem derive_star: forall x uty gamma M vty, derive ((x,uty):: gamma) M vty -> exists ty, derive gamma (\x M) ty /\ app_ty ty uty vty.
Proof.
  (* the complexity of the proof is due to the complexity of the definition of star *) 
  cut(forall gamma1 M vty, derive gamma1 M vty -> forall x uty gamma, gamma1 = (x,uty):: gamma -> exists ty, derive gamma (\x M) ty /\ app_ty ty uty vty).
  intros; eauto.
  intros gamma1 M vty d; induction d; intros; subst; simpl in *; auto_t.
  - caseEq (x0=?x)%string; intros; rewrite H0 in *.
    + inv_out H; exists (S2ty Kty Kty); split; repeat eapply derive_app; auto_t; eapply app_s1; intro con; inv_out con; inv_out H.
    + exists (K1ty uty); split; auto_t. 
  - eelim IHd1; intros. 2: eauto. split_all. 
    eelim IHd2; intros. 2: eauto. split_all.
    caseEq (occurs x M || occurs x N ); intros.
    repeat eexists. eapply derive_app. eapply derive_app. auto_t. eauto. auto_t. eauto. eapply app_s1. 2: auto_t.
    intro con; inv_out con.
    eapply derive_star_not_tag; eauto.
    rewrite orb_false_iff in *; split_all.
    rewrite star_occurs_false in H1; eauto. 
    rewrite star_occurs_false in H3; eauto; dertac. 
    exists (K1ty vty); split; auto_t. 
Qed.


Theorem derive_lam:
  forall x uty gamma M d vty, derive ((x,uty):: gamma) M vty -> derive gamma d uty ->
                            derive gamma (lam x M d) (Funty uty vty). 
Proof.
  intros. eelim derive_star; intros.  2: eauto. split_all.
  eapply derive_app. eapply derive_app. auto_t. eapply derive_app. repeat eapply derive_app; auto_t. eauto.
  apptac. apptac. 2: apptac; eauto. 
  eapply derive_app. repeat eapply derive_app; auto_t.  apptac. auto_t. apptac. 
Qed.

Lemma derive_fun_ap: forall gamma f uty vty u, derive gamma f (Funty uty vty) -> derive gamma u uty -> derive gamma (f @ u) vty.
Proof. intros; eapply derive_app; eauto; eapply app_fun_out. Qed. 




(* Recursion *)


Lemma derive_omega_z: forall gamma,  derive gamma omega_z omega_z_ty.
Proof. intros; cbv; repeat eapply derive_app; ( eapply derive_s || eapply derive_k || idtac); apptac. Qed. 



Lemma derive_Z: forall gamma f fty, derive gamma f fty -> derive gamma (Z f) (Rec fty).
Proof.
  intros; unfold Z, tagged.
  eapply derive_app. eapply derive_app. auto_t.
  eapply derive_app. auto_t. 2: apptac. 2: apptac. 2: cbv; repeat eapply derive_app; auto_t; apptac. 2: eapply app_Z. 
  unfold wait2.
  eapply derive_app. 2: cbv; repeat eapply derive_app; auto_t; apptac.
  eapply derive_app. auto_t. 2: auto_t. 2: apptac. 
  eapply derive_app. eapply derive_app. auto_t. 2: auto_t. 2: eapply derive_app; auto_t. 
  eapply derive_app. eapply derive_app. auto_t. 2: auto_t. 
  eapply derive_app. auto_t. eapply derive_omega_z. auto_t.
  eapply derive_app. auto_t. eapply derive_omega_z. auto_t.
  apptac. apptac. 
Qed.

Lemma derive_Z_app:
  forall gamma f fty p uty vty ty2,
    derive gamma f fty -> derive gamma p (Product vty uty) -> app_ty fty (Funty (Product vty uty) vty) ty2 -> app_ty ty2 (Product vty uty) vty -> 
    derive gamma (Z f @ p) vty.
Proof.  intros; eapply derive_app. eapply derive_Z; eauto. eauto. eapply app_Z_out; eauto. Qed.



  (*** Arithmetic *)

Lemma derive_pair: forall gamma u uty v vty, derive gamma u uty -> derive gamma v vty -> derive gamma (pairL @ u @ v) (Product uty vty).
Proof.
  intros. eapply derive_app; eauto. eapply derive_app; eauto. eapply derive_pairL. 1,2: cbv; apptac. Qed.

Lemma derive_Zero: forall gamma, derive gamma Zero Nat.
  intros; unfold Zero, tagged. 
  eapply derive_app. eapply derive_app; auto_t. eapply derive_app. repeat eapply derive_app; auto_t. eapply derive_fstL.   apptac.   
  cbv; repeat eapply derive_app; ( eapply derive_s || eapply derive_k || apptac || idtac); apptac. 
  eapply app_zero.
Qed.

Lemma derive_Succ: forall gamma n, derive gamma n Nat -> derive gamma (Succ @ n) Nat.
  intros; eelim derive_star; intros; split_all.
  eapply derive_app; eauto.
  unfold tagged. eapply derive_app. eapply derive_app. auto_t.
  eapply derive_app.
  repeat eapply derive_app; ( eapply derive_s || eapply derive_k || apptac || idtac); apptac. 
  eapply derive_app. eapply derive_app. auto_t. eapply derive_sndL. auto_t. 
  eapply derive_app. auto_t. eapply derive_var; simpl; auto. auto_t.
  1-3: apptac.   
  cbv; repeat eapply derive_app; ( eapply derive_s || eapply derive_k || apptac || idtac); apptac. 
  eapply app_succ.
Qed.


Lemma derive_isZero: forall gamma, derive gamma isZero (S2ty (S2ty Kty Kty) (K1ty (Product Bool (K1ty Bool)))). 
Proof.
  intros; unfold isZero. refold star; refold occurs. rewrite ! String.eqb_refl. refold orb.
  replace (occurs "n" pairL) with false by (cbv; auto).
  replace (occurs "n" tt) with false by (cbv; auto).
  replace (occurs "n" ff) with false by (cbv; auto).
  unfold p_type; simpl. 
  eapply derive_app. eapply derive_app; auto_t. eapply derive_I; simpl; eauto. 
  eapply derive_app. auto_t. eapply derive_pair. eapply derive_tt. eapply derive_app; auto_t. eapply derive_ff. auto_t.
  apptac. 
Qed.

Lemma app_isZero: app_ty  (S2ty (S2ty Kty Kty) (K1ty (Product Bool (K1ty Bool)))) Nat Bool. 
Proof. apptac; eapply app_pred; auto_t. Qed.


Lemma derive_pred: forall gamma, derive gamma predN (S2ty (S2ty Kty Kty) (K1ty (Product Nat (S2ty Kty Kty))) ). 
Proof.
  intros; unfold predN.  refold star; refold occurs. rewrite ! String.eqb_refl. refold orb.
  replace (occurs "n" pairL) with false by (cbv; auto).
  replace (occurs "n" Zero) with false by (cbv; auto).
  replace (occurs "n" Iop) with false by (cbv; auto).
  eapply derive_app. eapply derive_app; auto_t. eapply derive_I; simpl; eauto. 
  eapply derive_app. auto_t. eapply derive_pair. eapply derive_Zero. eapply derive_I. auto_t. apptac. 
Qed. 

Lemma app_ty_pred: app_ty (S2ty (S2ty Kty Kty) (K1ty (Product Nat (S2ty Kty Kty)))) Nat Nat.
Proof. apptac; auto_t. Qed. 


Definition compose := Sop @ (Kop @ Sop) @ Kop.

Lemma compose_red: forall g f x, sk_red (compose @ g @ f @ x) (g @ (f @ x)).
Proof. eval_tac. Qed.

Lemma app_ty_compose:
  forall uty fty gty ty ty2, app_ty fty uty ty -> app_ty gty ty ty2 -> exists ty3 ty4, app_ty (p_type compose) gty ty3 /\ app_ty ty3 fty ty4 /\ app_ty ty4 uty ty2.
Proof.  intros; repeat eexists; cbv; apptac; eauto. Qed. 



Lemma derive_primrec_app:
  forall gamma g h u gty hty uty ty ty2 ty3 p,
    derive gamma g gty -> derive gamma h hty -> derive gamma u uty -> derive gamma p (Product ty Nat) ->
    app_ty gty uty ty -> app_ty hty uty ty2 -> app_ty ty2 Nat ty3 -> app_ty ty3 ty ty -> derive gamma (primrec g h u @ p) ty. 
Proof. 
  intros; eapply derive_Z_app. 2: eauto.
  repeat eapply derive_app; ( eapply derive_s || eapply derive_k || apptac); eauto. apptac. apptac. eapply app_pair_out. apptac. apptac. eapply app_pair_out.
  apptac. apptac. eapply app_pred. apptac. auto_t. eauto. eauto.
Qed.


Lemma derive_minrec_app:
  forall gamma f u n fty uty ty2,
    derive gamma f fty -> derive gamma u uty -> derive gamma n Nat -> app_ty fty uty ty2 -> app_ty ty2 Nat Bool ->
    derive gamma (minrec f u @ n) Nat.
Proof.
  intros; unfold minrec. eapply derive_app. eapply derive_app. eapply derive_app. auto_t. eapply derive_app. auto_t.
  2,3: auto_t. 3: apptac. 3: eauto. 3: apptac.
  all: cycle 1.
  eapply derive_app. 2: eapply derive_Zero.  eapply derive_pairL. cbv; apptac. apptac.
  all: cycle -1.
  eapply derive_Z.
  repeat eapply derive_app; ( eapply derive_s || eapply derive_k || apptac); eauto. eapply app_Z_out.  apptac. apptac.
  all: auto_t. 
Qed.
 
  
(*** Lists *)


Lemma app_ty_nil_c : forall ty, app_ty (p_type nil_c) ty (List ty). 
Proof. intros; cbv; apptac; eapply app_nil.  Qed. 

Lemma app_ty_cons_c : forall ty, app_ty (p_type cons_c) (Product ty (List ty)) (List ty). 
Proof. intros; cbv; apptac. eapply app_cons. Qed.


Lemma derive_fold_left_c:
  forall gamma f fty uty vty ty2 p,
    derive gamma f fty -> derive gamma p (Product uty (List vty)) -> app_ty fty uty ty2 -> app_ty ty2 vty uty ->
    derive gamma (fold_left_c f @ p) uty.
Proof.
  intros; eapply derive_Z_app. 2: eauto. cbv; repeat eapply derive_app; (eapply derive_s || eapply derive_k || apptac); eauto.
  apptac.   apptac. auto_t. eauto. auto_t. auto_t. eapply app_list_out. apptac. auto_t. auto_t. eauto. auto_t.
Qed.




