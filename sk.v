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
(*            Simply-Typed Combinators                                *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith Lia Bool List Nat Datatypes String.

Set Default Proof Using "Type".

Ltac refold r := unfold r; fold r.
Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f. 
Ltac auto_t := eauto with TreeHintDb. 
Ltac eapply2 H := eapply H; auto_t; try lia.
Ltac split_all := intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); subst; try contradiction
end; try congruence.

Ltac inv_out H := inversion H; clear H; subst.

Ltac disjunction_tac:=
  match goal with
  | H : _ \/ _ |- _ => inv_out H; disjunction_tac
  | _ => try lia
  end.


Ltac invsub := 
match goal with 
| H : _ = _ |- _ => injection H; clear H; invsub 
| _ => intros; subst
end. 


(* 8.2: SK-Calculus *) 


Inductive SK:  Set :=
| Ref : string -> SK  (* variables are indexed by strings *) 
| Sop : SK   
| Kop : SK
| App : SK -> SK -> SK   
.

Global Hint Constructors SK : TreeHintDb.

Open Scope string_scope. 
Declare Scope sk_scope.
Open Scope sk_scope. 

Notation "x @ y" := (App x y) (at level 65, left associativity) : sk_scope.

(*** tags all collected here *)

 
Definition fun_tag dummy := Kop @ dummy. (* see also funty_tag for types *)
Definition Z_tag := Kop. 
Definition product_tag := Sop @ Sop.
Definition bool_tag := Sop @ Kop.
Definition nat_tag := Sop @ Kop @ Kop. 

Definition Iop := Sop @ Kop @ Kop. 


(* SK-reduction *) 
Inductive sk_red1 : SK -> SK -> Prop :=
| ss_red: forall (M N P : SK), sk_red1 (Sop @M@ N@ P) (M@P@(N@P))
| k_red : forall M N, sk_red1 (Kop @ M@ N) M
| appl_red : forall M M' N, sk_red1 M M' -> sk_red1 (M@ N) (M' @ N)  
| appr_red : forall M N N', sk_red1 N N' -> sk_red1 (M@ N) (M@ N')  
.
Global Hint Constructors sk_red1 : TreeHintDb. 

(* Multiple reduction steps *) 

Inductive multi_step : (SK -> SK -> Prop) -> SK -> SK -> Prop :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: SK-> SK -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.
Global Hint Constructors multi_step : TreeHintDb.


Definition transitive red := forall (M N P: SK), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; intros; simpl;  auto. apply succ_red with N; auto. Qed. 

Definition preserves_appl (red : SK -> SK -> Prop) := 
forall M N M', red M M' -> red (M@ N) (M' @ N).

Definition preserves_appr (red : SK -> SK -> Prop) := 
forall M N N', red N N' -> red (M@ N) (M@ N').

Definition preserves_app (red : SK -> SK -> Prop) := 
forall M M', red M M' -> forall N N', red N N' -> red (M@ N) (M' @ N').

Lemma preserves_appl_multi_step : 
forall (red: SK -> SK -> Prop), preserves_appl red -> preserves_appl (multi_step red). 
Proof. red; intros red hy M N M' r; induction r; auto with TreeHintDb; eapply succ_red; eauto. Qed.

Lemma preserves_appr_multi_step : 
forall (red: SK -> SK -> Prop), preserves_appr red -> preserves_appr (multi_step red). 
Proof. red; intros red hy M N M' r; induction r; auto with TreeHintDb; eapply succ_red; eauto. Qed.


Lemma preserves_app_multi_step : 
forall (red: SK -> SK -> Prop), 
preserves_appl red -> preserves_appr red -> 
preserves_app (multi_step red). 
Proof.
red; intros red pl pr M M' rM N N' rN;  
  apply transitive_red with (M' @ N); [ apply preserves_appl_multi_step | apply preserves_appr_multi_step] ;
    auto.
Qed.



(* sk_red *) 

Definition sk_red := multi_step sk_red1.

Lemma sk_red_refl: forall M, sk_red M M. Proof. intros; apply zero_red. Qed.
Global Hint Resolve sk_red_refl : TreeHintDb. 

Lemma preserves_appl_sk_red : preserves_appl sk_red.
Proof. apply preserves_appl_multi_step. red; auto_t. Qed.

Lemma preserves_appr_sk_red : preserves_appr sk_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_sk_red : preserves_app sk_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.



Ltac eval_tac1 := 
match goal with 
| |-  sk_red ?M _ => red; eval_tac1
(* 4 apps *) 
| |- multi_step sk_red1 (_ @ _ @ _ @ _ @ _) _ => 
  eapply transitive_red;  [eapply preserves_app_sk_red; [eval_tac1|auto_t] |auto_t]
(* 3 apps *) 
| |- multi_step sk_red1 (Sop @ _ @ _ @ _) _  => eapply succ_red; auto_t 
| |- multi_step sk_red1 (Kop @ _ @ _ @ _) _ =>
    eapply transitive_red;  [eapply preserves_app_sk_red; [eval_tac1|auto_t] |]; auto_t
| |- multi_step sk_red1 (_ @ _ @ _ @  _) (_ @ _)  =>  eapply preserves_app_sk_red; eval_tac1
(* 2 apps *) 
| |- multi_step sk_red1 (Sop @ _ @ _) (Sop  @ _ @ _) _ =>
  apply preserves_app_sk_red; [ apply preserves_app_sk_red |]; eval_tac1
| |- multi_step sk_red1 (Kop @ _ @ _ )  _  => eapply succ_red; auto_t 
| |- multi_step sk_red1 (_ @ _ @ _) (_ @ _)  => eapply preserves_app_sk_red; eval_tac1
| |- multi_step sk_red1 (_ @ _) (_ @ _) => apply preserves_app_sk_red; eval_tac1
| _ => auto_t
end.

Ltac eval_tac := intros; cbv; repeat eval_tac1. 


Ltac zerotac := try apply zero_red.
Ltac succtac :=
  repeat (eapply transitive_red;
  [ eapply succ_red; auto_t ;
    match goal with | |- multi_step sk_red1 _ _ => idtac | _ => fail end
  | ])
.
Ltac aptac := eapply transitive_red; [ eapply preserves_app_sk_red |].
                                             
Ltac ap2tac:=
  unfold sk_red; 
  eassumption || 
              match goal with
              | |- multi_step _ (_ @ _) _ => try aptac; [ap2tac | ap2tac | ]
              | _ => idtac
              end. 

Ltac trtac := unfold Iop; succtac;  zerotac. 

Lemma i_red: forall M, sk_red (Iop @ M) M.
Proof. eval_tac. Qed. 

Lemma i_alt_red: forall y M, sk_red (Sop @Kop@ y@ M) M. 
Proof. eval_tac. Qed. 




Ltac inv1 prop := 
match goal with 
| H: prop (_ @ _) |- _ => inversion H; clear H; inv1 prop
| H: prop Sop |- _ => inversion H; clear H; inv1 prop
| H: prop Kop |- _ => inversion H; clear H; inv1 prop
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| _ =>  subst; intros; auto_t
 end.



Ltac inv red := 
match goal with 
| H: multi_step red (_ @ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red Sop _ |- _ => inversion H; clear H; inv red
| H: multi_step red Kop _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (_ @ _) _ |- _ => inversion H; clear H; inv red
| H: red Sop _ |- _ => inversion H; clear H; inv red
| H: red Kop _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (_ @ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ Sop |- _ => inversion H; clear H; inv red
| H: multi_step red _ Kop |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (_ @ _) |- _ => inversion H; clear H; inv red
| H: red _ Sop |- _ => inversion H; clear H; inv red
| H: red _ Kop |- _ => inversion H; clear H; inv red
| _ => subst; intros; auto_t
 end.




Definition implies_red (red1 red2: SK-> SK-> Prop) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; intros; auto with TreeHintDb. 
apply transitive_red with N; auto. 
Qed. 


Lemma to_sk_red_multi_step: forall red, implies_red red sk_red -> implies_red (multi_step red) sk_red. 
Proof. 
red.  intros red B M N R; induction R; intros.
red; intros; auto with TreeHintDb. 
assert(sk_red M N) by (apply B; auto). 
apply transitive_red with N; auto. 
apply IHR; auto with TreeHintDb. 
Qed.


Inductive s_red1 : SK -> SK -> Prop :=
| ref_s_red : forall i, s_red1 (Ref i) (Ref i)
| sop_s_red :  s_red1 Sop Sop
| kop_s_red :  s_red1 Kop Kop
| app_s_red :
  forall M M' ,
    s_red1 M M' ->
    forall N N' : SK, s_red1 N N' -> s_red1 (M@ N) (M' @ N')  
| s_s_red: forall (M M' N N' P P' : SK),
    s_red1 M M' -> s_red1 N N' -> s_red1 P P' ->                  
    s_red1  (Sop @M @ N @ P) (M' @ P' @ (N' @ P'))
| k_s_red : forall M  M' N,  s_red1 M M' -> s_red1 (Kop @ M @ N) M'
.

Global Hint Constructors s_red1 : TreeHintDb.

Lemma s_red_refl: forall M, s_red1 M M.
Proof. induction M; intros; auto with TreeHintDb. Qed. 

Global Hint Resolve s_red_refl : TreeHintDb.

     
Definition s_red := multi_step s_red1.

Lemma preserves_appl_s_red : preserves_appl s_red.
Proof. apply preserves_appl_multi_step. red; auto_t. Qed.

Lemma preserves_appr_s_red : preserves_appr s_red.
Proof. apply preserves_appr_multi_step. red; auto_t. Qed.

Lemma preserves_app_s_red : preserves_app s_red.
Proof. apply preserves_app_multi_step;  red; auto_t. Qed.


Lemma sk_red1_to_s_red1 : implies_red sk_red1 s_red1.
Proof. red; intros M N B; induction B; intros; auto with TreeHintDb. Qed. 


Lemma sk_red_to_s_red: implies_red sk_red s_red.
Proof.
  apply implies_red_multi_step.
  red; intros.  eapply succ_red. eapply sk_red1_to_s_red1; auto_t. apply zero_red.
Qed. 


Lemma s_red1_to_sk_red: implies_red s_red1 sk_red .
Proof.
  intros M N OR; induction OR; auto_t.
  all: try (eapply succ_red; auto_t; fail).
  all: try (ap2tac; zerotac). 
  all:   eapply succ_red; auto_t.
Qed.

Global Hint Resolve s_red1_to_sk_red: TreeHintDb.

Lemma s_red_to_sk_red: implies_red s_red sk_red. 
Proof. apply to_sk_red_multi_step; auto_t. Qed.


Ltac exist x := exists x; split_all; auto_t.



(* Diamond Lemmas *) 


Definition diamond (red1 red2 : SK -> SK -> Prop) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof.
  unfold diamond; intros red1 red2 d1 M N r1 P r2; elim (d1 M P r2 N r1); intros x (?&?);
    exists x; tauto.
Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof.
  intros red1 red2 d; eapply diamond_flip; intros M N r; induction r;
    [intro P; exist P |
     intros P0 r0;
     elim (d M P0 r0 N); auto_t; intros x (?&?);  
     elim(IHr d x); auto; intros x0 (?&?); exist x0;  eapply2 succ_red
    ]. 
Qed. 


Definition diamond_star (red1 red2: SK -> SK -> Prop) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
  intros red1 red2 d M N r; induction r; intros P0 r0;
  [ exist P0 | 
  elim(d M _ r0 N); auto; intros x (r1&r2);   
  elim(IHr d x); auto; intros x0 (?&?); 
  exist x0; eapply2 transitive_red
    ]. 
Qed. 

Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
  intros red1 red2 d M N r; induction r as [| ? ? ? ? r1 r2]; 
    [  intro P; exist P |
       intros P0 r0; 
       elim(diamond_strip red red2 d M N r1 P0); auto;
       intros N3 (r3&?); 
       elim(IHr2 d N3 r3); intros P1 (?&?);  
       exist P1;  eapply2 succ_red
  ].  
Qed. 

Global Hint Resolve diamond_tiling: TreeHIntDb. 



Lemma diamond_s_red1 : diamond s_red1 s_red1. 
Proof.  
  intros M N r; induction r; intros P0 rP; auto_t.
  - inversion rP; clear rP; subst; inv s_red1; inv s_red1; auto_t.
    + elim(IHr1 M'0); auto; intros x (?&?);
      elim(IHr2 N'0); auto; intros x0 (?&?); exists (x@ x0); split; auto_t.
    + elim(IHr1 (Sop @ M'0 @ N'0)); auto_t; intros x (?&?); inv s_red1; invsub. 
      elim(IHr2 P'); auto_t; intros x (?&?).
      exist (N'4 @ x @ (N'3 @ x)).
    + elim(IHr1 (Kop@ P0)); auto_t; intros x (?&?); inv s_red1; invsub; auto_t. 
  - inv_out rP. inv s_red1. 
    eelim (IHr1 N'2); intros; auto_t.
    eelim (IHr2 N'1); intros; auto_t.
    eelim (IHr3 N'0); intros; auto_t.
    split_all.
    exist (x @ x1 @ (x0 @ x1)). 
    eelim (IHr1 M'0); intros; auto_t.
    eelim (IHr2 N'0); intros; auto_t.
    eelim (IHr3 P'0); intros; auto_t.
    split_all.
    exist (x @ x1 @ (x0 @ x1)). 
  - inv_out rP. inv s_red1. 
    eelim (IHr N'0); intros; auto_t.
    split_all.
    exist x.
    eelim (IHr P0); intros; auto_t.
Qed.


Global Hint Resolve diamond_s_red1: TreeHintDb.

Lemma diamond_s_red1_s_red : diamond s_red1 s_red.
Proof. eapply diamond_strip; auto_t. Qed. 

Lemma diamond_s_red : diamond s_red s_red.
Proof.  apply diamond_tiling; auto_t. Qed. 
Global Hint Resolve diamond_s_red: TreeHIntDb.


(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem confluence_s_red: confluence SK s_red. 
Proof. red; intros; eapply diamond_s_red; auto_t. Qed. 


 

Theorem confluence_sk_red: confluence SK sk_red. 
Proof. 
  red; intros.
  match goal with H: sk_red ?x ?y , H1 : sk_red ?x ?z |- _ => 
                  assert(py: s_red x y) by  (apply sk_red_to_s_red; auto_t);
                    assert(pz: s_red x z) by (apply sk_red_to_s_red; auto_t);
                    elim(diamond_s_red x y py z); auto_t end.
  intros x0 (?&?); exists x0; split; auto_t; apply s_red_to_sk_red; auto_t. 
Qed. 
Global Hint Resolve confluence_sk_red: TreeHintDb.

(* programs *)

Inductive program : SK -> Prop :=
| pr_S0 : program Sop
| pr_S1 : forall M, program M -> program (Sop @ M)
| pr_S2 : forall M1 M2, program M1 -> program M2 -> program (Sop @ M1 @ M2)
| pr_K0 : program Kop
| pr_K1 : forall M, program M -> program (Kop @ M) .

Global Hint Constructors program: TreeHintDb.


Ltac program_tac :=
  cbv; repeat (apply pr_S0 || apply pr_S1 || apply pr_S2 || apply pr_K0 || apply pr_K1); auto_t. 


(* normal forms *) 

Inductive active : SK -> Prop := 
| active_ref : forall i, active (Ref i)
| active_app : forall M N, active M -> active (M@ N)
.


Inductive normal : SK -> Prop := 
| nf_ref : forall i, normal (Ref i)
| nf_S : normal Sop
| nf_K : normal Kop                
| nf_app : forall M N, active M -> normal M -> normal N -> normal (M@ N)
| nf_S1 : forall M, normal M -> normal (Sop @ M)
| nf_K1 : forall M, normal M -> normal (Kop @ M)
| nf_S2 : forall M N, normal M -> normal N -> normal (Sop @ M @ N)
.


Global Hint Constructors active normal : TreeHintDb.


Lemma active_sk_red1 :
  forall M, active M -> forall N, sk_red1 M N  -> active N.
Proof.  intros M a; induction a; intros; inv sk_red1; inv_out a; inv_out H0; inv_out H1. Qed.   

  
Lemma active_sk_red2:
  forall M N P, active M -> sk_red1 (M@ N) P ->
                (exists M1, P = M1 @ N /\ sk_red1 M M1)
                \/ (exists N1, P = M@ N1 /\ sk_red1 N N1).
Proof. induction M; intros; inv sk_red1; auto_t; inv_out H; inv_out H1; inv_out H0. Qed. 
                      

Lemma active_sk_red:
  forall M N P, active M -> sk_red (M@ N) P ->
                (exists M1 N1, P = M1 @ N1 /\ sk_red M M1 /\ sk_red N N1).
Proof.
  cut(forall red M P, multi_step red M P -> red = sk_red1 -> 
forall M1 M2, M = M1 @ M2 -> active M1 -> 
                (exists P1 P2, P = P1 @ P2 /\ sk_red M1 P1 /\ sk_red M2 P2)).
    intro c;  intros; eapply2 c.

    intros red M P r; induction r; intros; subst; auto_t; inv sk_red1; inv1 active.
  - eelim IHr; [ | auto | auto_t| eapply active_sk_red1; auto_t].  
      intros x ex; elim ex; intros P2 (?&?&?); subst;
      repeat eexists; auto_t; eapply succ_red; auto_t. 
  - eelim IHr;  [ | auto | auto_t |]; auto; intros x ex; elim ex; intros x0 (?&?&?); subst;
       exists x; exist x0 ; eapply2 succ_red.    
Qed.



Lemma normal_is_irreducible: forall M, normal M -> forall N, sk_red1 M N -> False.
Proof.
  intros M n; induction n; intros; inv sk_red1;
    ((apply IHn1; fail) || (apply IHn2; fail) || (apply IHn; fail) || inv1 active).  
Qed.


Lemma active_is_stable:
  forall M N P, active M -> s_red1 (M@ N) P ->
                (exists M1 N1, P = M1 @ N1 /\ s_red1 M M1 /\ s_red1 N N1).
Proof.
  induction M; intros N P a r; inv s_red1; auto_t; inversion a; subst; eauto 10 with *; inv1 active.
Qed.   


Lemma normal_is_stable: forall M, normal M -> forall N, s_red1 M N -> N = M.
Proof. intros M n; induction n; intros; inv s_red1; repeat f_equal; auto; inv1 active. Qed.


Lemma normal_is_stable2: forall M N, s_red M N -> normal M -> N = M.
Proof.
  cut(forall red M N, multi_step red M N -> red = s_red1 -> normal M -> N = M); 
  [ intro c; intros; eapply2 c  
  | intros red M N r; induction r; intros; subst; auto_t; 
    assert(N = M) by (eapply normal_is_stable; eauto); subst; auto
  ].
  Qed.


Lemma triangle_s_red : forall M N P, s_red M N -> s_red M P -> normal P -> s_red N P.
Proof.
  intros; assert(d: exists Q, s_red N Q /\ s_red P Q) by (eapply diamond_s_red; auto_t);
  elim d; intros x (?&?); 
  assert(x = P) by (eapply normal_is_stable2; eauto);  subst; auto. 
Qed.


Lemma programs_are_normal: forall M, program M -> normal M.
Proof.  intros M pr; induction pr; intros; auto_t. Qed. 


Definition normalisable M := exists N,  sk_red M N /\ program N.


Ltac normal_tac :=
  cbv;
  repeat (apply nf_S2 || apply nf_K1 || apply nf_S1 || apply nf_app ||
          apply nf_K || apply nf_S || apply nf_ref);
  apply programs_are_normal; 
  auto_t. 

Ltac stable_tac :=
  match goal with
  | H : s_red ?Q ?R |- _ =>
    assert(R=Q) by (apply normal_is_stable2; auto_t; cbv; normal_tac); clear H 
  | H : s_red1 ?Q ?R |- _ =>
    assert(R=Q) by (apply normal_is_stable; auto_t; cbv; normal_tac); clear H
  | H : sk_red ?Q ?R |- _ => assert(s_red Q R) by (apply sk_red_to_s_red; auto_t); clear H; stable_tac 
  | _ => auto_t
  end; subst; try discriminate.




(*** Tags *)

(* tag is chosen to avoid lambda-abstractions but be typable on application to any K t
 tagged f t tags f by t without changing its functionality
 *) 


Definition tag := Sop @ (Sop @ (Kop @ Kop) @ (Kop @ Kop)).

Theorem tag_red: forall t x, sk_red (tag @ t @ x) Kop. 
Proof. eval_tac. Qed.


Definition tagged f t := Sop @ (Sop @ (Kop @ Kop) @ f) @ (tag @ (Kop @ t)).

Theorem tagged_red: forall f t x, sk_red (tagged f t @ x) (f @ x).
Proof. eval_tac. Qed.



(* lambda-abstraction *)

Fixpoint bracket x M := 
match M with 
| Ref y =>  if eqb x y then Iop else (Kop @ (Ref y))
| M1 @ M2 => Sop @ (bracket x M1) @ (bracket x M2)
| _ => Kop @ M 
end
.


(*** star abstraction *)


Fixpoint occurs x M :=
  match M with
  | Ref y => eqb x y
  | M1 @ M2 => (occurs x M1) || (occurs x M2)
  | _ => false
  end.


Fixpoint star x M :=
  match M with
  | Ref y => if eqb x y then Iop else Kop @ (Ref y)
  (*   no eta-contraction now
| M1 @ (Ref y) => 
    if eqb x y
    then if negb (occurs x M1)
         then M1 (* eta_red *) 
         else Sop @ (star x M1) @ Iop
    else if negb (occurs x M1)
         then Kop @ (M1 @ (Ref y))
         else Sop @ (star x M1) @ (Kop @ (Ref y))
*) 
  | M1 @ M2 => if occurs x (M1 @ M2)
                 then Sop @ (star x M1) @ (star x M2) 
                 else Kop @ (M1 @ M2)
  | _ => Kop @ M
  end.



Lemma star_id: forall x, star x (Ref x) = Iop.
Proof. intro; unfold star, occurs; rewrite eqb_refl; auto. Qed.


Lemma star_occurs_false: forall M x, occurs x M = false -> star x M = Kop @ M. 
Proof. induction M; simpl in *; auto_t; intros x occ;  rewrite occ; auto. Qed.


Lemma star_occurs_true:
  forall M1 M2 x, occurs x (M1 @ M2) = true -> (* M2 <> Ref x -> *) star x (M1 @ M2) = Sop @ (star x M1) @ (star x M2).
Proof. intros; simpl in *; rewrite H; auto. Qed.


Ltac startac x :=
  repeat ( (rewrite (star_occurs_true _ _ x); [| unfold occurs; fold occurs; rewrite ? orb_true_r; simpl; auto; fail])  ||
          rewrite star_id || 
          (rewrite (star_occurs_false _ x); [| unfold occurs; fold occurs; auto; cbv; auto; fail])
         ).


Notation "\" := star : sk_scope.


Theorem tagged_not_star: forall u x f t, \ x u <> tagged f t.
Proof.
  intros; caseEq u; intros; subst; simpl; try discriminate.
  caseEq (x=?s); intros; try discriminate. 
  caseEq (occurs x s || occurs x s0); intros; try discriminate.
  intro; inv_out H0. clear - H3.
  caseEq s0; intros; subst; simpl in *; try discriminate.
  caseEq (x=?s); intros; rewrite H in *; try discriminate. 
  caseEq (occurs x s || occurs x s1); intros; rewrite H in *; try discriminate.
  inv_out H3. clear - H1. 
  caseEq s; intros; subst; simpl in *; try discriminate.
  caseEq (x=?s0); intros; rewrite H in *; try discriminate. 
  caseEq (occurs x s0 || occurs x s1); intros; rewrite H in *; try discriminate.
  inv_out H1.
  caseEq s0; intros; subst; simpl in *; try discriminate.
  caseEq (x=?s); intros; rewrite H0 in *; try discriminate. 
  caseEq s1; intros; subst; simpl in *; try discriminate.
  rewrite H in *; simpl in *; try discriminate.
  rewrite H in *; simpl in *; try discriminate.
  caseEq (occurs x s || occurs x s2); intros; rewrite H0 in *; simpl in *; try discriminate.
Qed.


  
Lemma programs_are_closed: forall p, program p -> forall x, occurs x p = false. 
Proof. intros p pr; induction pr; intros; simpl; auto_t; rewrite IHpr1; simpl; auto. Qed. 

 

(*** Pairing and projections *)

Definition KI := Kop @ Iop.
Definition pairL := \"x" (\"y" (tagged (\"f" (Ref "f" @ Ref "x" @ Ref "y")) product_tag)).
Definition fstL := Sop @ Iop @ (Kop @ Kop). 
Definition sndL := Sop @ Iop @ (Kop @ KI). 

Lemma pairL_red: forall x y f, sk_red (pairL @ x @ y @ f) (f @ x @ y).
Proof. eval_tac. Qed.

Theorem fstL_red: forall x y, sk_red (fstL @ (pairL @ x @ y)) x. Proof. eval_tac.  Qed. 
Theorem sndL_red: forall x y, sk_red (sndL @ (pairL @ x @ y)) y. Proof. eval_tac. Qed. 


(*** Booleans *)


Definition tt := tagged fstL bool_tag.
Definition ff := tagged sndL bool_tag. 
Definition cond := \"b" (\"x" (\"y" (Ref "b" @ (pairL @ Ref "x" @ Ref "y")))).

Lemma cond_true: forall M N, sk_red (cond @ tt @ M @ N) M.
Proof. eval_tac. Qed.

Lemma cond_false: forall M N, sk_red (cond @ ff @ M @ N) N.
Proof. eval_tac. Qed.




(*** Natural numbers, using the Scott encoding, and then tagging  *)


Definition Zero := tagged fstL nat_tag.

Definition Succ := \"n" (tagged (Sop @ sndL @ (Kop @ Ref "n")) nat_tag).

Lemma Zero_red: forall x f, sk_red (Zero @ (pairL @ x @ f)) x.
Proof. eval_tac. Qed. 

Lemma Succ_red : forall n x f, sk_red (Succ @ n @ (pairL @ x @ f)) (f @ n).
Proof. eval_tac. Qed. 


Definition num k := iter k (fun x => Succ @ x) Zero.


Lemma num_succ_red: forall k, sk_red (num (S k)) (Succ @ (num k)).
Proof. intros; simpl; eapply zero_red. Qed.  

  
(*** The zero test and conditionals *)


Definition isZero := \"n" (Ref "n" @ (pairL @ tt @ (Kop @ ff))).

Theorem isZero_zero: sk_red (isZero @ Zero) tt.
Proof.  eval_tac. Qed.

Theorem isZero_succ: forall n, sk_red (isZero @ (Succ @ n)) ff.
Proof.  eval_tac. Qed.


(*** The predecessor function  - underpinning primitive recursion *) 

Definition predN := \"n" (Ref "n" @ (pairL @ Zero @ Iop)).

Theorem pred_red: forall k,  sk_red (predN @ (num k)) (num (pred k)). 
Proof. intros; unfold predN; caseEq k; intros; subst. eapply succ_red. cbv. eval_tac. eval_tac. simpl. eval_tac.  Qed.



(*** Sum types *)


Definition sum_tag := Sop @ Kop @ Sop.

Definition inl_c := \"p" (tagged (pairL @ tt @ Ref "p") sum_tag). 
Definition inr_c := \"p" (tagged (pairL @ ff @ Ref "p") sum_tag). 
Definition case_c := \"p" (\"c" (fstL @ Ref "c" @ (pairL @ (fstL @ Ref "p" @ (fstL @ (sndL @ Ref "c"))) @ (sndL @ Ref "p" @ (sndL @ (sndL @ Ref "c")))))).


Lemma case_inl_red: forall u d f g, sk_red (case_c @ (pairL @ f @ g) @ (inl_c @ (pairL @ u @ d))) (f @ u).
Proof. eval_tac. Qed.

Lemma case_inr_red: forall d v f g, sk_red (case_c @ (pairL @ f @ g) @ (inr_c @ (pairL @ d @ v))) (g @ v).
Proof. eval_tac. Qed.



(*** Waiting *) 

Definition wait M N := Sop @ (Sop @ (Kop @ M) @ (Kop @ N)) @ Iop.
Definition Wop := \"x" (\"y" (wait (Ref "x") (Ref "y"))). 

Lemma wait_red: forall M N P, sk_red (wait M N @ P) (M@ N @ P).
Proof.  intros; cbv; repeat (eapply2 succ_red). Qed. 

 
Lemma w_red1 : forall M N, sk_red (Wop @ M @ N) (wait M N).
Proof.  eval_tac.  Qed.    

Lemma w_red : forall M N P, sk_red (Wop @ M@ N @ P) (M@ N @ P).
Proof.  eval_tac.  Qed.

Definition wait2 M N x :=  Sop @ (Sop @ (Sop @ (Kop @ M) @ (Kop @ N)) @ (Kop @ x)) @ Iop.

Lemma wait2_red: forall M N x y, sk_red (wait2 M N x @ y) (M @ N @ x @ y).
Proof. eval_tac. Qed. 



(*** Function types and Fixpoints *)


Definition lam x M dummy := tagged (\x M) (Kop @ dummy).
(* Kop @ d is the tag of a function type that can act on d. No uninhabited argument types yet ! *) 



Definition omega_z :=
  \"w"
    (\"f"
       (\"x"
          (Ref "f" @
             (tagged
                (tagged
                   (wait2 (Ref "w") (Ref "w") (Ref "f")) (* delay reduction of w *) 
                   Z_tag)                                (* to make a Rec type *) 
                (Kop @ Ref "x"))                         (* to make a function type *) 
             @ Ref "x"))). 

Definition Z f := tagged (wait2 omega_z omega_z f) Z_tag. 

Lemma omega_z_red: forall w f x, sk_red (omega_z @ w @ f @ x) (f @ tagged (tagged (wait2 w w f) Z_tag) (Kop @ x) @ x). Proof.
  intros; unfold omega_z at 1.  unfold tagged at 1 2. unfold wait2; startac "x"; startac "f"; startac "w"; trtac.
  eapply preserves_appl_sk_red. eapply preserves_appr_sk_red.   trtac. eapply preserves_appl_sk_red. eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  aptac. trtac. trtac. eapply succ_red. eapply ss_red.
  aptac. 2: trtac. 2: eapply zero_red.
  eapply succ_red. eapply ss_red.  
  aptac.  trtac. 2: eapply zero_red. eapply succ_red. eapply ss_red.  
  aptac.   trtac. 2: eapply zero_red. 
  aptac. aptac.  eapply succ_red. eapply ss_red.  
  aptac. trtac. 2: eapply zero_red. 2: trtac. 2,3: eapply zero_red. eapply zero_red.
  eapply succ_red. eapply ss_red.
  aptac. 2: trtac. 2: eapply zero_red.
  aptac. eapply succ_red. eapply ss_red.   
  aptac. trtac. 1-3: eapply zero_red.
  eapply succ_red. eapply ss_red.   
  aptac. trtac. eapply zero_red.
  eapply preserves_appr_sk_red.
  aptac. eapply succ_red. eapply ss_red.
  aptac. eapply succ_red. eapply ss_red.
  aptac. trtac. all: try eapply zero_red. 
  eapply succ_red. eapply ss_red.   
  aptac. aptac. eapply succ_red. eapply ss_red.   
  aptac. trtac. trtac. trtac. trtac. trtac. trtac. eapply zero_red.
Qed. 



Theorem Z_red: forall f x, sk_red (Z f @ x) (f @ (tagged (Z f) (Kop @ x)) @ x).
Proof. intros; unfold Z; eapply transitive_red; [ eapply tagged_red | eapply transitive_red; [ eapply wait2_red | eapply omega_z_red]]. Qed.


(*** Primitive Recursion *)



Definition primrec0_abs :=
  \"z" (\"p" (* p : V * Nat *) 
     (sndL @ Ref "p"
        @ (pairL @ Ref "g" @ (\"n1" (Ref "h" @ Ref "n1" @ (Ref "z" @ (pairL @ (fstL @ Ref "p") @ Ref "n1"))))             
   ))).

Lemma primrec0_val:
  primrec0_abs =
     Sop @ (Kop @ (Sop @ (Sop @ (Kop @ sndL) @ Iop))) @
  (Sop @ (Kop @ (Sop @ (Kop @ (pairL @ Ref "g")))) @
   (Sop @ (Kop @ (Sop @ (Kop @ (Sop @ (Sop @ (Kop @ Ref "h") @ Iop))))) @
    (Sop @
     (Sop @ (Kop @ Sop) @
      (Sop @ (Kop @ Kop) @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ Kop) @ Iop)))) @
     (Kop @
      (Sop @
       (Sop @ (Kop @ Sop) @
        (Sop @ (Kop @ Kop) @ (Sop @ (Kop @ pairL) @ (Sop @ (Kop @ fstL) @ Iop)))) @
       (Kop @ Iop)))))) .
Proof. unfold primrec0_abs; startac "n1"; startac "p"; startac "z"; auto. Qed.



Definition primrec0 g h := Z (
                                  Sop @ (Kop @ (Sop @ (Sop @ (Kop @ sndL) @ Iop))) @
  (Sop @ (Kop @ (Sop @ (Kop @ (pairL @ g)))) @
   (Sop @ (Kop @ (Sop @ (Kop @ (Sop @ (Sop @ (Kop @ h) @ Iop))))) @
    (Sop @
     (Sop @ (Kop @ Sop) @
      (Sop @ (Kop @ Kop) @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ Kop) @ Iop)))) @
     (Kop @
      (Sop @
       (Sop @ (Kop @ Sop) @
        (Sop @ (Kop @ Kop) @ (Sop @ (Kop @ pairL) @ (Sop @ (Kop @ fstL) @ Iop)))) @
       (Kop @ Iop)))))) ).

Lemma primrec0_red_zero :  forall g h v, sk_red (primrec0 g h @ (pairL @ v @ Zero)) g.
Proof.
  intros; eapply transitive_red; [eapply Z_red | trtac].
  aptac. eapply sndL_red. eapply zero_red. eapply Zero_red.
Qed.

Lemma primrec0_red_succ :  forall g h v n, sk_red (primrec0 g h @ (pairL @ v @ (Succ @ n))) (h @ n @ (primrec0 g h @ (pairL @ v @ n))).
Proof. 
  intros. eapply transitive_red. eapply Z_red. trtac. aptac. eapply sndL_red. eapply zero_red. simpl. 
  eapply transitive_red. eapply Succ_red. trtac. eapply preserves_appr_sk_red. trtac. eapply transitive_red. eapply tagged_red.   
  eapply preserves_appr_sk_red. eapply preserves_appl_sk_red. eapply preserves_appr_sk_red. eapply fstL_red.
Qed.
  

Definition primrec g h x := primrec0 (g @ x) (h @ x).


Lemma primrec_red:
  forall g h u v n, sk_red (primrec g h u @ (pairL @ v @ Zero)) (g @ u) /\  
    sk_red (primrec g h u @ (pairL @ v @ (Succ @ n))) (h @ u @ n @ (primrec g h u @ (pairL @ v @ n))).
Proof.  intros; simpl; split.  eapply primrec0_red_zero. eapply primrec0_red_succ. Qed. 




Definition prim_plus0 m n := primrec Iop (Kop @ (Kop @ Succ)) m @ (pairL @ Zero @ n).

Definition prim_plus := \"m" (\"n" (prim_plus0 (Ref "m") (Ref "n"))). 

Theorem prim_plus_zero: forall m, sk_red (prim_plus @ m @ Zero) m. 
Proof. intros; eval_tac. Qed.

Theorem prim_plus_Succ: forall m n, sk_red (prim_plus @ m @ (num (S n))) (Succ @ (prim_plus0 m (num n))). 
Proof.
  intros.  unfold prim_plus.
  unfold prim_plus0 at 1; unfold primrec, primrec0, Z, tagged, wait2; startac "n"; startac "m"; trtac. 
  eapply transitive_red. eapply omega_z_red. trtac.   
  aptac. eapply sndL_red. trtac. simpl. eapply transitive_red. eapply Succ_red. aptac. trtac. eapply zero_red.
  trtac. eapply preserves_appr_sk_red.
  eapply transitive_red. eapply tagged_red.
  aptac. 2: trtac. 
  all: cycle 1. 
  aptac.   eapply zero_red. aptac. aptac. trtac. eapply fstL_red. 1,2,3: eapply zero_red. 2: eapply zero_red.
  eapply preserves_appl_sk_red.
  unfold primrec, primrec0, Z.
  eapply preserves_appl_sk_red.
  eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  eapply preserves_appl_sk_red.
  eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  aptac. aptac. trtac. 1,2,3: eapply zero_red. 
  eapply preserves_app_sk_red.
  eapply preserves_appr_sk_red.
  trtac.
  eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  aptac. eapply succ_red. eapply k_red. eapply zero_red. trtac. eapply zero_red.

  aptac. eapply succ_red. eapply ss_red. aptac. trtac. all: try eapply zero_red.
  eapply preserves_app_sk_red.
  eapply preserves_appr_sk_red.
  eapply succ_red. eapply ss_red. aptac. trtac. all: try eapply zero_red.
  eapply preserves_appr_sk_red.
  eapply succ_red. eapply ss_red. aptac. trtac. all: try eapply zero_red.
  eapply preserves_appr_sk_red.
  trtac.
  eapply preserves_appr_sk_red.
  eapply preserves_appr_sk_red.
  eapply preserves_appl_sk_red.
  eapply preserves_appr_sk_red.
  aptac. trtac. eapply zero_red. 
  eapply preserves_appr_sk_red.
  eapply succ_red. eapply ss_red. 
  eapply preserves_app_sk_red.
  eapply succ_red. eapply k_red. eapply zero_red. trtac.
  eapply succ_red. eapply k_red. eapply zero_red. 
Qed.

  
(*** Minimisation *)

 
Definition minrec_abs :=
  \"z" (\"vn" (cond @ (Ref "f" @ (sndL @ Ref "vn")) @ (sndL @ Ref "vn") @ (Ref "z" @ (pairL @ (fstL @ Ref "vn") @ (Succ @ (sndL @ Ref "vn")))))).

Lemma min_rec_abs_val :
  minrec_abs =
 Sop @
  (Kop @
   (Sop @
    (Sop @
     (Sop @ (Kop @ cond) @ (Sop @ (Kop @ Ref "f") @ (Sop @ (Kop @ sndL) @ Iop))) @
     (Sop @ (Kop @ sndL) @ Iop)))) @
  (Sop @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ Kop) @ Iop)) @
   (Kop @
    (Sop @ (Sop @ (Kop @ pairL) @ (Sop @ (Kop @ fstL) @ Iop)) @
     (Sop @ (Kop @ Succ) @ (Sop @ (Kop @ sndL) @ Iop))))).
Proof. unfold minrec_abs; startac "vn"; startac "z"; auto. Qed. 


Definition minrec0 f :=
  Z ( Sop @
  (Kop @
   (Sop @
    (Sop @
     (Sop @ (Kop @ cond) @ (Sop @ (Kop @ f) @ (Sop @ (Kop @ sndL) @ Iop))) @
     (Sop @ (Kop @ sndL) @ Iop)))) @
  (Sop @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ Kop) @ Iop)) @
   (Kop @
    (Sop @ (Sop @ (Kop @ pairL) @ (Sop @ (Kop @ fstL) @ Iop)) @
     (Sop @ (Kop @ Succ) @ (Sop @ (Kop @ sndL) @ Iop)))))).
  
Lemma minrec0_found: forall f n v, sk_red (f @ n) tt -> sk_red (minrec0 f @ (pairL @ v @ n)) n. 
Proof.
  intros; unfold minrec0; eapply transitive_red; [ eapply Z_red | ].
  trtac. aptac. aptac. aptac. trtac. aptac. trtac. trtac. aptac. trtac. eapply sndL_red. eauto. trtac. trtac. trtac. eapply tagged_red.
  eapply transitive_red. eapply cond_true. eapply sndL_red. 
Qed. 

Lemma minrec0_next: forall f n v, sk_red (f @ n) ff -> sk_red (minrec0 f @ (pairL @ v @ n)) (minrec0 f @ (pairL @ v @ (Succ @ n))).
Proof.
  intros; unfold minrec0; eapply transitive_red; [ eapply Z_red | ].
  trtac. aptac. aptac. aptac. trtac. aptac. trtac. trtac. aptac. trtac. eapply sndL_red. eauto. trtac. trtac. trtac. eapply tagged_red.
  eapply transitive_red. eapply cond_false. eapply preserves_appr_sk_red. 
  eapply preserves_app_sk_red. eapply preserves_appr_sk_red. trtac. eapply fstL_red.
  eapply preserves_appr_sk_red. trtac. eapply sndL_red.
Qed. 


Definition minrec f x := Sop @ (Kop @ (minrec0 (f@x))) @ (pairL @ Zero).


Lemma minrec_red:
  forall f x n, (sk_red (f @ x @ n) tt -> sk_red (minrec f x @ n) n) /\
                  (sk_red (f @ x @ n) ff -> sk_red (minrec f x @ n) (minrec0 (f@ x) @ (pairL @ Zero @ (Succ @ n)))). 
Proof. intros; unfold minrec; split; intros; trtac; [eapply minrec0_found; eauto | eapply minrec0_next; eauto]. Qed.


(*** Lists *)


Definition list_tag u := Sop @ (Sop @ Sop) @ u.

Definition nil_c := \"d" (tagged fstL (list_tag (Ref "d"))). 
Definition cons_c := \"p" (tagged (\"q" (sndL @ Ref "q" @ Ref "p")) (list_tag (fstL @ Ref "p"))).

Definition fold_left_c_abs :=
  \"z"
    (\"p"
       (sndL @
          Ref "p" @
          (pairL @
             (fstL @ Ref "p") @
             (\"q" (Ref "z" @ (pairL @ (Ref "f" @ (fstL @ Ref "p") @ (fstL @ Ref "q")) @ (sndL @ Ref "q"))))))).

Lemma fold_left_c_val: fold_left_c_abs =
                Sop @ (Kop @ (Sop @ (Sop @ (Kop @ sndL) @ Iop))) @
  (Sop @ (Kop @ (Sop @ (Sop @ (Kop @ pairL) @ (Sop @ (Kop @ fstL) @ Iop)))) @
   (Sop @
    (Sop @ (Kop @ Sop) @
     (Sop @ (Kop @ Kop) @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ Kop) @ Iop)))) @
    (Kop @
     (Sop @
      (Sop @ (Kop @ Sop) @
       (Sop @ (Kop @ (Sop @ (Kop @ pairL))) @
        (Sop @
         (Sop @ (Kop @ Sop) @
          (Sop @ (Kop @ Kop) @
           (Sop @ (Kop @ Ref "f") @ (Sop @ (Kop @ fstL) @ Iop)))) @
         (Kop @ (Sop @ (Kop @ fstL) @ Iop))))) @
      (Kop @ (Sop @ (Kop @ sndL) @ Iop)))))).
Proof.  unfold fold_left_c_abs; startac "q"; startac "p"; startac "z"; auto. Qed. 

Definition fold_left_c f :=
  Z(              Sop @ (Kop @ (Sop @ (Sop @ (Kop @ sndL) @ Iop))) @
  (Sop @ (Kop @ (Sop @ (Sop @ (Kop @ pairL) @ (Sop @ (Kop @ fstL) @ Iop)))) @
   (Sop @
    (Sop @ (Kop @ Sop) @
     (Sop @ (Kop @ Kop) @ (Sop @ (Kop @ Sop) @ (Sop @ (Kop @ Kop) @ Iop)))) @
    (Kop @
     (Sop @
      (Sop @ (Kop @ Sop) @
       (Sop @ (Kop @ (Sop @ (Kop @ pairL))) @
        (Sop @
         (Sop @ (Kop @ Sop) @
          (Sop @ (Kop @ Kop) @
           (Sop @ (Kop @ f) @ (Sop @ (Kop @ fstL) @ Iop)))) @
         (Kop @ (Sop @ (Kop @ fstL) @ Iop))))) @
      (Kop @ (Sop @ (Kop @ sndL) @ Iop))))))).
  

Lemma case_nil_red: forall d x f, sk_red (nil_c @ d @ (pairL @ x @ f)) x. 
Proof. eval_tac. Qed.

Lemma case_cons_red: forall p x f, sk_red (cons_c @ p @ (pairL @ x @ f)) (f @ p).
Proof. eval_tac. Qed.

Lemma fold_left_red: forall f u d h t, sk_red (fold_left_c f @ (pairL @ u @ (nil_c @ d))) u /\
                                         sk_red (fold_left_c f @ (pairL @ u @ (cons_c @ (pairL @ h @ t)))) (fold_left_c f @ (pairL @ (f @ u @ h) @ t)).
Proof.
  intros; split; unfold fold_left_c at 1; (eapply transitive_red; [ eapply Z_red | trtac]). 
  eval_tac.
  aptac.  eapply sndL_red. trtac. eapply transitive_red. eapply case_cons_red. trtac. eapply transitive_red. eapply tagged_red.
  eapply preserves_appr_sk_red.
  eapply preserves_app_sk_red.
  eapply preserves_appr_sk_red.
  trtac.
  eapply preserves_app_sk_red.
  eapply preserves_appr_sk_red.
  eapply fstL_red.
  eapply fstL_red.
  eapply sndL_red.
Qed.

