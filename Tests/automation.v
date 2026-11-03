(* Regression checks for the Classic-mode Ltac2 adapters and legacy entry points. *)
From Stdlib Require Import NArith.
Require Import Picinae_i386.
Open Scope N_scope.

Goal forall n:N, n + 0 = n.
Proof. intros. psimpl. reflexivity. Qed.
Goal forall n:N, n + 0 = n.
Proof. intros. psimpl_ltac1. reflexivity. Qed.
Goal forall n:N, n + 0 = n -> n = n.
Proof. intros n H. psimpl in H. exact H. Qed.
Goal forall n:N, n + 0 = n.
Proof. intros. psimpl (N.add _ 0). reflexivity. Qed.
Goal forall n:N, n + 0 = n -> n = n.
Proof. intros n H. psimpl (N.add _ 0) in H. exact H. Qed.
Goal forall n:N, n = n.
Proof. intros. pose (local := n + 0). psimpl in local. unfold local. reflexivity. Qed.
Goal forall n:N, n = n.
Proof. intros. pose (local := n + 0). psimpl (N.add _ 0) in local. unfold local. reflexivity. Qed.
Goal forall (s:store) n, update s R_EAX (n + 0) R_EAX = n.
Proof. intros. i386_psimpl. reflexivity. Qed.
Goal nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => true) true nil.
Proof. x86_step. exact I. Qed.
Goal nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => true) true nil.
Proof. x86_step_ltac1. exact I. Qed.

Require Import Picinae_amd64.
Goal nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => true) true nil.
Proof. x64_step. exact I. Qed.
Require Import Picinae_armv7.
Goal nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => true) true nil.
Proof. arm7_step. exact I. Qed.
Require Import Picinae_armv8.
Goal nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => true) true nil.
Proof. arm8_step. exact I. Qed.
Require Import Picinae_riscv.
Goal nextinv (fun _ _ => None) (fun _ => Some True) (fun _ => true) true nil.
Proof. r5_step. exact I. Qed.
