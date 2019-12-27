(*** Abstract transaction interface *)
Require Import List.
Require Import Coq.Program.Basics.
Import ListNotations.
Import Decidable.
Require Import Sumbool.
Require Import FoldIn.
Require Import Storage.

Set Implicit Arguments.

Module Basic (S : Storage.Interface).
