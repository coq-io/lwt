Require Import Extraction.Loop.
Require Import Extraction.Lwt.
Require Import Extraction.Sys.
Require Import Io.All.

Module Command.
  Definition t : Type :=
    {A : Type & Lwt.t A}.

  Definition answer (c : t) : Type :=
    projT1 c.
End Command.

Definition E : Effect.t :=
  Effect.New Command.t Command.answer.

(** Evaluate an expression using Lwt. *)
Fixpoint eval {A} (x : C.t E A) : Lwt.t A.
  destruct x as [A x | command | A B x f | A x1 x2 | A B x y].
  - exact (Lwt.ret x).
  - exact (projT2 command).
  - exact (Lwt.bind (eval _ x) (fun x => eval _ (f x))).
  - exact (Lwt.choose (eval _ x1) (eval _ x2)).
  - exact (Lwt.join (eval _ x) (eval _ y)).
Defined.

(** Launch the main function. *)
Definition launch (main : list LString.t -> C.t E unit) : unit :=
  let argv := List.map String.to_lstring Sys.argv in
  Extraction.Lwt.launch (eval (main argv)).

Module I.
  Fixpoint eval_aux {A} (steps : nat) (x : C.I.t E A) : Lwt.t A :=
    match steps with
    | O => Loop.error tt
    | S steps =>
      match x with
      | C.I.Ret _ v => Lwt.ret v
      | C.I.Call c => projT2 c
      | C.I.Let _ _ x f =>
        Lwt.bind (eval_aux steps x) (fun v_x => eval_aux steps (f v_x))
      | C.I.Choose _ x1 x2 => Lwt.choose (eval_aux steps x1) (eval_aux steps x2)
      | C.I.Join _ _ x y => Lwt.join (eval_aux steps x) (eval_aux steps y)
      end
    end.

  Definition eval {A} (x : C.I.t E A) : Lwt.t A :=
    eval_aux Loop.infinity x.

  Definition launch (main : list LString.t -> C.I.t E unit) : unit :=
    let argv := List.map String.to_lstring Sys.argv in
    Extraction.Lwt.launch (eval (main argv)).
End I.
