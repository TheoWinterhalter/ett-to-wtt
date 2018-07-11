Require Import TypingFlags.Loader.
Set Type In Type.

(* Quotations of terms for examples *)

From Coq Require Import Bool String List BinPos Compare_dec Omega.
From Equations Require Import Equations DepElimDec.
From Template Require Import Ast LiftSubst Typing Checker.
From Translation Require Import util Sorts SAst Quotes FinalTranslation.

Inductive vec A : nat -> Type :=
| vnil : vec A 0
| vcons : A -> forall n, vec A n -> vec A (S n).

Arguments vnil {_}.
Arguments vcons {_} _ _ _.

Existing Instance Sorts.type_in_type.
Open Scope string_scope.

Notation Ty := (sSort tt).

(* We have conversion obligations that were generated by the typing of vrev.
   We state them here in order to realise them in Coq.
 *)
(* Definition ty_obligation1 : sterm := *)
(*   sProd nAnon Ty *)
(*       (sProd nAnon (sAx "nat") *)
(*          (sProd nAnon (sAx "nat") *)
(*             (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 2)) (sAx "nat") Ty (sRel 1)) *)
(*                (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 3)) (sAx "nat") Ty (sRel 1)) *)
(*                   (sEq Ty *)
(*                      (sProd nAnon (sAx "nat") *)
(*                         (sProd (nNamed "acc") *)
(*                            (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 5)) (sAx "nat") Ty (sRel 0)) *)
(*                            (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 6)) (sAx "nat") Ty (sRel 1)))) *)
(*                      (sApp *)
(*                         (sApp *)
(*                            (sLambda (nNamed "n") (sAx "nat") *)
(*                               (sProd (nNamed "v") *)
(*                                  (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 5)) (sAx "nat") Ty (sRel 0)) Ty) *)
(*                               (sLambda (nNamed "v") *)
(*                                  (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 5)) (sAx "nat") Ty (sRel 0)) Ty *)
(*                                  (sProd (nNamed "m") (sAx "nat") *)
(*                                     (sProd nAnon *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 7)) (sAx "nat") Ty (sRel 0)) *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                           (sAx "nat") Ty *)
(*                                           (sApp *)
(*                                              (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) (sRel 3)) *)
(*                                              (sAx "nat") (sAx "nat") (sRel 1))))))) (sAx "nat") *)
(*                            (sProd (nNamed "v") *)
(*                               (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 5)) (sAx "nat") Ty (sRel 0)) Ty) *)
(*                            (sAx "O")) (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 4)) (sAx "nat") Ty (sAx "O")) *)
(*                         Ty *)
(*                         (sApp (sAx "vnil") Ty *)
(*                            (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 0)) (sAx "nat") Ty (sAx "O"))  *)
(*                            (sRel 4)))))))). *)

(* Definition ty_obligation2 : sterm := *)
(*   sProd nAnon Ty *)
(*       (sProd nAnon (sAx "nat") *)
(*          (sProd nAnon (sAx "nat") *)
(*             (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 2)) (sAx "nat") Ty (sRel 1)) *)
(*                (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 3)) (sAx "nat") Ty (sRel 1)) *)
(*                   (sEq Ty *)
(*                      (sProd (nNamed "f") *)
(*                         (sProd (nNamed "a") (sRel 4) *)
(*                            (sProd (nNamed "n") (sAx "nat") *)
(*                               (sProd (nNamed "v") *)
(*                                  (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 6)) (sAx "nat") Ty (sRel 0)) *)
(*                                  (sProd nAnon *)
(*                                     (sApp *)
(*                                        (sApp *)
(*                                           (sLambda (nNamed "n") (sAx "nat") *)
(*                                              (sProd (nNamed "v") *)
(*                                                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                                    (sAx "nat") Ty (sRel 0)) Ty) *)
(*                                              (sLambda (nNamed "v") *)
(*                                                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                                    (sAx "nat") Ty (sRel 0)) Ty *)
(*                                                 (sProd (nNamed "m") (sAx "nat") *)
(*                                                    (sProd nAnon *)
(*                                                       (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10)) *)
(*                                                          (sAx "nat") Ty (sRel 0)) *)
(*                                                       (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 11)) *)
(*                                                          (sAx "nat") Ty *)
(*                                                          (sApp *)
(*                                                             (sApp (sAx "add") (sAx "nat") *)
(*                                                                (sProd (nNamed "m") (sAx "nat") (sAx "nat"))  *)
(*                                                                (sRel 3)) (sAx "nat") (sAx "nat") (sRel 1)))))))  *)
(*                                           (sAx "nat") *)
(*                                           (sProd (nNamed "v") *)
(*                                              (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                                 (sAx "nat") Ty (sRel 0)) Ty) (sRel 1)) *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 7)) (sAx "nat") Ty (sRel 1)) *)
(*                                        Ty (sRel 0)) *)
(*                                     (sApp *)
(*                                        (sApp *)
(*                                           (sLambda (nNamed "n") (sAx "nat") *)
(*                                              (sProd (nNamed "v") *)
(*                                                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                                    (sAx "nat") Ty (sRel 0)) Ty) *)
(*                                              (sLambda (nNamed "v") *)
(*                                                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                                    (sAx "nat") Ty (sRel 0)) Ty *)
(*                                                 (sProd (nNamed "m") (sAx "nat") *)
(*                                                    (sProd nAnon *)
(*                                                       (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 11)) *)
(*                                                          (sAx "nat") Ty (sRel 0)) *)
(*                                                       (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 12)) *)
(*                                                          (sAx "nat") Ty *)
(*                                                          (sApp *)
(*                                                             (sApp (sAx "add") (sAx "nat") *)
(*                                                                (sProd (nNamed "m") (sAx "nat") (sAx "nat"))  *)
(*                                                                (sRel 3)) (sAx "nat") (sAx "nat") (sRel 1)))))))  *)
(*                                           (sAx "nat") *)
(*                                           (sProd (nNamed "v") *)
(*                                              (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                                 (sAx "nat") Ty (sRel 0)) Ty) (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 2))) *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                           (sAx "nat") Ty (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 2))) Ty *)
(*                                        (sApp *)
(*                                           (sApp *)
(*                                              (sApp *)
(*                                                 (sApp (sAx "vcons") Ty *)
(*                                                    (sProd nAnon (sRel 0) *)
(*                                                       (sProd (nNamed "n") (sAx "nat") *)
(*                                                          (sProd nAnon *)
(*                                                             (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 2)) *)
(*                                                                (sAx "nat") Ty (sRel 0)) *)
(*                                                             (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 3)) *)
(*                                                                (sAx "nat") Ty (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 1)))))) *)
(*                                                    (sRel 8)) (sRel 8) *)
(*                                                 (sProd (nNamed "n") (sAx "nat") *)
(*                                                    (sProd nAnon *)
(*                                                       (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10)) *)
(*                                                          (sAx "nat") Ty (sRel 0)) *)
(*                                                       (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 11)) *)
(*                                                          (sAx "nat") Ty (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 1))))) *)
(*                                                 (sRel 3)) (sAx "nat") *)
(*                                              (sProd nAnon *)
(*                                                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                                    (sAx "nat") Ty (sRel 0)) *)
(*                                                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10))  *)
(*                                                    (sAx "nat") Ty (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 1))))  *)
(*                                              (sRel 2)) *)
(*                                           (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                              (sAx "nat") Ty (sRel 2)) *)
(*                                           (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                              (sAx "nat") Ty (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 3)))  *)
(*                                           (sRel 1))))))) *)
(*                         (sProd (nNamed "n") (sAx "nat") *)
(*                            (sProd (nNamed "v") *)
(*                               (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 6)) (sAx "nat") Ty (sRel 0)) *)
(*                               (sApp *)
(*                                  (sApp *)
(*                                     (sLambda (nNamed "n") (sAx "nat") *)
(*                                        (sProd (nNamed "v") *)
(*                                           (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                              (sAx "nat") Ty (sRel 0)) Ty) *)
(*                                        (sLambda (nNamed "v") *)
(*                                           (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                              (sAx "nat") Ty (sRel 0)) Ty *)
(*                                           (sProd (nNamed "m") (sAx "nat") *)
(*                                              (sProd nAnon *)
(*                                                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10))  *)
(*                                                    (sAx "nat") Ty (sRel 0)) *)
(*                                                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 11))  *)
(*                                                    (sAx "nat") Ty *)
(*                                                    (sApp *)
(*                                                       (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                          (sRel 3)) (sAx "nat") (sAx "nat") (sRel 1)))))))  *)
(*                                     (sAx "nat") *)
(*                                     (sProd (nNamed "v") *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8)) (sAx "nat") Ty (sRel 0)) *)
(*                                        Ty) (sRel 1)) *)
(*                                  (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 7)) (sAx "nat") Ty (sRel 1)) Ty *)
(*                                  (sRel 0))))) *)
(*                      (sProd nAnon *)
(*                         (sProd (nNamed "a") (sRel 4) *)
(*                            (sProd (nNamed "n") (sAx "nat") *)
(*                               (sProd (nNamed "v") *)
(*                                  (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 6)) (sAx "nat") Ty (sRel 0)) *)
(*                                  (sProd nAnon *)
(*                                     (sProd (nNamed "m") (sAx "nat") *)
(*                                        (sProd nAnon *)
(*                                           (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                              (sAx "nat") Ty (sRel 0)) *)
(*                                           (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                              (sAx "nat") Ty *)
(*                                              (sApp *)
(*                                                 (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                    (sRel 3)) (sAx "nat") (sAx "nat") (sRel 1))))) *)
(*                                     (sProd (nNamed "m") (sAx "nat") *)
(*                                        (sProd nAnon *)
(*                                           (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                              (sAx "nat") Ty (sRel 0)) *)
(*                                           (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10))  *)
(*                                              (sAx "nat") Ty *)
(*                                              (sApp *)
(*                                                 (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                    (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 4)))  *)
(*                                                 (sAx "nat") (sAx "nat") (sRel 1))))))))) *)
(*                         (sProd (nNamed "n") (sAx "nat") *)
(*                            (sProd (nNamed "v") *)
(*                               (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 6)) (sAx "nat") Ty (sRel 0)) *)
(*                               (sProd (nNamed "m") (sAx "nat") *)
(*                                  (sProd nAnon *)
(*                                     (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8)) (sAx "nat") Ty (sRel 0)) *)
(*                                     (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                        (sAx "nat") Ty *)
(*                                        (sApp *)
(*                                           (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) (sRel 3)) *)
(*                                           (sAx "nat") (sAx "nat") (sRel 1))))))))))))). *)

(* Definition ty_obligation3 : sterm := *)
(*   sProd nAnon Ty *)
(*       (sProd nAnon (sAx "nat") *)
(*          (sProd nAnon (sAx "nat") *)
(*             (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 2)) (sAx "nat") Ty (sRel 1)) *)
(*                (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 3)) (sAx "nat") Ty (sRel 1)) *)
(*                   (sProd nAnon (sRel 4) *)
(*                      (sProd nAnon (sAx "nat") *)
(*                         (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 6)) (sAx "nat") Ty (sRel 0)) *)
(*                            (sProd nAnon *)
(*                               (sProd (nNamed "m") (sAx "nat") *)
(*                                  (sProd nAnon *)
(*                                     (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8)) (sAx "nat") Ty (sRel 0)) *)
(*                                     (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                        (sAx "nat") Ty *)
(*                                        (sApp *)
(*                                           (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) (sRel 3)) *)
(*                                           (sAx "nat") (sAx "nat") (sRel 1))))) *)
(*                               (sProd nAnon (sAx "nat") *)
(*                                  (sProd nAnon *)
(*                                     (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9)) (sAx "nat") Ty (sRel 0)) *)
(*                                     (sEq Ty *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10))  *)
(*                                           (sAx "nat") Ty *)
(*                                           (sApp *)
(*                                              (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                 (sRel 4)) (sAx "nat") (sAx "nat") *)
(*                                              (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 1)))) *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10))  *)
(*                                           (sAx "nat") Ty *)
(*                                           (sApp *)
(*                                              (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                 (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 4)))  *)
(*                                              (sAx "nat") (sAx "nat") (sRel 1)))))))))))))). *)

(* Definition ty_obligation4 : sterm := *)
(*   sProd nAnon Ty *)
(*       (sProd nAnon (sAx "nat") *)
(*          (sProd nAnon (sAx "nat") *)
(*             (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 2)) (sAx "nat") Ty (sRel 1)) *)
(*                (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 3)) (sAx "nat") Ty (sRel 1)) *)
(*                   (sEq Ty *)
(*                      (sProd nAnon (sRel 4) *)
(*                         (sProd (nNamed "n") (sAx "nat") *)
(*                            (sProd (nNamed "v") *)
(*                               (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 6)) (sAx "nat") Ty (sRel 0)) *)
(*                               (sProd (nNamed "rv") *)
(*                                  (sProd (nNamed "m") (sAx "nat") *)
(*                                     (sProd nAnon *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                           (sAx "nat") Ty (sRel 0)) *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                           (sAx "nat") Ty *)
(*                                           (sApp *)
(*                                              (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                 (sRel 3)) (sAx "nat") (sAx "nat") (sRel 1))))) *)
(*                                  (sProd (nNamed "m") (sAx "nat") *)
(*                                     (sProd (nNamed "acc") *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                           (sAx "nat") Ty (sRel 0)) *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10))  *)
(*                                           (sAx "nat") Ty *)
(*                                           (sApp *)
(*                                              (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                 (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 4)))  *)
(*                                              (sAx "nat") (sAx "nat") (sRel 1))))))))) *)
(*                      (sProd (nNamed "a") (sRel 4) *)
(*                         (sProd (nNamed "n") (sAx "nat") *)
(*                            (sProd (nNamed "v") *)
(*                               (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 6)) (sAx "nat") Ty (sRel 0)) *)
(*                               (sProd nAnon *)
(*                                  (sProd (nNamed "m") (sAx "nat") *)
(*                                     (sProd nAnon *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 8))  *)
(*                                           (sAx "nat") Ty (sRel 0)) *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                           (sAx "nat") Ty *)
(*                                           (sApp *)
(*                                              (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                 (sRel 3)) (sAx "nat") (sAx "nat") (sRel 1))))) *)
(*                                  (sProd (nNamed "m") (sAx "nat") *)
(*                                     (sProd nAnon *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 9))  *)
(*                                           (sAx "nat") Ty (sRel 0)) *)
(*                                        (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 10))  *)
(*                                           (sAx "nat") Ty *)
(*                                           (sApp *)
(*                                              (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) *)
(*                                                 (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 4)))  *)
(*                                              (sAx "nat") (sAx "nat") (sRel 1)))))))))))))). *)

Definition ty_vcons_act_obligation :=
  sProd nAnon Ty
     (sProd nAnon (sAx "nat")
        (sProd nAnon Ty
           (sProd nAnon
              (sProd nAnon
                 (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 2)) (sAx "nat") Ty
                    (sApp (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) (sRel 1)) 
                       (sAx "nat") (sAx "nat") (sApp (sAx "S") (sAx "nat") (sAx "nat") (sAx "O")))) 
                 (sRel 1))
              (sProd nAnon (sRel 3)
                 (sProd nAnon (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 4)) (sAx "nat") Ty (sRel 3))
                    (sEq Ty
                       (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 5)) (sAx "nat") Ty
                          (sApp (sAx "S") (sAx "nat") (sAx "nat") (sRel 4)))
                       (sApp (sApp (sAx "vec") Ty (sProd nAnon (sAx "nat") Ty) (sRel 5)) (sAx "nat") Ty
                          (sApp (sApp (sAx "add") (sAx "nat") (sProd (nNamed "m") (sAx "nat") (sAx "nat")) (sRel 4)) 
                             (sAx "nat") (sAx "nat") (sApp (sAx "S") (sAx "nat") (sAx "nat") (sAx "O")))))))))).

(* The global context of obligations *)
(* We define a term that mentions everything that the global context should
   have. *)
Definition glob_term :=
  let _ := @pp_sigT in
  let _ := @epair in
  let _ := @pi1 in
  let _ := @pi2 in
  let _ := @eq in
  let _ := @transport in
  let _ := @K in
  let _ := @funext in
  let _ := @heq in
  let _ := @heq_to_eq in
  let _ := @heq_refl in
  let _ := @heq_sym in
  let _ := @heq_trans in
  let _ := @heq_transport in
  let _ := @Pack in
  let _ := @ProjT1 in
  let _ := @ProjT2 in
  let _ := @ProjTe in
  let _ := @cong_prod in
  let _ := @cong_app in
  let _ := @cong_lambda in
  let _ := @cong_sum in
  let _ := @cong_pair in
  let _ := @cong_pi1 in
  let _ := @cong_pi2 in
  let _ := @cong_eq in
  let _ := @cong_refl in
  let _ := @eq_to_heq in
  let _ := @heq_type_eq in
  (* Candidate *)
  let _ := @candidate in
  (* For examples *)
  let _ := nat in
  let _ := vec in
  let _ := vec_rect in
  let _ := Nat.add in
  Type.

Quote Recursively Definition glob_prog := @glob_term.
Definition Σ : global_context :=
  (* Eval lazy in *)
  (* reconstruct_global_context (Datatypes.fst glob_prog). *)
  pair (Datatypes.fst glob_prog) init_graph.

Arguments Σ : simpl never.


(* Putting obligations in Coq *)

Notation "s --> t" := (acons s t) (at level 20).
Notation "[< a ; b ; .. ; c >]" :=
  (a (b (.. (c empty) ..))).
Notation "[< a >]" := (a empty).
Notation "[< >]" := (empty).

(* Notation "[< a --> x ; b --> y ; .. ; c --> z >]" := *)
(*   (acons a x (acons b y .. (acons c z empty) ..)). *)

Quote Definition qnat := nat.
Quote Definition qvec := vec.
Quote Definition qadd := Nat.add.
Quote Definition qO := O.
Quote Definition qS := S.
Quote Definition qvnil := @vnil.
Quote Definition qvcons := @vcons.

Definition axoc :=
  [< "nat" --> qnat ;
     "vec" --> qvec ;
     "add" --> qadd ;
     "O" --> qO ;
     "S" --> qS ;
     "vnil" --> qvnil ;
     "vcons" --> qvcons
  >].

(* Definition tc_obligation1 : tsl_result term := *)
(*   Eval lazy in *)
(*   tsl_rec (2 ^ 18) Σ [] ty_obligation1 axoc. *)

(* Make Definition coq_obligation1 := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_obligation1 with *)
(*               | FinalTranslation.Success _ t => t *)
(*               | _ => tRel 0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)

(* Definition tc_obligation2 : tsl_result term := *)
(*   Eval lazy in *)
(*   tsl_rec (2 ^ 18) Σ [] ty_obligation2 axoc. *)

(* Make Definition coq_obligation2 := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_obligation2 with *)
(*               | FinalTranslation.Success _ t => t *)
(*               | _ => tRel 0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)

(* Definition tc_obligation3 : tsl_result term := *)
(*   Eval lazy in *)
(*   tsl_rec (2 ^ 18) Σ [] ty_obligation3 axoc. *)

(* Make Definition coq_obligation3 := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_obligation3 with *)
(*               | FinalTranslation.Success _ t => t *)
(*               | _ => tRel 0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)

(* Definition tc_obligation4 : tsl_result term := *)
(*   Eval lazy in *)
(*   tsl_rec (2 ^ 18) Σ [] ty_obligation4 axoc. *)

(* Make Definition coq_obligation4 := *)
(*   ltac:( *)
(*     let t := eval lazy in *)
(*              (match tc_obligation4 with *)
(*               | FinalTranslation.Success _ t => t *)
(*               | _ => tRel 0 *)
(*               end) *)
(*       in exact t *)
(*   ). *)

Definition tc_vcons_act_obligation : tsl_result term :=
  Eval lazy in
  tsl_rec (2 ^ 18) Σ [] ty_vcons_act_obligation axoc.

Make Definition coq_vcons_act_obligation :=
  ltac:(
    let t := eval lazy in
             (match tc_vcons_act_obligation with
              | FinalTranslation.Success _ t => t
              | _ => tRel 0
              end)
      in exact t
  ).

(* Lemma vrev_obligation1 : coq_obligation1. *)
(* Proof. *)
(*   unfold coq_obligation1. *)
(*   intros A n m v acc. reflexivity. *)
(* Defined. *)

(* Lemma vrev_obligation2 : coq_obligation2. *)
(* Proof. *)
(*   unfold coq_obligation2. *)
(*   intros A n m v acc. reflexivity. *)
(* Defined. *)

(* Lemma vrev_obligation3 : coq_obligation3. *)
(* Proof. *)
(*   unfold coq_obligation3. *)
(*   intros A n m v acc a n' v' h m' acc'. *)
(*   f_equal. myomega. *)
(* Defined. *)

(* Lemma vrev_obligation4 : coq_obligation4. *)
(* Proof. *)
(*   unfold coq_obligation4. *)
(*   intros A n m v acc. *)
(*   reflexivity. *)
(* Defined. *)

Lemma vcons_act_obligation : coq_vcons_act_obligation.
Proof.
  unfold coq_vcons_act_obligation.
  intros A n X f a v. f_equal. myomega.
Defined.
