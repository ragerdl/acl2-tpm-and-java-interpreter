; ACL2 TPM  Model
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

(defmacro defposition-if (function-name predicate-name
                                         &key guard)
  (let* ((declaration (if guard
                          `((declare (xargs :guard ,guard)))
                        `((declare (xargs :guard t)))))
         (ac-declaration (if guard 
                             `((declare (xargs :guard 
                                               (and ,guard (integerp acc)))))
                           `((declare (xargs :guard (integerp acc))))))
         (ac-function-name (intern-in-package-of-symbol
                            (concatenate 'string 
                                         (symbol-name function-name)
                                         "-AC")
                            function-name))

         ;; (type-of-function-theorem-name
         ;;  (intern-in-package-of-symbol
         ;;   (concatenate 'string 
         ;;                "TYPE-OF-"
         ;;                (symbol-name function-name))
         ;;   function-name))
          
         (function-ac-of-append-theorem-name
          (intern-in-package-of-symbol
           (concatenate 'string 
                        (symbol-name ac-function-name)
                        "-OF-APPEND")
           function-name))
         
         (nth-of-ac-function-theorem-name
          (intern-in-package-of-symbol
           (concatenate 'string 
                        "NTH-OF-"
                        (symbol-name ac-function-name))
           function-name))
         
         (nth-of-function-theorem-name
          (intern-in-package-of-symbol
           (concatenate 'string 
                        "NTH-OF-"
                        (symbol-name function-name))
           function-name))

         ;; (limit-of-ac-function-theorem-name
         ;;  (intern-in-package-of-symbol
         ;;   (concatenate 'string 
         ;;                "LIMIT-OF-"
         ;;                (symbol-name ac-function-name))
         ;;   function-name))

         ;; (limit-of-function-theorem-name
         ;;  (intern-in-package-of-symbol
         ;;   (concatenate 'string 
         ;;                "LIMIT-OF-"
         ;;                (symbol-name function-name))
         ;;   function-name))
         )
    `(progn

       ; Define the accumulator
       (defund ,ac-function-name (lst acc)
         ,@ac-declaration
         (cond ((atom lst) nil)
               ((,predicate-name (car lst)) acc)
               (t (,ac-function-name (cdr lst) (1+ acc)))))

       ; Define the main function
       (defund ,function-name (lst)
         ,@declaration
         (,ac-function-name lst 0))

       (local (include-book "centaur/vl/util/arithmetic" :dir :system))

       ;; (defthm ,type-of-function-theorem-name
       ;;   (or (not (,function-name lst))
       ;;       (natp (,function-name lst)))
       ;;   :rule-classes :type-prescription
       ;;   :hints (("Goal" :in-theory (enable ,function-name))))

       (encapsulate ()
         (local (defun defposition-if-induct (x acc)
                  (if (atom x)
                      acc
                    (defposition-if-induct (cdr x) (+ 1 acc)))))

         (defthm ,function-ac-of-append-theorem-name
           (implies (force (acl2-numberp acc))
                    (equal (,ac-function-name (append x y) acc)
                           (if (,ac-function-name x acc)
                               (,ac-function-name x acc)
                             (,ac-function-name y (+ (len x) acc)))))
           :hints(("Goal" :induct (defposition-if-induct x acc)
                   :in-theory (enable ,ac-function-name)))))
       
       (defthm ,nth-of-ac-function-theorem-name
         (implies (and (,ac-function-name lst acc)
                       (natp acc))
                  (,predicate-name (nth (- (,ac-function-name lst acc) acc)
                             lst)))
         :hints(("Goal"
                 :in-theory (enable ,ac-function-name)
                 :do-not '(generalize fertilize)
                 :induct (,ac-function-name lst acc))))
       
       (defthm ,nth-of-function-theorem-name
         (implies (,function-name lst)
                  (,predicate-name (nth (,function-name lst)
                             lst)))
         :hints(("Goal"
                 :use ((:instance ,nth-of-ac-function-theorem-name
                                  (acc 0)))
                 :in-theory (enable ,function-name))))
                  

       )))

(local (include-book "cutil/deflist" :dir :system))

(local (encapsulate ()

  (defn three-conses (x)
    (and (consp x)
         (consp (cdr x))
         (consp (cddr x))))

  (defun airplane-p (x)
    (declare (xargs :guard (three-conses x)))
    (equal (caddr x) 787))

  (cutil::deflist three-conses-list-p (x)
    (three-conses x))

  (in-theory (disable airplane-p))

  (defposition-if find-the-airplane
                   airplane-p
                   :guard (three-conses-list-p lst))))

(local (include-book "misc/assert" :dir :system))

(local 
 (assert! 
  (equal (find-the-airplane '((1 2 3) (4 5 6) (7 8 787) (10 11 12)))
         2)))
 
 
#|
; I'm leaving the following here for historical reasons.  I'll delete it at
; some point.

(defposition-if position-car (equal (caar lst) x))

(position-car 3 '( ( 1 . 2) ( 3 . 4) ( 5 . 6)))


(defposition-if position-invalid-session
 (equal (tpm-session-data->session-type (car lst))
        :tpmx-st-invalid))

(position-invalid-session ...)




(defun position-invalid-session (x lst)
  (declare (xargs :guard (tpm-session-data-list-p lst)))
  (cond ((atom lst) -1)
	((equal (tpm-session-data->session-type (car lst))
		x)
	 0)
	(t (let ((recursive (position-invalid-session x (cdr lst))))
             (if (equal recursive -1)
                 -1
               (+ 1 (position-invalid-session x (cdr lst))))))))


(defun position-invalid-session (x lst acc)
  (declare (xargs :guard (and (tpm-session-data-list-p lst)
                              (integerp acc))))
  (cond ((atom lst) -1)
	((equal (tpm-session-data->session-type (car lst))
		x)
	 acc)
	(t (position-invalid-session x (cdr lst) (1+ acc)))))

(defun my-test (x)
  (equal (tpm-session-data->session-type x) 
         :tpmx-st-invalid))

(include-book "cutil/deflist" :dir :system)

(defn three-conses (x)
  (and (consp x)
       (consp (cdr x))
       (consp (cddr x))))

(defun test (x)
  (declare (xargs :guard (three-conses x)))
  (equal (caddr x) 787))

(cutil::deflist three-conses-list-p (x)
  (three-conses x))

(in-theory (disable test))

(defun find-it-ac (lst acc)
  (declare (xargs :guard (and (three-conses-list-p lst)
                              (integerp acc))))
  (cond ((atom lst) nil)
        ((test (car lst)) acc)
        (t (find-it-ac (cdr lst) (1+ acc)))))

(defun find-it (lst)
  (declare (xargs :guard (three-conses-list-p lst)))
  (find-it-ac lst 0))

(local (include-book "centaur/vl/util/arithmetic" :dir :system))

;; (defthm natp-of-find-it-ac-when-natp
;;   (implies (natp acc)
;;            (or (not (find-it-ac lst acc))
;;                (natp (find-it-ac lst acc))))
;;   :rule-classes :type-prescription)

(defthm type-of-find-it
  (or (not (find-it lst))
      (natp (find-it lst)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable find-it))))

(encapsulate
  ()
  (local (defun my-induct (x acc)
           (if (atom x)
               acc
             (my-induct (cdr x) (+ 1 acc)))))

  (defthm find-it-ac-of-append
    (implies (force (acl2-numberp acc))
             (equal (find-it-ac (append x y) acc)
                    (if (find-it-ac x acc)
                        (find-it-ac x acc)
                      (find-it-ac y (+ (len x) acc)))))
    :hints(("Goal" :induct (my-induct x acc)))))

;; (defthm find-it-ac-upper-bound-weak
;;   (implies (natp acc)
;;            (<= (find-it-ac lst acc)
;;                (+ (len lst) acc)))
;;   :rule-classes ((:rewrite) (:linear)))

;; (defthm find-it-ac-upper-bound-strong
;;   (implies (and (case-split (find-it-ac lst acc))
;;                 (natp acc))
;;            (< (find-it-ac lst acc)
;;               (+ (len lst) acc)))
;;   :rule-classes ((:rewrite) (:linear)))

;; (defthm find-it-ac-monotonic
;;   (implies (and (find-it-ac lst acc)
;;                 (natp acc))
;;            (<= acc (find-it-ac lst acc)))
;;   :rule-classes ((:rewrite) (:linear))
;;   :hints(("Goal" :in-theory (enable find-it-ac))))

(defthm nth-of-find-it-ac
  (implies (and (find-it-ac lst acc)
                (natp acc))
           (test (nth (- (find-it-ac lst acc) acc)
                       lst)))
  :hints(("Goal"
          :in-theory (enable find-it-ac)
          :do-not '(generalize fertilize)
          :induct (find-it-ac lst acc))))

(defthm nth-of-find-it
  (implies (find-it lst)
           (test (nth (find-it lst)
                      lst)))
  :hints(("Goal"
          :use ((:instance nth-of-find-it-ac
                           (acc 0))))))


;; (defthm acl2-numberp-of-find-it
;;   (equal (acl2-numberp (find-it x))
;;          (if (find-it x)
;;              t
;;            nil)))

;; (defthm integerp-of-find-it
;;   (equal (integerp (find-it x))
;;          (if (find-it x)
;;              t
;;            nil)))

;; (defthm natp-of-find-it-ac
;;   (implies (natp acc)
;;            (equal (natp (find-it-ac lst acc))
;;                   (if (find-it-ac lst acc)
;;                       t
;;                     nil))))


|#



