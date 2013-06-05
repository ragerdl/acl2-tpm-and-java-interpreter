; ACL2 Interpreter for Java
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

(in-package "JI")

(include-book "~/r/parser/earley-acl2/earley-parser")

(include-book "tools/bstar" :dir :system)

; This file contains definitions that we use to generate the parse-tree-p
; predicate.

(program)

; Even though we are writing in program mode, we will still define function
; guards where we feel like it.  This way we get runtime checking of some
; properties.

(set-guard-checking :all)

(defun safe-nth (n lst)
  (declare (xargs :guard (and (true-listp lst) (natp n))
                  :mode :logic))
  (cond ((< n (len lst)) 
         (nth n lst)) 
        (t nil)))

(defun make-predicate-for-lexical-token (entry)
  (declare (xargs :guard (and (consp entry)
                              (stringp (car entry))
                              ;(consp (cdr entry))
                              (acl2::terminal-list-p (cdr entry)))))
  
  (b* ((terminal (cadr entry))
;       ((unless (atom (cddr entry)))
;        (raise "This function is only written to account for terminal-list-p's ~
;                of length 1"))
       (class (acl2::terminal->class terminal))
       
       (predicate-name
        (intern$ (concatenate 'string 
                              class
                              "-TOKEN-P")
                 "JI")))
    `(defn ,predicate-name (x)
       (and (consp x)
            (equal (car x) ,class)))))

(defun make-predicates-for-lexical-tokens (dict)
  (declare (xargs :guard (ACL2::dictionary-p dict)))
  (cond ((atom dict)
         nil)
        (t (cons (make-predicate-for-lexical-token (car dict))
                 (make-predicates-for-lexical-tokens (cdr dict))))))

(defun str-upper-case-p1 (chars)
  (declare (xargs :guard (character-listp chars)))
  (cond ((atom chars)
         t)
        (t (and (str::up-alpha-p (car chars))
                (str-upper-case-p1 (cdr chars))))))

(defun str-upper-case-p (str)
  (declare (xargs :guard (stringp str)))
  (str-upper-case-p1 (coerce str 'list)))

(defun string-represents-lexical-token-p (str)
  (declare (xargs :guard (stringp str)))
  (str-upper-case-p str))


(defun make-predicates-for-target-list1 (target-list n)
  (declare (xargs :guard (and (acl2::string-list-p target-list)
                              (integerp n))))
  (cond ((atom target-list)
         nil)
        (t 
         (b* ((description (car target-list))
              (predicate-name 
               (intern$
                (concatenate 'string
                             (str::upcase-string description)

                             (cond ((string-represents-lexical-token-p
                                     description)
                                    "-TOKEN-P")
                                   (t "-NONTERM-P")))
                "JI")))
                       


              (cons `(,predicate-name (safe-nth ,n x))
                    (make-predicates-for-target-list1 (cdr target-list) (1+ n)))))))

(defun make-predicates-for-target-list (target-list)
  (declare (xargs :guard (acl2::string-list-p target-list)))
  (cons 'and (make-predicates-for-target-list1 target-list 0)))


(defun make-predicate-for-target-list-list (target-list-list)
  (declare (xargs :guard (acl2::string-list-list-p target-list-list)))
  (cond ((atom target-list-list)
         nil)
        (t (cons (make-predicates-for-target-list (car target-list-list))
                 (make-predicate-for-target-list-list (cdr target-list-list))))))

(defun make-predicate-for-nonterminal (rule)
  (declare (xargs :guard (and (consp rule)
                              (stringp (car rule))
                              (acl2::string-list-list-p (cdr rule)))))
  (b* ((predicate-name 
        (intern$
         (concatenate 'string
                      (str::upcase-string (car rule))
                      "-NONTERM-P")
         "JI"))) 
    
    `(defun ,predicate-name (x)
       (or ,@(make-predicate-for-target-list-list (cdr rule))))))
  







