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

(include-book "portcullis")

(include-book "cutil/defalist" :dir :system)
(include-book "cutil/deflist" :dir :system)
(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/defenum" :dir :system)
(include-book "cutil/define" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "util")
(include-book "parse-tree-examples")
(include-book "parse-tree")


(defxdoc JI
  :short "Java Interpreter for ACL2"
  :long "Beginnings of an interpreter for MSEJava.

  The interpreter will consist of classes, which define member variables and
  methods, and objects, which are instantiations of classes with associated
  variable values.

  Note that the above idea of an object doesn't address the issue of aliasing.
  At some point we will need to model a heap.  In this case, the heap may have
  a list of addresses (keys) and values, where the values are not just numbers
  but annotated also annotated with information that describes the type/class
  of the address.")

(defenum scope-p
  (public protected package private)
  :short "Scope for a method, variable, etc."
  :parents (JI))

(defaggregate JI::method
  ((name stringp "Name of the method.  Since every method has a class, we plan
                  to embed the methods inside the java-class structure and not
                  save the name as its fully qualified name.  We might need to
                  do something like that later for reflection.")
   (scope scope-p "Scope of the method"))
  :parents (JI))

(deflist method-list-p (x)
; perhaps this should be an [fast] alist, where the name of the method is the
; key, but going with a basic list for now.
  (method-p x)
  :parents (JI))  

(defaggregate member 
  :short "A member variable of a class"
  :parents (JI)
  :tag :member
  ((name symbolp "Name of the member variable")
   (scope scope-p "Scope of the member variable")))

(deflist member-list-p (x)

  (member-p x)
    :short "List of member variables for a class"
  :parents (JI))


(defaggregate classs
  ((name stringp "Name of the class")
   (scope scope-p "Scope of the class")
   (members member-list-p "Members of the class")
   (methods method-list-p "Methods of the class"))
  :parents (JI)
  :tag :class)

(define variable-p (x)
  (symbolp x)
  :parents (ji))

(define constant-p (x)
  (or (acl2-numberp x) ; should be uint32-p, int32-p, short-p, boolean-p, etc
      (stringp x))
  :parents (ji))

(defenum operator-p
  (+ - / *))

(local 
 (defthm expression-admission-lemma
   (implies (and (alistp x)
                 (consp x))
            (< (acl2-count (cdr (assoc-equal foo x)))
               (acl2-count x)))))

(defaggregate expression
  :long "This should probably be a union type"
  ((value constant-p) 
   (lhs (implies lhs (expression-p lhs))
        "Left-hand side of the expression")
   (operator operator-p)
   (rhs (implies rhs (expression-p rhs))
        "Right-hand side of the expression"))
  :parents (ji)
  ;:tag :expression
  )

(defaggregate assignment
  ((variable variable-p "Variable to receive value")
   (value expression-p))
  :parents (JI)
  :tag :assignment)

(defaggregate j-return
  ((return t))
  :tag :j-return)

   
(defaggregate var-table-entry
  :long "Identifier and context for an entry in the var-table"
  ((type "Either one of the primitive types or a fully qualified class name")
   (identifier "local variable name")
   (context var-table-entry-p "variable containing the variable.  Empty if part
                               of the top-level scope"))
  :tag :var-table-entry)

;; (defaggregate var-table-value
;;   :long "Value for a variable"
;;   ((val "Value")))

(define var-table-value-p (x)
  :verify-guards t
  (declare (ignore x))
  t)

(defalist var-table-p (x)
;  :long "Variable list and associated values"
  :key (var-table-entry-p x)
  :val (var-table-value-p x))


(defaggregate j-id
  :parents (JI)
  ((names string-listp "identifier names"))
  :tag :j-id)

;; (define create-identifier<ptree>
;;   ((tree true-listp "parse tree"))
;;   (b* (((unless (and (equal (safe-car tree) "Identifier")
;;                      (equal (safe-car (safe-car (safe-cdr tree)))
;;                             "IDENTIFIER")))
;;         (raise "Strucutre of tree incorrect: ~x0" tree)))
;;     (make-j-identifier :name (or (safe-car (safe-cdr (safe-car 
;;                                                       (safe-cdr tree))))
;;                                  "bogus-identifier"))))

(defaggregate j-infix-call
  :parents (JI)
  ((op stringp "Operation to apply")
   (lhs t "Lefthand side of the operation")
   (rhs t "Righthand side of the operation.  Could be another j-infix-call."))
  :tag :j-infix-call)

;(ld "parse-tree.lisp")

(include-book "tools/match-tree" :dir :system)

(define identifier-tree-p
  ((tree t "Tree to check"))
  :returns (ans booleanp)
  (b* (((when-match tree
                    ("IdentifierRag" 
                     ("Identifier" ("IDENTIFIER" (:? id)))))
        (stringp id))
       ((when-match tree 
                    ("IdentifierRag"
                     ("Identifier" ("IDENTIFIER" (:? id)))
                     ("PERIOD" ".")
                     (:? nextrag)))
        (and (stringp id)
             (identifier-tree-p nextrag))))
    nil))

;; (define identifier-tree-p
;;   ((tree t "Tree to check"))
;;   :returns (ans booleanp)
;;   (case-match tree
;;     (("IdentifierRag" 
;;       ("Identifier" ("IDENTIFIER" id)))
;;      (stringp id))
;;     (("IdentifierRag"
;;       ("Identifier" ("IDENTIFIER" id))
;;       ("PERIOD" ".")
;;       nextrag)
;;      (and (stringp id)
;;           (identifier-tree-p nextrag)))
;;     (& nil)))




(local 
 (acl2::def-match-tree-rewrites
   ("IdentifierRag" 
    ("Identifier" ("IDENTIFIER" (:? id))))
   :prefix e1->))

(local 
 (acl2::def-match-tree-rewrites
   ("IdentifierRag"
    ("Identifier" ("IDENTIFIER" (:? id)))
    ("PERIOD" ".")
    (:? nextrag))
   :prefix e2->))


(include-book "misc/untranslate-patterns" :dir :system)

(acl2::add-untranslate-pattern
 (MV-NTH 0 (ACL2::MATCH-TREE ?x)) (match-tree-ok ?x))

(define gather-identifiers
  ((tree identifier-tree-p "parse tree"))
  :returns (ans string-listp "List of strings that represent the identifier's scope
                              and the identifier itself" :hyp :fguard
                              :hints (("Goal" :in-theory (enable identifier-tree-p))))
  (b* (((when-match tree
                    ("IdentifierRag"
                     ("Identifier" ("IDENTIFIER" (:? id)))))
        (list id))
       ((when-match tree
                    ("IdentifierRag"
                     ("Identifier" ("IDENTIFIER" (:? id)))
                     ("PERIOD" ".")
                     (:? nextrag)))
        (cons id
              (gather-identifiers nextrag))))
    (er hard? 'gather-identifiers
        "Gather-identifiers given input that it doesn't know how to parse: ~x0"
        tree))
  :guard-hints (("Goal" :in-theory (enable identifier-tree-p))))

(define gather-identifiers-safe
  ((tree parse-tree-p "parse tree"))
  :returns (ans string-listp "List of strings that represent the identifier's scope
                              and the identifier itself.  <tt>Nil</tt> if @('tree')
                              is not an @('identifier-tree-p').")
  (if (identifier-tree-p tree)
      (gather-identifiers tree)
    (prog2$ (er hard? 'gather-identifiers-safe
                "Provided tree wasn't an identifier-tree-p.  Provided tree is: ~x0" tree)
;; We might want eventually to return a dummy identifier list like
;; ("GatherIdentifiersError").
            nil)))

(define statement-p 
  (x)
  (or (j-return-p x)))

(deflist statement-list-p (x)
  (statement-p x)
  :parents (JI))



;(skip-proofs
;; (define gather-identifiers
;;   ((tree identifier-tree-p "parse tree"))
;;   :returns (ans string-listp "List of strings that represent the identifier's scope
;;                               and the identifier itself" :hyp :fguard
;;                               :hints (("Goal" :in-theory (enable parse-tree-p))))
;;   (case-match tree
;;     (("IdentifierRag"
;;       ("Identifier" ("IDENTIFIER" id-name)))
;;      (list id-name))
;;     (("IdentifierRag"
;;       ("Identifier" ("IDENTIFIER" id))
;;       ("PERIOD" ".")
;;       nextrag)
;;      (cons id
;;            (gather-identifiers nextrag)))
;;     (& (er hard? 'gather-identifiers
;;            "Gather-identifiers given input that it doesn't know how to parse: ~
;;             ~x0"
;;            tree)))
;;   :guard-hints (("Goal" :in-theory (enable identifier-tree-p))));)


(define create-expression
  ((tree parse-tree-p "parse tree"))

; At some point we'd like to define a j-expression predicate and prove that
; create-expression returns a j-expression.  But, we will wait to do that until
; we have a working example.  This means that while our j-expression
; interpreter might have a guard that its input is a j-expression, we won't be
; able to prove anything about running the result of create-expression.

  :guard-debug t
  (case-match tree
    (("IdentifierRag" & & &)
     (make-j-id :names (gather-identifiers-safe tree)))
    (("IdentifierRag" &)
     (make-j-id :names (gather-identifiers-safe tree)))
    ;; (("Identifier" ("IDENTIFIER" id-name))
    ;;  (make-j-identifier :name id-name))
    (("Expression2" expr3) ; nothing meaningful to do but recur
     (create-expression expr3))
    (("Expression2" ("Expression3" expr3L) expr2rest) 
     (case-match expr2rest
       (("Expression2Rest"
         ("InfixOpExpression3Rag"
          ("InfixOp" (infixop-label infixop))
          ("Expression3" expr3R)))
        (declare (ignore infixop-label))
        (make-j-infix-call :op infixop
                           :lhs (create-expression expr3L)
                           :rhs (create-expression `("Expression3" ,expr3R))))
       (& (er hard? 'create-identifier "problem creating expression within expr2rest"))
       ))
    (("Expression3" rest)
     (create-expression rest))
    (("Expression1" rest)
     (create-expression rest))
    (("Expression" rest)
     (create-expression rest))
    
    (("Statement" ("RETURN" "return") expr ("SEMICOLON" ";"))
     (make-j-return :return (create-expression expr)))

    ;; (("BlockStatement" ("Statement" &))
    ;;  (create-expression (cdr tree)))
    ;; (("BlockStatement" ("Statement" & &))
    ;;  (create-expression (cdr tree)))
    ;;(("BlockStatement" ("Statement" & & &)) ; this is the one I'm working on admitting
    ;; (create-expression (cdr tree)))
    ;; (("BlockStatement" ("Statement" & & & &))
    ;;  (create-expression (cdr tree)))
    ;; (("BlockStatement" ("Statement" & & & & &))
    ;;  (create-expression (cdr tree)))

    (("BlockStatements" ("Blockstatement" &))
     (create-expression (cdr tree)))

    (("BlockStatements" ("Blockstatement" &) more-block-statements)
     (cons (create-expression (cdr tree))
           (create-expression more-block-statements)))
    

    (("Primary" rest)
     (create-expression rest))
    

    (& (er hard? 'create-expression "problem creating expression")))
  :guard-hints (("Goal" :in-theory (enable parse-tree-p))))

(assert! 
 (equal (create-expression *addition-tree*)
        '(:J-INFIX-CALL (OP . "+")
                        (LHS :J-ID (NAMES "x"))
                        (RHS :J-ID (NAMES "y")))))

