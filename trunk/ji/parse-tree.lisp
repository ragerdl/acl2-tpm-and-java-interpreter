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

(include-book "cutil/define" :dir :system)
(include-book "misc/assert" :dir :system)

; Some day I'll want to automatically generate parse-tree-p from the MSEJ
; grammar.  We'll want some heuristics to guide the generation of this
; predicate.  Take for example the grammar rules for Expression2:

;;; <Expression2> ::= 
;;;    <Expression3> 
;;;  | <Expression3> <Expression2Rest>

; This should result in the following case-match forms being added to the
; predicate:

;;; (("Expression2" Expression3)
;;;  (parse-tree-p Expression3))
;;; (("Expression2" Expression3 Expression2Rest)
;;;  (and (parse-tree-p Expression3)
;;;       (parse-tree-p Expression2Rest)))

; We can do something so simple for the above, because there are no "parts of
; speech" used ("part of speech" is a term derived from the Earley Parser
; literature, but concretely, it means a terminal or something that has a
; definition in the lexicon.  Let us now consider Expression2Rest, which does
; employ a part of speech:

;;; <Expression2Rest> ::= 
;;;     <InfixOpExpression3Rag> 
;;;   | <INSTANCEOF> <Type>

; This should result in the following case-match forms being added to the
; predicate:

;;; (("Expression2Rest" InfixOpExpression3Rag)
;;;  (parse-tree-p InfixOpExpression3Rag))
;;; (("Expression2Rest" ("INSTANCEOF" "instanceof") Type)
;;;  (parse-tree-p Type))

; It is debateable whether we should include ("INSTANCEOF" "instanceof")
; explicitly in the case-match.  Alternatively, we could do what we do for
; identifiers, which is:

;;; (("Expression2Rest" ("INSTANCEOF" instanceof) Type)
;;;  (and (stringp instanceof)
;;;       (parse-tree-p Type)))

; Such an approach is required for terminals that use regular expressions,
; because we don't need to keep the regular expression syntax around any more.
; In fact, just knowing that any terminal is a stringp is good for this round
; of translation -- we don't need regular expression anymore, because we will
; have already ascertained whether a terminal is an identifier, plus sign, etc.
; For most of the terminals, we won't even need to look at the string itself
; (exceptions include identifiers and literals).

(define infix-op-p 
  ((tree t "Infix op tree to check"))
  :enabled t
  (case-match tree
    (("PLUS" "+") ; would be derived from lexicon
     t)
    (("MINUS" "-") ; would also be derived from lexicon
     t)
    (& nil)))
  
  

(define parse-tree-p
  ((tree t "Tree to check"))
  :returns (ans booleanp)
  (case-match tree
    (("IdentifierRag" 
      ("Identifier" ("IDENTIFIER" id)))
     (stringp id))
    (("IdentifierRag"
      ("Identifier" ("IDENTIFIER" id))
      ("PERIOD" ".")
      ragitself)
     (and (stringp id)
          (parse-tree-p ragitself)))
    (("Primary" targ)
     (parse-tree-p targ))
    (("Expression3" primary)
     (parse-tree-p primary))
    (("Expression2" expr3)
     (parse-tree-p expr3))
    (("Expression2" expr3 expr2rest)
     (and (parse-tree-p expr3)
          (parse-tree-p expr2rest)))
    (("Expression2Rest" InfixOpExpression3Rag)
     (parse-tree-p InfixOpExpression3Rag))
    (("Expression2Rest" ("INSTANCEOF" "instanceof") Type)
     (parse-tree-p Type))
    (("Expression1" rest)
     (parse-tree-p rest))
    (("Expression" rest)
     (parse-tree-p rest))
    (("InfixOpExpression3Rag" InfixOp Expression3)
     (and (parse-tree-p InfixOp)
          (parse-tree-p Expression3)))
    
    (("InfixOpExpression3Rag" InfixOp Expression3 InfixOpExpression3Rag)
     (and (parse-tree-p InfixOp)
          (parse-tree-p Expression3)
          (parse-tree-p InfixOpExpression3Rag)))

    (("Statement" ("RETURN" "return") expr ("SEMICOLON" ";"))
     (parse-tree-p expr))

    (("BlockStatement" rest)
     (parse-tree-p rest))

    (("Block" ("LBRACK" "{") blockstatements ("RBRACK" "}"))
     (parse-tree-p blockstatements))

    (("BlockStatements" blockstatement)
     (parse-tree-p blockstatement))
    (("BlockStatements" blockstatement blockstatements)
     (and (parse-tree-p blockstatement)
          (parse-tree-p blockstatements)))

    ;; One approach to infixops:
    (("InfixOp" InfixOp)
     (infix-op-p InfixOp))
   
    ;; ;; Another approach to infix ops, which would involve writing infixop-p
    ;; (("InfixOpExpression3Rag" InfixOp Expression3)
    ;;  (and (infixop-p InfixOp)
    ;;       (parse-tree-p Expression3)))
    ;; ;; Yet another approach to infix ops
    ;; (("InfixOpExpression3Rag" (InfixOp-name infix-op-symbol) Expression3)
    ;;  (and (stringp infixop-name)
    ;;       (stringp infixop-symbol)
    ;;       (parse-tree-p Expression3)))

    

    (("Identifier" ("IDENTIFIER" id-name))
     (stringp id-name))
    (& nil)))
    


(ACL2::assert!
 (parse-tree-p 
  '("IdentifierRag"
    ("Identifier" ("IDENTIFIER" "x"))
    ("PERIOD" ".")
    ("IdentifierRag"
     ("Identifier" ("IDENTIFIER" "y"))
     ("PERIOD" ".")
     ("IdentifierRag"
      ("Identifier" ("IDENTIFIER" "z"))
      ("PERIOD" ".")
      ("IdentifierRag"
       ("Identifier" ("IDENTIFIER" "a"))
       ("PERIOD" ".")
       ("IdentifierRag"
        ("Identifier" ("IDENTIFIER" "b"))
        ("PERIOD" ".")
        ("IdentifierRag"
         ("Identifier" ("IDENTIFIER" "c"))))))))))
