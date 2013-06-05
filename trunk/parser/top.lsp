; ACL2 Parser for Java
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

(include-book "earley-parser")

(defconsts (*oracle-grammar* state)
  (load-bnf-grammar "./examples/oracle-grammar.txt" state))

(defconsts (*oracle-lexicon* state)
  (load-lexicon "./examples/oracle-lexicon.txt" state))

(defconsts *oracle-tree-list*
  (chart-list->trees
   (earley-parse "hello . there" *oracle-grammar* *oracle-lexicon*)))
#|
(assert! (equal *oracle-tree-list*
                '(("S" ("VP" ("verb" "book")
                        ("NP" ("det" "that")
                         ("nominal" ("integer" "787"))))))))
|#



(include-book "cutil/tools/assert-return-thms" :dir :system)
(assert-return-thms read-next-bnf-lexeme1)
(assert-return-thms read-next-bnf-lexeme)
(assert-return-thms fix-production)
(assert-return-thms read-next-bnf-production)
(assert-return-thms inject-expansions!) 
(assert-return-thms load-bnf-grammar2)
(assert-return-thms load-bnf-grammar1)
(assert-return-thms predictor1)
(assert-return-thms predictor)
(assert-return-thms member-lexicon-equal)
(assert-return-thms scanner)
(assert-return-thms completer1)
(assert-return-thms completer)
(assert-return-thms earley-parse400)
(assert-return-thms earley-parse200)
(assert-return-thms earley-parse100)
(assert-return-thms earley-parse50)
(assert-return-thms earley-parse25)
(assert-return-thms earley-parse)



(chart-list->trees
 (earley-parse "public class helloworld { public static void main (
         String [] args ) {}}" 
               *oracle-grammar* *oracle-lexicon*))


(chart-list->trees
 (earley-parse "public class helloworld { public static void foo (
         int x  ) {}}" 
               *oracle-grammar* *oracle-lexicon*))


(chart-list->trees
 (earley-parse "public class helloworld { public static void foo (
         int x , int y ) {}}" 
               *oracle-grammar* *oracle-lexicon*))

(chart-list->trees

; This example is the first that yields an ambiguous parse tree.  Here are the
; snippets of the two trees that differ:
#|
 ("Expression2"
  ("Expression3"
   ("Primary"
    ("IdentifierRag" ("Identifier" ("IDENTIFIER" "x")))))
  ("Expression2Rest"
   ("InfixOpExpression3Rag"
    ("InfixOp" ("PLUS" "+"))
    ("Expression3"
     ("Primary"
      ("IdentifierRag"
       ("Identifier" ("IDENTIFIER" "y"))))))))

 ("Expression2"
  ("Expression3"
   ("Primary"
    ("IdentifierRag" ("Identifier" ("IDENTIFIER" "x"))))
   ("SelectorRag"
    ("Selector"
     ("Expression"
      ("Expression1"
       ("Expression2"
        ("Expression3"
         ("PrefixOp" ("PLUS" "+"))
         ("Expression3"
          ("Primary"
           ("IdentifierRag"
            ("Identifier" ("IDENTIFIER" "y")))))))))))))
|#

 (earley-parse "public class helloworld { public static int foo (
         int x , int y ) { return x + y ; }}" 
               *oracle-grammar* *oracle-lexicon*))

(chart-list->trees
 (earley-parse "

public class arithmetic { 
  public static int add (int x, int y) { 
    return x + y;
  }
}" 
               *oracle-grammar* *oracle-lexicon*))

(chart-list->trees
 (earley-parse "public class helloworld { public static int foo (
         int x , int y ) { int z = x + y ;  return z ;}}" 
               *oracle-grammar* *oracle-lexicon*))

(chart-list->trees
 (earley-parse "public class helloworld { public static void main (
         String [] args ) { int z = x + y ;  return z * args;}}" 
               *oracle-grammar* *oracle-lexicon*))

(chart-list->trees
 (earley-parse "public class helloworld { public static void main (
         String [] args ) { foo (  ) ; }}" 
               *oracle-grammar* *oracle-lexicon*))
