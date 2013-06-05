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

(defconst *pase-tree*
  '("CompilationUnit"
    ("TypeDeclarationRag"
     ("TypeDeclaration"
      ("ClassOrInterfaceDeclaration"
       ("ModifierRag" ("Modifier" ("PUBLIC" "public")))
       ("ClassDeclaration"
        ("NormalClassDeclaration"
         ("CLASS" "class")
         ("Identifier" ("IDENTIFIER" "arithmetic"))
         ("ClassBody"
          ("LBRACK" "{")
          ("ClassBodyDeclarationRag"
           ("ClassBodyDeclaration"
            ("ModifierRag" ("Modifier" ("PUBLIC" "public"))
             ("ModifierRag" ("Modifier" ("STATIC" "static"))))
            ("MemberDecl"
             ("MethodOrFieldDecl"
              ("Type" ("BasicType" ("INT" "int")))
              ("Identifier" ("IDENTIFIER" "add"))
              ("MethodOrFieldRest"
               ("MethodDeclaratorRest"
                ("FormalParameters"
                 ("LPAREN" "(")
                 ("FormalParameterDecls"
                  ("Type" ("BasicType" ("INT" "int")))
                  ("FormalParameterDeclsRest"
                   ("VariableDeclaratorId" ("Identifier" ("IDENTIFIER" "x")))
                   ("COMMA" ",")
                   ("FormalParameterDecls"
                    ("Type" ("BasicType" ("INT" "int")))
                    ("FormalParameterDeclsRest"
                     ("VariableDeclaratorId"
                      ("Identifier" ("IDENTIFIER" "y")))))))
                 ("RPAREN" ")"))
                ("Block"
                 ("LBRACK" "{")
                 ("BlockStatements"
                  ("BlockStatement"
                   ("Statement"
                    ("RETURN" "return")
                    ("Expression"
                     ("Expression1"
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
                            ("Identifier" ("IDENTIFIER" "y"))))))))))
                    ("SEMICOLON" ";"))))
                 ("RBRACK" "}"))))))))
          ("RBRACK" "}")))))))))


(defconst *addition-tree*
  '("Expression2"
    ("Expression3"
     ("Primary"
      ("IdentifierRag" ("Identifier" ("IDENTIFIER" "x")))))
    ("Expression2Rest"
     ("InfixOpExpression3Rag"
      ("InfixOp" ("PLUS" "+"))
      ("Expression3"
       ("Primary"
        ("IdentifierRag"
         ("Identifier" ("IDENTIFIER" "y")))))))))

(defconst *id-tree*
  '("Expression"
    ("Expression1"
     ("Expression2"
      ("Expression3"
       ("Primary"
        ("IdentifierRag"
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
              ("Identifier" ("IDENTIFIER" "c"))))))))))))))


(defconst *primary-tree*
  '("Primary" ("IdentifierRag" ("Identifier" ("IDENTIFIER" "x")))))
