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

(include-book "cutil/define" :dir :system)

(program)

; Below, we define a function named "my-f" that takes two arguments, an
; integerp x and stringp y.  It then returns the maximum of x and the length of
; y.  We could define this function by just using "defun", but then, later,
; when we went to prove anything about it, our proof burdern would be heavier.
; By using define and specifying more properties about this function up-front,
; we save ourselves work later.

(cutil::define my-f ; function name

; Now we provide a list of lists, where the first element of each inner list is
; the argument name, the second element of each inner list is the
; type/predicate the describes the argument, and the third element of each
; inner list is the documentation for that argument.

; First we define the first arugment, x, which should be an integerp.

 ((x integerp "Documentation for the first argument")

; Now we define the second argument, y, which should be a stringp.

  (y stringp "Documentation for the second argument"))

; Now we describe the return value, by providing: (1) a name for the return
; value (used in more advanced defintions), (2) the type/predicate that
; describes the return value, and (3) documentation for the return value.  We
; include :hyp :fguard at the end of it for logical reasons (this notation
; means that the types of the input arguments should be used as preconditions
; for when we prove that the function returns what is specified below).

; In this case, we name the return value "retval", state that it should be an
; integerp, and document it.  

 :returns (retval integerp "Documentation for the return value"
                  :hyp :fguard)
 
 ; Now we define our function's body (the easy part)!

 (max x (length y)))

(my-f 3 "hi")

(my-f 3 "hello")


(cutil::define my-f-two ; function name
 ((x integerp "Documentation for the first argument")
  (y stringp "Documentation for the second argument"))

 :returns (mv (retval1 integerp "Documentation for the return value"
                       :hyp :fguard)
              (retval2 booleanp "Documentation for the second return value"
                       :hyp :fguard))
 
 ; Now we define our function's body (the easy part)!

 (mv (max x (length y)) (null y)))

(my-f-two 3 "hi")

(my-f-two 3 "hello")
