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

(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/deflist" :dir :system)

(program)

; Here I define a class foo, which has two members, my-int-a and my-int-b.  I
; then specify that integerp should be true for both my-int-a and my-int-b.

(cutil::defaggregate foo
  ((my-int-a integerp)
   (my-int-b integerp))
  :tag :foo) ; always use :tag and then place a classname with a colon pre-pended to it

(defconst *my-foo*
  (make-foo :my-int-a 3 
            :my-int-b 4))

(foo->my-int-a *my-foo*)

(integerp (foo->my-int-a *my-foo*))

(foo->my-int-b *my-foo*)

(change-foo *my-foo*
            :my-int-a 99)

; Here I define a class bar, which has two members, my-int-c and my-foo.  I
; then specify that my-int-c should be an integerp and that my-foo should be a
; foo-p (defined in the previous definition).

(cutil::defaggregate bar
  ((my-int-c integerp)
   (my-foo foo-p))
  :tag :bar)

(defconst *my-bar*
  (make-bar :my-int-c 5
            :my-foo *my-foo*))

(bar->my-int-c *my-bar*)

(bar->my-foo *my-bar*)

(defconst *my-second-bar*
  (make-bar :my-int-c 6
            :my-foo (make-foo :my-int-a 10
                              :my-int-b 11)))

(bar->my-int-c *my-second-bar*)

(bar->my-foo *my-second-bar*)

(assert$ (foo-p (bar->my-foo *my-second-bar*))
         "success!")

; Here I define a predicate that recognizes a list of natural numbers.  My hope
; is that you won't need to define such predicates that much.

(cutil::deflist nat-list-p (x) ; always use "x"
  (natp x)
  :elementp-of-nil nil
  :true-listp t)

(defconst *my-list-of-nats*
  '(1 2 3 4 5 6))

(nth 3 *my-list-of-nats*) ; first element is in slot 0

(assert$ (nat-list-p *my-list-of-nats*)
         "success!")

(cutil::defaggregate dependent-foo
  ((my-int-q integerp)
   (my-int-r integerp))
  :require
  ((alemma
    (and (integerp my-int-q)
         (integerp my-int-r)
         (< my-int-q my-int-r))))
  :tag :dependent-foo)
