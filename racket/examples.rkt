#!/usr/bin/racket
#lang racket

(require "srfi/201.rkt")

;; Before showing the capabilities of SRFI-201,
;; we're going to build a little unit test framework
;; for ourselves. The main interface to the framework
;; will be the "e.g." form, whose main use is going to
;; be:

;; (e.g. <expression> ===> <value>)

;; which checks whether <expression> evaluates to <value>,
;; and reports an error if that's not the case.

;; A more primitive use of the form is

;; (e.g. <expression>)

;; which passes if <expression> evaluates to non-#f value.
;; The former usage could therefore be defined in the
;; terms of the latter as:

;; (e.g. <expression> ===> <value>)
;; === (e.g. (equal? <expression> '<value>))

;; Moreover, since Scheme expressions can in general have
;; more (or less) than one value, we allow the usages:

;; (e.g. <expression> ===> <values> ...)

;; where <values> ... is a sequence of zero or more
;; literals.

;; Our examples, however, are also going to include
;; expressions that are not valid syntax, or ones such
;; that their execution causes runtime errors (similar
;; to arity mismatch in procedure application)

;; Therefore, expressions causing runtime errors
;; will be expressed as

;; (e.g. <expression> ===>! runtime-error)

;; and expressions causing expansion-time errors
;; will be marked as

;; (e.g. <expression> ===>! syntax-error)

;; Note that it is an error for such expressions not
;; to raise an error!

;; There's also another class of expressions that we want
;; to be able to express, namely - syntactic forms whose
;; behavior is unspecified, and such that may or may not
;; raise an error, depending on a specific implementation.
;; We need to be prepared for handling errors from them,
;; but it's OK if they don't raise any errors.

;; We're going to mark these expressions using the ===>?!
;; arrow.

(define-syntax e.g.
  (syntax-rules (===>
		 ===>!
		 ===>?!
		 syntax-error
		 runtime-error)
    ;; let's start with the simplest case: a test which
    ;; fails when expression evaluates to #f
    ((e.g. <example>)
     (or <example>
	 (error "false example" '<example>)))

    ;; and here's a variant with an expected result
    ((e.g. <expression> ===> <values> ...)
     (call-with-values (lambda () <expression>)
       (lambda results
	 (if (equal? results '(<values> ...))
	     (apply values results)
	     (error "false example"
		    '<expression>
		    `(expected ,<values> ...
			       got . ,results))))))

    ;; in case of runtime errors, we need to use Guile's
    ;; mechanism for recovering from errors:
    ((e.g. <expression> ===>! runtime-error)
     ;; if an error is raised,
     ;; we return the information about
     ;; the error
     (let ((failure (with-handlers ((exn:fail? identity))
		      ;; if <expression> succeeds,
		      ;; we return #f so that the handler
		      ;; will know that  no error has
		      ;; occurred, and will be
		      ;; able to report that as an error
		      <expression>
		      #f)))
       (or failure
	   (error "unexpected success" '<expression>))))

    ;; the case of detecting syntax errors is a bit more
    ;; complicated: if we tried to include a piece of
    ;; invalid syntax as an expression, we would obtain
    ;; syntactically invalid program. So instead we quote
    ;; the expression and try to evaluate it, expecting
    ;; an error
    ((e.g. <expression> ===>! syntax-error)
     (let ((failure (with-handlers ((exn:fail? identity))
		      (eval '<expression>)
		      #f)))
       (or failure
	   (error "unexpected success" '<expression>))))

    ;; In the case of "unspecified behavior", we only
    ;; need to protect ourselves from the possibility
    ;; of <expression> causing either runtime or expansion
    ;; time error, but it's ok if none of such errors
    ;; occurs
    ((e.g. <expression> ===>?! reason)
     (with-handlers ((exn:fail? identity))
       (eval '<expression>)))
    ))

;; Now that we have built a "metalanguage" for talking about
;; the values/behaviors of expressions, we can move on to
;; specifying the extensions to the core macros.

;; The ones presented here are built on top of Alex Shinns
;; match macro, which is shipped with Guile as the
;; (ice-9 match) module. It is important to emphasize
;; that SRFI-201 is intended to work with whatever pattern
;; matcher is provided for a given Scheme implementation.

;; SRFI-201's let form allows to handle
;; multiple values and perform desttucturing
;; bindings
(e.g.
 (let ((`(,x) `(,y) (values '(1) '(2))))
   (list x y))
 ===> (1 2))


;; The additional values, if present, are ignored
(e.g.
 (let ((x y (values 1 2 3)))
   (list x y))
 ===> (1 2))

;; If there's one multiple-value binding in a let
;; form, it must be the only binding in that form.

;; While it would be possible to implement this,
;; preserving the semantics of the 'let' form,
;; it would require capturing the results into
;; heap-allocated lists, which might be inefficient.
;;
;; For this reason, we encourage to use multiple
;; multiple value bindings only inside of a let* form,
;; which allows to implement this facility more
;; efficiently and naturally.

(e.g.
 (let ((x y (values 1 2))
       (z 3))
   (list x y z)) ===>?! syntax-error)

(e.g.
 (let (((values x y) '(values 1 2))
       (z 3))
   (list x y z)) ===>?! syntax-error)

;; The 'values' keyword is treated specially
;; in the context of binding:
(e.g.
 (let (((values x y) (values 1 2)))
   (list x y))
 ===> (1 2))

;; This no longer allows us to ignore unused
;; values
(e.g.
 (let (((values x y) (values 1 2 3)))
   (list x y))
 ===>! runtime-error)

;; But, the remaining values can be captured
;; in a list:
(e.g.
 (let (((values x y . z) (values 1 2 3)))
   (values
    (list x y)
    z))
 ===> (1 2) (3))

;; The 'named-let' is of course supported
(e.g.
 (let loop ((x 0))
   (if (>= x 10)
       x
       (loop (+ x 1))))
 ===> 10)

;; and it is also capable of destructuring
(e.g.
 (let loop ((`(,x) '(0)))
   (if (>= x 10)
       x
       (loop `(,(+ x 1)))))
 ===> 10)

;; There is an option to use a named-let with multiple
;; values:

(e.g.
 (let loop ((`(,x) y (values '(1) 2)))
   (if (>= (+ x y) 10)
       (values x y)
       (loop `(,(+ x 1)) (+ y 1))))
 ===> 5 6)

;; It also works with the 'values' keyword:

(e.g.
 (let loop (((values x `(,y)) (values 1 '(2))))
   (if (>= (+ x y) 10)
       (values x y)
       (loop (+ x 1) `(,(+ y 1)))))
 ===> 5 6)

;; But like with unnamed let, if there's a multiple value
;; binding, it precludes all other bindings from the form:

(e.g.
 (let loop ((a b (values 1 2))
	    (c 3))
   'whatever) ===>! syntax-error)

;; and the 'values' keyword doesn't change that:

(e.g.
 (let loop (((values a b) (values 1 2))
	    (c 3))
   'whatever) ===>! syntax-error)


;; The let* form inherits most of the let form's
;; capabilities:
(e.g.
 (let* ((`(,x) y (values '(1) 2 3))
	(z `(,w) (values 4 '(5))))
   (list x y z w))
 ===> (1 2 4 5))

;; including the support for the "values"
;; keyword on left positions

(e.g.
 (let* (((values `(,x) y . _) (values '(1) 2 3))
	((values z `(,w)) (values 4 '(5))))
   (list x y z w))
 ===> (1 2 4 5))


;; The lambda keyword allows to destructure arguments

(e.g.
 (map (lambda (`(,l . ,r))
	(+ l r))
      '((1 . 2) (3 . 4) (5 . 6)))
 ===> (3 7 11))

;; But body-less lambdas can be used e.g. for
;; filtering based on patterns:

(e.g.
 (filter (lambda (`(,_ ,_ ,_)))
	 '((1 2) (3 4 5) (6 7) (8 9 0)))
 ===> ((3 4 5) (8 9 0)))

;; This also allows to express a procedure that returns #t
;; for any argument as

(e.g.
 (lambda _))

;; and I think it's beautiful.

(e.g.
 (and ((lambda _))
      (andmap (lambda _) (list "1" 5 '(x y) '() #f))
      ((lambda _) "1" 5 '(x y) '())))

;; It is an error to apply a lambda to an object that cannot
;; be properly desctructured (just like it is an error
;; to apply a lambda to a larger or smaller number of arguments
;; than it supports, i.e. arity mismatch error)

(e.g.
 ((lambda (`(,x . ,y)) 'whatever) '()) ===>! runtime-error)

;; The 'define' keyword supports currying, and it
;; desugars to destructuring lambdas:

(e.g.
 (let ()
   (define ((f `(,a ,b)) `(,c ,d))
     `(,a ,b ,c ,d))
   ((f '(1 2)) '(3 4)))
 ===> (1 2 3 4))

;; Body-less curried definitions only test for validity
;; of patterns, so they don't throw 'invalid match'
;; errors, but return #t on successful

(e.g.
 (let ()
   (define ((f `(,a ,b)) `(,c ,d)))
   (and ((f '(1 2)) '(3 4))
	(not ((f 5) '(6 7))))))

;; The "or" form ought to perform short-circuiting
;; while still supporting multiple values. Only the
;; first value can account to short-circuiting:

(e.g.
 (or (values #f 5)
     (values 6 7 8))
 ===> 6 7 8)

(e.g.
 (or (values #t 5)
     (values 6 7 8))
 ===> #t 5)

;; As in the context of if's condition, any value
;; other than #f is considered true:

(e.g.
 (or (values 4 5)
     (values 6 7 8))
 ===> 4 5)
