(define-module (srfi srfi-201)
  #:use-module (srfi srfi-1)
  #:use-module (ice-9 match)
  #:replace ((cdefine . define)
	     (mlambda . lambda)
	     (named-match-let-values . let)
	     (or/values . or)
	     (match-let*-values . let*)))

(define-syntax mlambda
  (lambda (stx)
    (syntax-case stx ()
      ;; lambda with no body is treated as a pattern predicate,
      ;; returning #t if the argument matches, and #f otherwise
      ((_ args)
       #'(lambda args*
	   (match args*
	     (args #t)
	     (_ #f))))

      ;; in case of patterns consisting entitely
      ;; of identifiers, we desugar to the core lambda
      ((_ (first-arg ... last-arg . rest-args) . body)
       (and (every identifier? #'(first-arg ... last-arg))
	    (or (identifier? #'rest-args) (null? #'rest-args)))
       #'(lambda (first-arg ... last-arg . rest-args) . body))

      ((_ arg body ...)
       (or (identifier? #'arg) (null? #'arg))
       #'(lambda arg body ...))

      ((_ pattern body ...)
       #'(lambda args
	   (match args
	     (pattern body ...)
	     (_ (error
		 `((mlambda pattern body ...) ,args))))))
      )))

(define-syntax cdefine
  (syntax-rules ()
    ;; for consistency with bodyless lambdas,
    ;; bodyless curried definitions only pattern-match
    ;; on their arguments, and return #t if all matches
    ;; succeed, or #f if some of the matches fail
    ((_ (prototype . args))
     (cdefine-bodyless (prototype . args) #t))

    ((_ ((head . tail) . args) body ...)
     (cdefine (head . tail)
	      (mlambda args body ...)))
    ((_ (function . args) body ...)
     (define function
       (mlambda args body ...)))
    ((_ . rest)
     (define . rest))
    ))

(define-syntax cdefine-bodyless
  (syntax-rules ()
   ((_ (function . pattern) result . args)
    (cdefine-bodyless function
		      (match arg
			(pattern result)
			(_ #f))
		      arg . args))

   ((_ name result args ... arg)
    (cdefine-bodyless name (lambda arg result) args ...))

   ((_ name value)
    (define name value))
   ))

(define-syntax match-let/error
  (syntax-rules ()
    ((_ ((structure expression) ...)
	body + ...)
     ((lambda args
	(match args
	  ((structure ...) body + ...)
	  (_ (error 'match-let/error
		    (current-source-location)
		    '((structure expression) ...)
		    expression ...))))
      expression ...))))

(define-syntax named-match-let-values
  (lambda (stx)
    (syntax-case stx (values)
      ((_ ((identifier expression) ...)
	  body + ...)
       (every identifier? #'(identifier ...))
       ;; optimization: plain "let" form
       #'(let ((identifier expression) ...)
	   body + ...))

      ((_ name ((identifier expression) ...)
	  body + ...)
       (and (identifier? #'name)
	    (every identifier? #'(identifier ...)))
       ;; optimization: regular named-let
       #'(let name ((identifier expression) ...)
	   body + ...))

      ((_ name (((values . structure) expression))
	  body + ...)
       (identifier? #'name)
       #'(letrec ((name (mlambda structure body + ...)))
	   (call-with-values (lambda () expression) name)))

      ((_ (((values . structure) expression)) body + ...)
       #'(call-with-values (lambda () expression)
	   (mlambda structure body + ...)))

      ((_ name ((structure expression) ...)
	  body + ...)
       (and (identifier? #'name)
	    (any (lambda (pattern)
		   (and (pair? pattern)
			(eq? (car pattern) 'values)))
		 (syntax->datum #'(structure ...))))
       #'(syntax-error "let can only handle one binding \
in the presence of a multiple-value binding"))

      ((_ name ((structure expression) ...)
	  body + ...)
       (identifier? #'name)
       #'(letrec ((name (mlambda (structure ...) body + ...)))
	   (name expression ...)))

      ((_ ((structure expression) ...)
	  body + ...)
       (any (lambda (pattern)
	      (and (pair? pattern)
		   (eq? (car pattern) 'values)))
	    (syntax->datum #'(structure ...)))
       #'(syntax-error "let can only handle one binding \
in the presence of a multiple-value binding"))

      ((_ ((structure expression) ...)
	  body + ...)
       #'(match-let/error ((structure expression) ...)
			  body + ...))

      ((_ ((structure structures ... expression)) body + ...)
       #'(call-with-values (lambda () expression)
	   (mlambda (structure structures ... . _)
		    body + ...)))

      ((_ name ((structure structures ... expression))
		body + ...)
       (identifier? #'name)
       #'(letrec ((name (mlambda (structure structures ...)
			     body + ...)))
	   (call-with-values (lambda () expression) name)))

      ;; it should generally be discouraged to use the plain
      ;; let with multiple values, because there's no natural
      ;; way to implement that when there's more than one
      ;; (multiple-value) binding,
      ;; but it could be added for completeness
#|
      ((_ ((structure structures ... expression) ...)
	  body + ...)
       #'(match-let/error (((structure structures ... . _)
			    (list<-values expression)) ...)
			  body + ...))

      ((_ name ((structure structures ... expression) ...)
	  body + ...)
       (identifier? #'name)
       #'(letrec ((loop
		   (lambda args
		     (match args
		       (((structure structures ... . _) ...)
			(let-syntax ((name
				      (syntax-rules ()
					((_ args (... ...))
					 (loop (list<-values
						args)
					       (... ...))))))
			  body + ...))
		     (_ (error 'named-match-let-values
			       (current-source-location)
			       'name)))))
		  (loop (list<-values expression) ...)))
|#
      )))

(define-syntax or/values
  (syntax-rules ()
    ((_)
     #false)

    ((or/values final)
     final)

    ((or/values first . rest)
     (call-with-values (lambda () first)
       (lambda result
	 (if (and (pair? result) (car result))
	     (apply values result)
	     (or/values . rest)))))))

(define-syntax match-let*-values
  (lambda (stx)
    (syntax-case stx ()
      ((_ ((identifier expression) ...) body + ...)
       (every identifier? #'(identifier ...))
       ;; optimization/base case: regular let*
       #'(let* ((identifier expression) ...)
	   body + ...))
      ((_ (binding . bindings) body + ...)
       #'(named-match-let-values (binding)
				 (match-let*-values
				  bindings
				  body + ...))))))
