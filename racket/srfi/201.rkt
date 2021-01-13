#lang racket
(require racket/match)

(define-for-syntax (every pred stx)
  (andmap pred (syntax->list stx)))

(define-for-syntax (any pred stx)
  (ormap pred (syntax->list stx)))

(define-for-syntax (empty? stx)
  (null? (syntax->list stx)))

(define-for-syntax (racket-argument? x)
  "racket argument is either an identifier, a keyword or a [name value] pair"
  (or (identifier? x)
      (keyword? (syntax->datum x))
      (let ((list (syntax->list x)))
	(and (list? list)
	     (= (length list) 2)
	     (let ((name (syntax->datum (car list))))
	       (and (not (eq? name 'quote))
		    (not (eq? name 'quasiquote))))))))

(provide #%module-begin #%app #%datum syntax-rules
         (rename-out [cdefine define]
                     [mlambda lambda]
                     [named-match-let-values let]
                     [or/values or]
                     [match-let*-values let*]
		     ))

(define-syntax list-pattern
  ;; convert Scheme-style arguments (proper or improper
  ;; lists) into Racket matcher's pattern (either
  ;; (list args ...) or (list-rest args ... tail))
  (syntax-rules ()
    ((list-pattern final failure (first second . rest)
		   (processed ...) body ...)
     (list-pattern final failure (second . rest)
		   (processed ... first) body ...))

    ((list-pattern (final ...) failure (last)
		   (processed ...)
		   body ...)
     (final ... ((list processed ... last) body ...)
            (_ failure)))

    ((list-pattern (final ...) failure (last . tail)
		   (processed ...) body ...)
     (final ... ((list-rest processed ... last tail)
		 body ...)
            (_ failure)))

    ((list-pattern (final ...) failure improper
		   () body ...)
     (final ... (improper body ...) (_ failure)))))

(define-syntax-rule (match-lambda-rest failure args
				       processed body ...)
  (list-pattern (match-lambda*) failure args
		processed body ...))

(define-syntax mlambda
  (lambda (stx)
    (syntax-case stx ()

      ((_ args)
       #'(match-lambda-rest #f args () #t))

      ((_ (first-arg ... last-arg . rest-args) . body)
       (and (every racket-argument?
		   #'(first-arg ... last-arg))
            (or (identifier? #'rest-args)
                (empty? #'rest-args)))
       #'(lambda (first-arg ... last-arg . rest-args) . body))

      ((_ arg body ...)
       (or (identifier? #'arg) (empty? #'arg))
       #'(lambda arg body ...))

      ((_ args body ...)
       #'(match-lambda-rest
	  (error "invalid pattern"
		 '(lambda args body ...)) args () body ...))
      )))

(define-syntax cdefine
  (syntax-rules ()
    ((_ (prototype . args))
     (cdefine-bodyless (prototype . args) #t))

    ((_ ((head . tail) . args) body ...)
     (cdefine (head . tail) (mlambda args body ...)))

    ((_ (function . args) body ...)
     (define function
       (procedure-rename
	(mlambda args body ...)
	'function)))
    ((_ . rest)
     (define . rest))
    ))

(define-syntax cdefine-bodyless
  (syntax-rules ()
   ((_ (function . pattern) result . args)
    (cdefine-bodyless function
		      (list-pattern
		       (match arg)
		       #f
		       pattern
		       ()
		       result)
		      arg . args))

   ((_ name result args ... arg)
    (cdefine-bodyless name (lambda arg result) args ...))

   ((_ name value)
    (define name value))
   ))

(define-syntax-rule (match-let/error ((structure
				       expression) ...)
				     body + ...)
  ((match-lambda-rest
    (error "invalid pattern"
	   '(let ((structure expression) ...) body + ...)
	   `(expression ,expression) ...)

    (structure ...) () body + ...)
   expression ...))

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
       (identifier? #'name)
       #'(letrec ((name (mlambda (structure ...)
				 body + ...)))
           (name expression ...)))

      ((_ ((structure expression) ...)
          body + ...)
       #'(match-let/error ((structure expression) ...)
                          body + ...))

      ((_ ((identifier identifiers ... expression))
	  body + ...)
       (every identifier? #'(identifier identifiers ...))
       #'(call-with-values
	     (lambda () expression)
           (lambda (identifier identifiers ... . _)
             body + ...)))

      ((_ ((structure structures ... expression))
	  body + ...)
       #'(call-with-values
	     (lambda () expression)
           (match-lambda-rest
            (error "invalid pattern"
		   '(let ((structure
			   structures
			   ...
			   expression))
		      body + ...))
            (structure structures ... . _)
            () body + ...)))

      ((_ name ((identifier identifiers ... expression))
	  body + ...)
       (and (identifier? #'name)
            (every identifier? #'(identifier
				  identifiers ...)))
       #'(let ((name (lambda (identifier identifiers ...)
		       body + ...)))
           (call-with-values (lambda () expression) name)))

      ((_ name ((structure structures ... expression))
	  body + ...)
       (identifier? #'name)
       #'(letrec ((name (match-lambda-rest
			 (error "invalid pattern"
				'(let name ((structure
					     structures
					     ...
					     expression))
				   body + ...))
			 (structure structures ...)
			 () body + ...)))
           (call-with-values (lambda () expression) name)))

      )))

(define-syntax or/values
  (syntax-rules ()
    ((_)
     #false)

    ((or/values final)
     final)

    ((or/values first . rest)
     (call-with-values
	 (lambda () first)
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
