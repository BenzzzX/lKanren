#lang racket
(define (current-continuation) 
  (call/cc 
   (λ (cc)
     (cc cc))))

(define fail-stack '())

(define (fall)
  (if (not (pair? fail-stack))
      (display "error! no more solution.")
      (let ((back-track-point (car fail-stack)))
        (set! fail-stack (cdr fail-stack))
        back-track-point)))

(define (fail)
  (let ((fall-point (fall)))
    (fall-point fall-point)))

(define (amb choices)
  (let ((cc (current-continuation)))
    (cond
      [(null? choices) (fail)]
      [(pair? choices) (let ((choice (car choices)))
                         (set! choices (cdr choices))
                         (set! fail-stack (cons cc fail-stack))
                         choice)])))

(define-syntax var
  (syntax-rules ()
    ((_ x) (vector 'var (quote x)))))

(define (var? x)
  (vector? x))

(define (extend x y env)
  (cons (cons x y) env))

(define (walk var env)
  (if (var? var)
      (let ((value (assq var env)))
        (if value
            (walk (cdr value) env)
            var))
      var))

(define (walk* var env)
  (let ((var (walk var env)))
    (if (pair? var)
        (cons (walk* (car var) env)
              (walk* (cdr var) env))
        var)))

(define (match a b env)
  (let ((a (walk a env))
        (b (walk b env)))
    (cond
      [(eq? a b) env]
      [(var? a) (extend a b env)]
      [(var? b) (extend b a env)]
      [(and (pair? a)
            (pair? b))
       (match (cdr a) (cdr b)
         (match (car a) (car b) env))]
      [else (fail)])))

(define (== a b)
  (λ (env) (match a b env)))

(define-syntax exist
  (syntax-rules ()
    ((_ (x ...) f ...)
     (let ((x (var)) ...) (r-and f ...)))))

(define-syntax r-and
  (syntax-rules ()
    ((_ f) f)
    ((_ f t ...)
     (λ (env)
       ((r-and t ...) (f env))))))

(define-syntax r-or
  (syntax-rules ()
    ((_ t ...)
     (λ (env)
       ((amb (list t ...)) env)))))

(define-syntax r-cond
  (syntax-rules ()
    ((_ [a ...] ...)
     (r-or (r-and a ...) ...))))

(define (inst-name n)
  (string->symbol
   (string-append "_" (number->string n))))

(define (inst x env)
  (walk*
   (walk* x env)
   (let inst-env ((x x) (env '()))
     (let ((x (walk x env)))
       (cond
         ((var? x)
          (extend x (inst-name (length env)) env))
         ((pair? x) (inst-env (cdr x)
                              (inst-env (car x) env)))
         (else env))))))

(define-syntax query*
  (syntax-rules ()
    ((_ (x ...) f)
     (let ((res '()) (x (var x)) ...)
       (set! fail-stack '())
       (if (amb '(#t #f))
           (let ((env (f '())))
             (set! res (cons (inst (list x ...) env) res))
             (fail))
           res)))))









