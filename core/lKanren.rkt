#lang racket

;core
(define (var) (vector))

(define (var? x) (vector? x))

(define (extend x y env)
  `((,x . ,y) . ,env))

(define (walk var env)
  (if (var? var)
      (let ((value (assq var env)))
        (if value
            (walk (cdr value) env)
            var))
      var))

(define (unify a b env)
  (if (not env) #f
      (let ((a (walk a env))
            (b (walk b env)))
        (cond
          [(eq? a b) env]
          [(var? a) (extend a b env)]
          [(var? b) (extend b a env)]
          [(and (pair? b) (pair? a))
           (unify (cdr a) (cdr b)
             (unify (car a) (car b) env))]
          [else #f]))))

(define-syntax lazy
  (syntax-rules ()
    ((_ f) (λ (env)
             (λ () (f env))))))

(define (mplus a b)
  (cond
    [(null? a) b]
    [(procedure? a) (λ () (mplus b (a)))] ;lazy carry
    [else (cons (car a) (mplus (cdr a) b))]))

(define (bind a b)
  (cond
    [(null? a) '()]
    [(procedure? a) (λ () (bind (a) b))] ;lazy carry
    [else (mplus (b (car a)) (bind (cdr a) b))]))

(define (disj a b)
  (λ (env) (mplus (a env) (b env))))

(define (conj a b)
  (λ (env) (bind (a env) b)))

;reduction
(define (inst-name n)
  (string->symbol
   (string-append "_" (number->string n))))

(define (walk* var env)
  (let ((var (walk var env)))
    (if (pair? var)
        (cons (walk* (car var) env)
              (walk* (cdr var) env))
        var)))

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

(define (pull stream)
  (if (procedure? stream)
      (pull (stream))
      stream))

(define (pull* stream)
  (let ((h (pull stream)))
    (if (null? h) '()
        (cons (car h) (pull* (cdr h))))))

(define (pulln n stream)
  (if (zero? n) '()
      (let ((h (pull stream)))
        (if (null? h) '()
            (cons (car h) (pulln (- n 1) (cdr h)))))))
;interfaces
(provide r-= r-exist r-and r-or r-cond reduct* reduct)

(define (r-= a b)
  (λ (env)
    (let ((s (unify a b env)))
      (if s (list s) '()))))

(define-syntax r-exist
  (syntax-rules ()
    ((_ (x ...) f ...)
     (let ((x (var)) ...) (r-and f ...)))))

(define-syntax r-and
  (syntax-rules ()
    ((_ f) (lazy f))
    ((_ f t ...)
     (conj (lazy f) (r-and t ...)))))

(define-syntax r-or
  (syntax-rules ()
    ((_ f) (lazy f))
    ((_ f t ...)
     (disj (lazy f) (r-or t ...)))))

(define-syntax r-cond
  (syntax-rules ()
    ((_ [a ...] ...)
     (r-or (r-and a ...) ...))))

(define-syntax reduct*
  (syntax-rules (in)
    ((_ (x ...) in f)
     (let ((x (var)) ...)
       (map (λ (env) (inst (list x ...) env))
            (pull* (f '())))))))

(define-syntax reduct
  (syntax-rules (in)
    ((_ n (x ...) in f)
     (let ((x (var)) ...)
       (map (λ (env) (inst (list x ...) env))
            (pull n (f '())))))))

(define-syntax pmatch
  (syntax-rules (_ quote unquote)
    ((_ v [_ t ...]) (r-and t ...))
    ((_ v [() t ...]) (r-and (r-= v '()) t ...))
    ((_ v [(unquote var) t ...]) (r-and (r-= v var) t ...))
    ((_ v [(quote lit) t ...]) (r-and (r-= v (quote lit)) t ...))
    ((_ v [(l . r) t ...])
     (r-exist (vl vr)
            (r-= v `(,vl . ,vr))
            (pmatch vl [l (pmatch vr [r t ...])])))
    ((_ v [var t ...]) (r-exist (var) (r-= v var) t ...))))

(define x 1)
(define (f a)
  (pmatch a [('x ,x)]))

(reduct* (x) in (f x))
     
    