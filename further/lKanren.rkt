#lang racket
(require syntax/parse)
(require (for-syntax syntax/parse))
;core
(define-syntax-rule (var x) (vector (quote x)))

(define (var? x) (vector? x))

(define (extend x y graph)
  `((,x . ,y) . ,graph))

(define (walk var graph)
  (if (var? var)
      (let ((value (assq var graph)))
        (if value
            (walk (cdr value) graph)
            var))
      var))

(define (unify a b graph)
  (if (not graph) #f
      (let ((a (walk a graph))
            (b (walk b graph)))
        (cond
          [(eq? a b) graph]
          [(var? a) (extend a b graph)]
          [(var? b) (extend b a graph)]
          [(and (pair? b) (pair? a))
           (unify (cdr a) (cdr b)
             (unify (car a) (car b) graph))]
          [else #f]))))

(define-syntax lazy; create lazy tail for stream
  (syntax-rules ()
    [(_ f) (λ (env)
             (λ () (f env)))]))

(define (s-merge stream1 stream2); merge stream (logic or)
  (cond
    [(null? stream1) stream2]
    [(procedure? stream1) (λ () (s-merge stream2 (stream1)))]; lazy carry
    [else (cons (car stream1) (s-merge (cdr stream1) stream2))]))

(define (s-map stream relation); fliter stream (logic and)
  (cond
    [(null? stream) '()]
    [(procedure? stream) (λ () (s-map (stream) relation))]; lazy carry
    [else (s-merge (relation (car stream)) (s-map (cdr stream) relation))]))

(define (disj relation1 relation2); or
  (λ (env) (s-merge (relation1 env) (relation2 env))))

(define (conj relation1 relation2); and
  (λ (env) (s-map (relation1 env) relation2)))
 
;reduction
(define (inst-name n symbol)
  (string->symbol
   (string-append symbol (number->string n))))

(define (walk* var graph)
  (let ((var (walk var graph)))
    (if (pair? var)
        (cons (walk* (car var) graph)
              (walk* (cdr var) graph))
        var)))

(define (inst x graph symble)
  (walk* (walk* x graph)
   (let inst-env ((x x) (env '()))
     (let ((x (walk x graph)))
       (cond
         ((var? x)
          (extend x (inst-name (length env) symble) env))
         ((pair? x) (inst-env (cdr x)
                              (inst-env (car x) env)))
         (else env))))))

(define (filter x graph); only instantiate varibles that have constraint
  (cond
    [(null? x) '()]
    [(pair? x)
     (if (and (var? (car x)) (assq (car x) graph))
         (cons (car x) (filter (cdr x) graph))
         (filter (cdr x) graph))]))

(define (de-duplication x)
  (cond [(null? x) '()]
        [(memq (car x) (cdr x))
         (de-duplication (cdr x))]
        [else (cons (car x) (de-duplication (cdr x)))]))

(define (inst* x env); instantiate x with calculated enviroment
  (let* ((x (de-duplication x))
          (excepts (inst-=/= x (cdr env)))
          (fact (inst x (car env) "?")))
    (if (null? excepts) fact
        (cons fact (cons 'except excepts)))))

(define (inst-=/= x graphs); instantiate part that never equal
  (if (null? graphs) '()
      (let ((fixed (filter x (car graphs))))
        (if (null? fixed)
            (inst-=/= x (cdr graphs))
            (cons (inst (walk* fixed (car graphs)) (car graphs) "!")
                  (inst-=/= x (cdr graphs)))))))

(define (pull stream); force excute calculation
  (if (procedure? stream) (pull (stream)) stream))

(define (pull* stream)
  (let ((h (pull stream)))
    (if (null? h) '()
        (cons (car h) (pull* (cdr h))))))

(define (pulln n stream)
  (if (zero? n) '()
      (let ((h (pull stream)))
        (if (null? h) '()
            (cons (car h) (pulln (- n 1) (cdr h)))))))

(define (== a b)
  (λ (env)
    (==-verify (unify a b (car env)) env)))

(define (==-verify graph env)
  (cond [(not graph) '()] ; not equal,fail
        [(eq? graph (car env)) (list env)]; equal,succeed,do nothing
        [(verify-=/= (cdr env) '() graph)
         => (λ (g) (list (cons graph g)))]
        [else '()]))

(define (verify-=/= gs gs* graph)
  (cond [(null? gs) gs*]
        [(unify* (car gs) graph); try to expand not equal relation
         => (λ (g)
              (cond
                [(eq? graph g) #f]; equal,fail
                (else (let ((c (prefix-s g graph))); otherwise,take new relation to
                        (verify-=/= (cdr gs) (cons c gs*) graph)))))]; expand disequal relation
        [else (verify-=/= (cdr gs) gs* graph)])); if now it's surely disequal
                                                ; remove the disequal relation
  
(define (unify* l graph)
  (cond [(null? l) graph]
        [(unify (car (car l))
                (cdr (car l)) graph)
         => (λ (g) (unify* (cdr l) g))]
        {else #f}))

(define (=/= a b)
  (λ (env)
    (=/=-verify (unify a b (car env)) env))) ;reuse unify

(define (=/=-verify graph env)
  (cond [(not graph) (list env)] ; not equal,succeed,do nothing
        [(eq? graph (car env)) '()] ; equal,fail
        [else (let ((c (prefix-s graph (car env)))) ; otherwise,take new relation
                (list (cons (car env)               ; into disequal relation
                            (cons c (cdr env)))))]))

(define (prefix-s new-graph graph); find common prefix
  (if (eq? new-graph graph) '()
      (cons (car new-graph)
            (prefix-s (cdr new-graph) graph))))

(define-syntax exist; declare varialbe
  (syntax-rules ()
    [(_ (x ...) f ...)
     (let ((x (var x)) ...)  (ando f ...))]))

;tools
(define-syntax ando
  (syntax-rules ()
    [(_ f) (lazy f)]
    [(_ f t ...)
     (conj (lazy f) (ando t ...))]))

(define-syntax oro
  (syntax-rules ()
    [(_ f) (lazy f)]
    [(_ f t ...)
     (disj (lazy f) (oro t ...))]))

(define (fail env) '())

(define-syntax condo
  (syntax-rules ()
    [(_ [a ...] ...)
     (oro (ando a ...) ...)]
    [(_) (lazy fail)]))

(define-syntax ifo
  (syntax-rules ()
    ((_ cond true false)
     (condo [cond true]
             [!#t false]))))

(define (conso a b x) (== x `(,a . ,b)))
(define (caro x a)
  (exist (b)
    (conso a b x)))
(define (cdro x a)
  (exist (b)
    (conso b a x)))
(define (null?o x) (== x '()))
(define (pair?o x)
  (exist (a b)
    (conso a b x)))
(define (appendo a b x)
  (matcho a
    ['() (== x b)]
    [(h . t)
     (exist (y)
       (conso h y x)
       (appendo t b y))]))

(define-syntax solve*
  (syntax-rules ()
    [(_ (f args ...))
     (expand (args ...)
        (map (λ (env) (inst* (split args ...) env))
             (pull* ((f (disunquote args) ...) '(() . ())))))]))

(define-syntax solve
  (syntax-rules ()
    [(_ n (f args ...))
     (expand (args ...)
        (map (λ (env) (inst* (split args ...) env))
             (pulln n ((f (disunquote args) ...) '(() . ())))))]))

(define-syntax (expand expr)
  (syntax-parse expr
    [(_ () expr) #'expr]
    [(_ (v:id vs ...) expr)
     #'(let ((v (var v)))
       (expand (vs ...) expr))]
    [(_ (_ vs ...) expr) #'(expand (vs ...) expr)]))

(define-syntax (split expr)
  (syntax-parse expr
    [(_) #''()]
    [(_ v:id vs ...)
     #'(cons v (split vs ...))]
    [(_ _ vs ...) #'(split vs ...)]))

(define-syntax disunquote
  (syntax-rules (unquote)
    [(_ ()) '()]
    [(_ (unquote v)) v]
    [(_ v) v]))

(define-syntax-rule (parseo v p t ...) (parseo-aux (link v) p t ...))

(define-syntax link
  (syntax-rules ()
    [(_ (v . g)) (cons (link v) (link g))]
    [(_ ()) '()]
    [(_ v) v]))

(define-syntax (parseo-aux expr)
  (define-syntax-class ellipsis
    #:description "ellipsis"
    #:literals (...)
    (pattern ...))
  (define-syntax-class wildcard
    #:description "wildcard"
    #:literals (_)
    (pattern _))
  (syntax-parse expr 
    #:literals (quote unquote)
    [(_ v () t ...) #'(ando (== v '()) t ...)]
    [(_ v (unquote var) t ...) #'(ando (== v var) t ...)]
    [(_ v (quote lit) t ...) #'(ando (== v (quote lit)) t ...)]
    [(_ v (l e:ellipsis . r) t ...); split list with appendo
     #'(exist (vl vr)
         (appendo vl vr v)
         (parseo-aux vl l
             (parseo-aux vr r t ...)))]
    [(_ v (l . r) t ...); split pair
     #'(exist (vl vr)
         (== v `(,vl . ,vr))
         (parseo-aux vl l (parseo-aux vr r t ...)))]
    [(_ v _:wildcard t ts ...) #'(ando t ts ...)]; wildcard , match evetything
    [(_ v var:id t ...) #'(exist (var x) (== v var) t ...)]))

(define-syntax matcho
  (syntax-rules ()
    [(_ v [p t ...]) (lazy (parseo v p t ...))]
    [(_ v [p t ...] g ...)
     (disj (lazy (parseo v p t ...))
           (matcho v g ...))]))

(provide == =/= exist ando oro condo var
         solve* solve parseo matcho
         conso caro cdro null?o pair?o appendo)