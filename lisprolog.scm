; current-continuation : -> continuation
(define (current-continuation) 
  (call-with-current-continuation 
   (lambda (cc)
     (cc cc))))

; fail-stack : list[continuation]
(define fail-stack '())

(define (fall)
  (if (not (pair? fail-stack))
      (display-newline "no more solution.")
      (let ((back-track-point (car fail-stack)))
        (set! fail-stack (cdr fail-stack))
        back-track-point)))

; fail : -> ...
(define (fail)
  (let ((fall-point (fall)))
    (fall-point fall-point)))

; amb : list[a] -> a
(define (amb choices)
  (let ((cc (current-continuation)))
    (cond
      ((null? choices) (fail))
      ((pair? choices) (let ((choice (car choices)))
                         (set! choices (cdr choices))
                         (set! fail-stack (cons cc fail-stack))
                         choice)))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (translate-syntax exp)
  (cond
    ((pair? exp)
     (cons (translate-syntax (car exp))
           (translate-syntax (cdr exp))))
    ((symbol? exp)
     (let ((str (symbol->string exp)))
       (if (string=? (substring str 0 1) "?")
           (list '?
                 (string->symbol
                  (substring str 1 (string-length str))))
           exp)))
    (else exp)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (instantiate partten env fail-handle)
  (let loop ((p partten))
    (cond
      ((var-lable? p)
       (let ((partten (lookup-var p env)))
         (if partten
             (loop partten)
             (fail-handle p))))
      ((pair? p)
       (cons (loop (car p))
             (loop (cdr p))))
      (else p))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define rules '())

(define (add-rule! rule)
  (set! rules
        (cons rule rules)))

(define (rule-exp rule)
  (car rule))

(define (rule-body rule)
  (if (null? (cdr rule))
      #f
      (caddr rule)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (lookup-var var-lable env)
  (let ((var-pair (assoc var-lable env)))
    (if var-pair
        (cdr var-pair)
        #f)))

(define (new-var var-lable var-value env)
  (cons (cons var-lable var-value) env))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (var-lable? p)
  (if (pair? p)
      (equal? (car p) '?)
      #f))

(define counter 0)

(define (new-partten exp)
  (set! counter (+ counter 1))
  (let loop ((p exp))
    (cond
      ((var-lable? p) (append p (list counter)))
      ((pair? p)
       (cons (loop (car p))
             (loop (cdr p))))
      (else p))))   
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (eval-and partten env)
  (cond
    ((null? partten)
      env)
    (else
      (eval-and
       (cdr partten)
       (eval-partten (car partten) env)))))

(define (eval-or partten env)
  (eval-partten (amb partten) env))

(define (eval-partten partten env)
  (if (pair? partten)
      (let ((operator (car partten)))
        (cond
          ((equal? operator 'and)
           (let ((ands (cdr partten)))
             (eval-and ands env)))
          ((equal? operator 'or)
           (let ((ors (cdr partten)))
             (eval-or ors env)))
          (else (apply-rules partten env))))
      (apply-rules partten env)))
     
(define (apply-rules partten env)
  (if (null? rules)
      (fail)
      (apply-a-rule partten (amb rules) env)))
   
(define (apply-a-rule partten rule env)
  (let* ((the-rule (new-partten rule))
         (enviroment (match partten
                      (rule-exp the-rule)
                      env))
         (body (rule-body rule)))
    (if body
        (eval-partten (rule-body the-rule) enviroment)
        enviroment)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (match partten-1 partten-2 env)
  (let ((partten-1 (try-instantiate partten-1 env))
        (partten-2 (try-instantiate partten-2 env)))
      (cond
        ((equal? partten-1 partten-2) env)
        ((var-lable? partten-1)
         (try-extend partten-1 partten-2 env))
        ((var-lable? partten-2)
         (try-extend partten-2 partten-1 env))
        ((and (pair? partten-1)
              (pair? partten-2))
         (match (cdr partten-1) (cdr partten-2)
           (match (car partten-1) (car partten-2) env)))
        (else (fail)))))

(define (try-instantiate partten env)
  (instantiate partten env (lambda (p) p)))
  
(define (try-extend var-lable partten env)
  (let ((var-value (lookup-var var-lable env)))
    (cond
      (var-value
       (match var partten env))
      ((var-lable? partten)
       (let ((var2-value (lookup-var partten env)))
         (if var2-value
             (try-extend var-lable var2-value env)
             (new-var var-lable partten env))))
      ((involve? partten var-lable env)
       (fail))
      (else (new-var var-lable partten env)))))

(define (involve? exp var-lable env)
  (define (loop e)
    (cond
      ((var-lable? e)
       (if (equal? e var-lable)
           #t
           (let ((b (lookup-var e env)))
             (if b
                 (loop b)
                 #f))))
      ((pair? e)
       (or (loop (car e))
           (loop (cdr e))))
      (else
       #f)))
  (loop exp))

(define scounter 0)

(define (next-symbol)
  (set! scounter (+ scounter 1))
  (string->symbol
   (string-append "_"
                  (number->string scounter))))

(define symbol-map '())

(define (map-symbol p)
  (let ((symbol (assq p symbol-map)))
    (if symbol
        (cdr symbol)
        (let ((new-symbol (next-symbol)))
          (set! symbol-map
                (cons (cons p new-symbol)
                      symbol-map))
          new-symbol))))

(define (rule p) (add-rule! (translate-syntax p)))

(define (query* p)
  (set! counter 0)
  (let ((partten (new-partten (translate-syntax p)))
         (result '()))
    (if (amb '(#t #f))
        (let ((enviroment (eval-partten partten
                                   '())))
          (set! scounter 0)
          (set! symbol-map '())
          (set! result (cons (instantiate partten
                               enviroment
                               map-symbol)
                             result))
          (fail))
        result)))

(rule '(((?a . ?b) append ?c form (?a . ?d))
        when (?b append ?c form ?d)))
(rule '((() append ?c form ?c)))

(rule '((() is subset of ?x )))
(rule '(((?a . ?t) is subset of ?x)
        when (and (?b append (?a . ?c) form ?x)
                  (?b append ?c form ?d)
                  (?t is subset of ?d))))

(query* '((a b c) append (d f) form ?x))
(newline)
(query* '(?a append ?b form (a b c)))
(newline)
(query* '(?x is subset of (a b c)))




