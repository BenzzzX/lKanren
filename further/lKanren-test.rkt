#lang racket
(require "lKanren.rkt")
;lKanren
(define (removeo a b x)
  (parseo a
    (h ... ,b t ...)
    (appendo h t x)))

(define (subseto x a)
  (matcho (x a)
    [((h ... m . t) (,m))]
    [((h ... m . t) (,m . g))
     (exist (y)
       (appendo h t y)
       (subseto y g))]))

(define (sublisto x a)
  (matcho (x a)
    [((_ ... h . _) (,h))]
    [((_ ... z . t) (,z . g)) (sublisto t g)]))

(define (csublisto x a)
  (parseo (x a) ((_ ... h t ... . _) (,h . ,t))))

(solve* (removeo '(1 2 3) x y))