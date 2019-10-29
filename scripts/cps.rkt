#lang racket

(define (M expr)
  (match expr
    [`(lambda (,var) ,expr)
     (define $k (gensym '$k))
     `(lambda (,var ,$k) ,(T expr $k))]
    [(? symbol?) expr]
    [(? number?) expr]))

(define (T expr cont)
  (match expr
    [`(lambda . ,_) `(,cont ,(M expr))]
    [(? symbol?) `(,cont ,(M expr))]
    [(? number?) `(,cont ,(M expr))] 
    [`(,f ,e)
     (define $f (gensym '$f))
     (define $e (gensym '$e))
     (T f `(lambda (,$f)
             ,(T e `(lambda (,$e)
                      (,$f ,$e ,cont)))))]))

(define (T-k expr k)
  (match expr
    [`(lambda . ,_)      (k (M expr))]
    [ (? symbol?)   (k (M expr))]
    [ (? number?)   (k (M expr))]
    [`(,f ,e)    
      ; =>
      (define $rv (gensym '$rv))
      (define cont `(lambda (,$rv) ,(k $rv)))
      (T-k f (lambda ($f)
             (T-k e (lambda ($e)
                      `(,$f ,$e ,cont)))))]))

(define (T-c expr c)
  (match expr
    [`(lambda . ,_)     `(,c ,(M expr))]
    [ (? symbol?)  `(,c ,(M expr))]
    [ (? number?)  `(,c ,(M expr))]
    [`(,f ,e)    
      ; =>
      (T-k f (lambda ($f)
               (T-k e (lambda ($e)
                        `(,$f ,$e ,c)))))]))
     
(define (M2 expr)
  (match expr
    [`(lambda (,var) ,expr)
      ; =>
      (define $k (gensym '$k))
     `(lambda (,var ,$k) ,(T-c expr $k))]
    
    [(? symbol?)  #;=>  expr]
    [(? number?)  #;=>  expr]))

(define foo
  '(lambda (y)
     (magic y)))

(define foo2
  (M foo))

(define foo3
  (M2 foo))

;; connect = bind new (\v -> thenn (write v loggedOut) (pure v))
(define connect
  '(lambda (_)
     ((bind new)
      (lambda (v)
        ((thenn ((write v) loggedOut))
         (pure v))))))

(define connect2
  (M connect))

(define connect3
  (M2 connect))

