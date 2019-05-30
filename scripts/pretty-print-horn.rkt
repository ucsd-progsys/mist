#lang racket

(define tabsize (make-parameter 2))

(define (indent depth)
  (make-string (* depth (tabsize)) #\space))

(define (add-newlines lines)
  (add-between lines "\n"))

(define (surround start end body)
  (append (list start) body (list end)))

(define (parens body)
  (surround "(" ")" body))

;; formula, depth -> list string
(define (pretty-print-depth formula depth)
  (list* (indent depth)
         (match formula
           [(list 'and conjuncts ...)
            (parens
             (list* "and"
                    "\n"
                    (flatten
                     (add-newlines
                      (map (lambda (x) (pretty-print-depth x (+ depth 1)))
                           conjuncts)))))]
           [(list 'forall head body)
            (parens
             (list* "forall"
                    " "
                    (~a head)
                    "\n"
                    (pretty-print-depth body (+ depth 1))))]
           [(list 'exists head body)
            (parens
             (list* "exists"
                    " "
                    (~a head)
                    "\n"
                    (pretty-print-depth body (+ depth 1))))]
           [formula
            (list (~a formula))])))

(define (pretty-print formula)
  (apply string-append (pretty-print-depth formula 0)))

(display (pretty-print (read)))