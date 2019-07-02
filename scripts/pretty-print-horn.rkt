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

(define (cubify constraints)
  ;; EHC -> (LinearEHC -> LinearEHC) -> List LinearEHC
  (define (cubify-help formula path-builder)
    (match formula
      [(list 'and conjuncts ...)
       (apply append (map (lambda (conjunct) (cubify-help conjunct path-builder)) conjuncts))]

      [(list 'forall head body)
       (cubify-help body (lambda (x) (path-builder (list 'forall head x))))]

      [(list 'exists head body)
       (cubify-help body (lambda (x) (path-builder (list 'exists head x))))]

      [formula (list (path-builder formula))]))

  (cubify-help constraints identity))

(define input-file (make-parameter #f))
(define hypercube (make-parameter #f))

(command-line
 #:program "pretty-print"
 #:once-each
 [("-i" "--input") file-name
                   "read input from file"
                   (input-file file-name)]
 [("--hypercube") "print the constraints as a hyper cube"
                  (hypercube #t)])


(current-input-port (if (input-file)
                        (open-input-file (input-file))
                        (current-input-port)))
(define constraints (read))

(displayln (pretty-print constraints))

(when (hypercube)
  (displayln "")
  (for-each displayln (cubify constraints)))
