#lang typed/racket

(define-type Label String)
(define-type Tag (U 'B 'Pair '->))
(define-type Head (U #f (List Label)))
(define-type Body (U (fail )))
(define-type Hypercoercion
  (U '* (List Head Body Tail)))