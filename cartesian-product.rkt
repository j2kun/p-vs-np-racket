#lang racket

(provide cartesian-product)

(require plai)
(print-only-errors)

(define (cartesian-product* next-list so-far)
  (foldl append '() 
         (map (λ (elt) 
                (map (λ (x) (cons elt x)) so-far)) 
              next-list)))

(test (cartesian-product* '(a) '((b c))) '((a b c)))
(test (cartesian-product* '(a e) '((g h) (g i))) '((e g h) (e g i) (a g h) (a g i)))

(define (cartesian-product lists)
  (foldl cartesian-product* '(()) lists))

(test (cartesian-product '()) '(()))
(test (cartesian-product '((a) (b))) '((b a)))
(test (cartesian-product '((1 2 3))) '((3) (2) (1)))
(test (cartesian-product '((1 2 3) (4 5 6) (7 8 9))) '((9 6 3) (9 6 2) (9 6 1) (9 5 3) (9 5 2) (9 5 1) (9 4 3) (9 4 2) (9 4 1)
                                                       (8 6 3) (8 6 2) (8 6 1) (8 5 3) (8 5 2) (8 5 1) (8 4 3) (8 4 2) (8 4 1)
                                                       (7 6 3) (7 6 2) (7 6 1) (7 5 3) (7 5 2) (7 5 1) (7 4 3) (7 4 2) (7 4 1)))