#lang racket

(require plai "cartesian-product.rkt")
(print-only-errors)

(define-type formula
  [var (name symbol?)]
  [¬ (body formula?)]
  [∨ (disjuncts (listof formula?))]
  [∧ (conjuncts (listof formula?))])

;; distribute¬: formula -> formula
;; distribute negations across all other logical constructs
(define (distribute¬ expr)
  (type-case formula expr
    [¬ (φ) (type-case formula φ
             [∨ (disjuncts) (∧ (map distribute¬ (map ¬ disjuncts)))]
             [∧ (conjuncts) (∨ (map distribute¬ (map ¬ conjuncts)))]
             [¬ (body) (distribute¬ body)] ; delete double negations
             [var (x) (¬ (var x))])]
    [∨ (disjuncts) (∨ (map distribute¬ disjuncts))]
    [∧ (conjuncts) (∧ (map distribute¬ conjuncts))]
    [else expr]))

;; compress ∧s of ∧s
(define (∧-compress f)
  (type-case formula f
    [∧ (conjuncts) (∧ (foldl append empty (map (λ (x) (∧-conjuncts x)) conjuncts)))]
    [else (error '∧-compress "not a ∧!")]))

(define (∨-compress f)
  (type-case formula f
    [∨ (disjuncts) (∨ (foldl append empty (map (λ (x) (∨-disjuncts x)) disjuncts)))]
    [else (error '∨-compress "not a ∨!")]))

(test (∧-compress (∧ (list (∧ (list (var 'x) (var 'x))) (∧ (list (var 'x) (var 'y)))))) (∧ (list (var 'x) (var 'y) (var 'x) (var 'x))))

;; do the ∨ part of CNF below
;; assume that cnf-conjuncts is a list of expressions in cunjunctive normal form
(define (regroup f cnf-conjuncts)
  (let* ([list-of-lists (map (λ (x) (∧-conjuncts x)) cnf-conjuncts)]
         [product (cartesian-product list-of-lists)])
    (map f product)))

;; conjunctive-normal-form: formula -> formula
;; convert a propositional formula to conjunctive normal form
;;  assume negations have been distributed
(define (conjunctive-normal-form φ)
  (type-case formula φ
    [∨ (disjuncts) (let* ([cnf-disjuncts (map conjunctive-normal-form disjuncts)]
                          [list-of-∨s (regroup ∨ cnf-disjuncts)]
                          [compressed-∨s (map ∨-compress list-of-∨s)])
                     (∧ compressed-∨s))]
    [∧ (conjuncts) (let ([inner-∧s (map conjunctive-normal-form conjuncts)])
                     (∧-compress (∧ inner-∧s)))]
    [else (∧ (list (∨ (list φ))))]))

(test (conjunctive-normal-form (∨ (list (var 'x) (¬ (var 'y))))) (∧ (list (∨ (list (var 'x) (¬ (var 'y)))))))
(test (conjunctive-normal-form (∨ (list (∧ (list (var 'x) (var 'y) (var 'z))) 
                                        (∧ (list (var 'a) (var 'b) (var 'c)))))) 
      (∧ (list (∨ (list (var 'x) (var 'a)))
               (∨ (list (var 'y) (var 'a)))
               (∨ (list (var 'z) (var 'a)))
               (∨ (list (var 'x) (var 'b)))
               (∨ (list (var 'y) (var 'b)))
               (∨ (list (var 'z) (var 'b)))
               (∨ (list (var 'x) (var 'c)))
               (∨ (list (var 'y) (var 'c)))
               (∨ (list (var 'z) (var 'c))))))

;; the type for an edge: we associate vertices with their formula labels, 
;; but we require distinct identifiers "i,j" for the i'th entry of the j'th column
(define-type a-vertex
  [vertex (label string?) (expr formula?)])

(define (label-column column col-index row-index)
  (if (empty? column) empty
      (cons (vertex (string-append (number->string col-index) "," (number->string row-index)) ;; the vertex identifier
                      (first column)) 
            (label-column (rest column) col-index (+ 1 row-index)))))

(define (label-graph columns col-index)
  (if (empty? columns) empty 
      (cons (label-column (first columns) col-index 1) 
            (label-graph (rest columns) (+ 1 col-index)))))

(test (label-graph (list (list (var 'x) (var 'y)) (list (var 'z) (var 'w))) 1) 
      (list (list (vertex "1,1" (var 'x)) (vertex "1,2" (var 'y))) 
            (list (vertex "2,1" (var 'z)) (vertex "2,2" (var 'w)))))

;; atom-info formula -> (symbol boolean)
(define (atom-info expr)
  (type-case formula expr
             [var (name) (list name #f)]
             [¬ (body) (list (var-name body) #t)] ;; body is guaranteed to be an atom by CNF
             [else (error "not a propositional atom!")])) 

(define (xnor a b) (or (and a b) (and (not a) (not b))))
(define (no-conflict? edge-pair)
  (let ([left-vertex (atom-info (vertex-expr (first edge-pair)))]
        [right-vertex (atom-info (vertex-expr (second edge-pair)))])
    (if (equal? (first left-vertex) (first right-vertex))
        (xnor (second left-vertex) (second right-vertex))
        #t)))

(define (all-pairs-in-distinct-lists lists)
  (if (equal? 1 (length lists)) empty
      (append (foldr append empty (map (λ (other-list) (cartesian-product (list other-list (first lists)))) (rest lists)))
              (all-pairs-in-distinct-lists (rest lists)))))

(test (all-pairs-in-distinct-lists '((1 2) (4 5) (7 8)))
      '((2 5) (2 4) (1 5) (1 4) (2 8) (2 7) (1 8) (1 7) (5 8) (5 7) (4 8) (4 7)))

;; n-sat-to-clique: formula -> (listof edge)
;; transform an input to n-sat to an input for clique
;; assume the input expression is in CNF, and that 
(define (n-sat-to-clique expr)
  (let* ([conjuncts (∧-conjuncts expr)]
         [columns (map (λ (x) (∨-disjuncts x)) conjuncts)]
         [labeled-columns (label-graph columns 1)]
         [possible-edges (all-pairs-in-distinct-lists labeled-columns)])
    (list->set (filter no-conflict? possible-edges))))

(test (n-sat-to-clique (∧ (list (∨ (list (var 'x) (var 'y)))
                                (∨ (list (¬ (var 'x)) (var 'y) (var 'z)))
                                (∨ (list (var 'x) (¬ (var 'z))))))) 
      (set
       (list (vertex "1,1" (var 'x)) (vertex "2,3" (var 'z)))
       (list (vertex "1,1" (var 'x)) (vertex "2,2" (var 'y)))
       (list (vertex "1,1" (var 'x)) (vertex "3,2" (¬ (var 'z))))
       (list (vertex "1,1" (var 'x)) (vertex "3,1" (var 'x)))
       (list (vertex "1,2" (var 'y)) (vertex "2,2" (var 'y)))
       (list (vertex "1,2" (var 'y)) (vertex "2,3" (var 'z)))
       (list (vertex "1,2" (var 'y)) (vertex "2,1" (¬ (var 'x))))
       (list (vertex "1,2" (var 'y)) (vertex "3,2" (¬ (var 'z))))
       (list (vertex "1,2" (var 'y)) (vertex "3,1" (var 'x)))
       (list (vertex "2,1" (¬ (var 'x))) (vertex "3,2" (¬ (var 'z))))
       (list (vertex "2,2" (var 'y)) (vertex "3,2" (¬ (var 'z))))
       (list (vertex "2,2" (var 'y)) (vertex "3,1" (var 'x)))
       (list (vertex "2,3" (var 'z)) (vertex "3,1" (var 'x)))))