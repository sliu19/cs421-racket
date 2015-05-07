; Written by Minas Charalambides
; for CS421 Spring 2015, MP6.

#lang racket

; How many names.
(define name-count 500)

; How many friends per person.
(define connectivity 10)

; Returns a new list which is a copy of lst
; but with the elements at positions i and j
; swapped.
(define (swap lst i j)
  (if (= i j)
    lst
    (let ([a (list-ref lst i)]
          [b (list-ref lst j)])
       (let loop ([index 0]
                 [acc '()]
                 [lst lst])
         (cond 
           [(= index i)
              (loop (add1 index) (append acc (list b)) (cdr lst))]
           [(= index j)
              (append acc (list a) (cdr lst))]
           [(null? lst)
             acc]
           [else (loop (add1 index) (append acc (list (car lst))) (cdr lst))])))))

; Returns a random number in the interval [i, j)
(define (random-in-interval i j)
  (+ i (random (- j i))))

; Returns a random permutation of the list lst
; up till the index n.
(define (random-permutation lst [n (length lst)])
  (let loop ([i 0]
             [lst lst])
    (if (= i n)
      lst
      (loop (add1 i) (swap lst i (random-in-interval i (length lst)))))))

; Generates a list containing the numbers from i to j inclusive.
(define (genlist i j)
  (let loop ([j j]
             [acc '()])
    (if (= i j)
      (cons i acc)
      (loop (sub1 j) (cons j acc)))))

; A list containing Name0 ... NameX where X = name-count.
(define people (map string-append (make-list name-count "Name")
                                  (map number->string (genlist 1 name-count))))

; Formats the elements of the list as a string that fits the assumed file format.
(define (format-for-printing lst)
  (let loop ([lst lst]
             [acc ""])
    (if (null? lst)
      acc
      (loop (cdr lst) (string-append acc (car lst) " ")))))

; Generate all lines in the file.
(for ([i name-count])
  (define current (list-ref people i))
  (define lst (random-permutation people connectivity))
  (printf  "~a : ~a ;~n" current (format-for-printing (remove current (take lst connectivity)))))

