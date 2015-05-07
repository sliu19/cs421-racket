#lang racket
(require eopl)
(require trace/calltrace-lib)


(define spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    ))


(define grammar
  '((Friend (identifier ":" (arbno identifier) ";") friendship)
    ))


;;sllgen from textbook appendix B
(sllgen:make-define-datatypes spec grammar)
(define scan&parse
  (sllgen:make-string-parser spec grammar))

(define nameTable (make-hash))
(define index 1)
(define nameVector #())
(define friendshipVector #())
(define getNewIndex 
  (lambda ()
    (begin
      (set! index (+ index 1))
      (- index 1))))

(define the-data 'uninitialized)

(define set-data
  (lambda(new-data)
    (set! the-data new-data)))

(define get-data
  (lambda () the-data))

(define new-name-struct
  (lambda () '()))

(define replicate
  (lambda (element n)
    (cond
      ((zero? n)
        '())
      (else
        (cons element (replicate element (- n 1)))))))

(define fold-left
  (lambda (function the-list)
    (cond
      ((eqv? (length the-list) 1)
        (function (car the-list)))
      ((eqv? (length the-list) 2)
        (function (car the-list) (cadr the-list)))
      (else
        (let ([lhs (car the-list)]
              [rhs (cadr the-list)])
          (fold-left function (cons (function lhs rhs) (cddr the-list))))))))

(define mapNames
  (lambda (Newname)
    (if (equal? "not here" (hash-ref nameTable Newname "not here"))
        (begin
          (let [(newIndex (getNewIndex))]
            (hash-set! nameTable Newname newIndex)
            (set! nameVector (vector-append nameVector (vector Newname)))
            newIndex))
        (hash-ref nameTable Newname))))

(define name-struct-insert
  (lambda (person-name friends-list name-struct)
      (cons (list person-name friends-list) name-struct)))

(define friendship->owner
  (lambda (friend)
    (cases Friend friend
      (friendship (owner list) owner))))

(define friendship->friendList
  (lambda (friend)
    (cases Friend friend
      (friendship (owner list) list))))


(define friendlist->bitMap
  (lambda (list)
    (begin
      (let* [(listLength (length list))
            (emptylist (replicate 0 listLength))
            (2-list (replicate 2 listLength))
            (tableList (replicate nameTable listLength))]
        (begin
          (fold-left bitwise-ior (map expt 2-list (map hash-ref tableList list)))))))) 


;;get friendList bitMap Vector
(define parseInput
  (lambda (listsOfStrings)
    (let* [(friendlist (friendship->friendList (scan&parse (car listsOfStrings))))
          (num (friendlist->bitMap friendlist))]
      (if(null? (cdr listsOfStrings))
       (set! friendshipVector (vector-append friendshipVector (vector num)))   
       (begin
         (set! friendshipVector (vector-append friendshipVector (vector num)))
         (parseInput  (cdr listsOfStrings)))))))


;;Get owners index  
(define preparseInput  
  (lambda (listsOfStrings)
    (let [(friend (scan&parse (car listsOfStrings)))]
      (if (null? (cdr listsOfStrings))
          (mapNames (friendship->owner friend))
          (begin
            (mapNames (friendship->owner friend))
            (preparseInput (cdr listsOfStrings)))))))


(define readFile
 (lambda (path)
          (let [(input(file->lines path))]
            
            (begin
              (preparseInput input)
              (parseInput input)))))

(trace friendlist->bitMap)
(trace parseInput)

(readFile "dataset.txt")
(print nameVector)
(print friendshipVector)