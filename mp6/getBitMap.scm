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
(define index 0)
(define nameVector #())
(define friendshipVector #())
(define nameListLength 0)
(define stopNameTable (make-hash))
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
            (2-list (replicate 2 listLength))]
        (begin
          (fold-left bitwise-ior (map expt 2-list (map mapNames list)))))))) 

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
              (set! nameListLength (vector-length nameVector))
              (parseInput input)
              (display '-)
              (display (vector-length nameVector))
              (display '-)
              (display nameListLength)
              (set! friendshipVector (extraZeros (- (vector-length nameVector) nameListLength ) friendshipVector))))))

(define logarithm
  (lambda (val base) (/ (log val) (log base))))

(define bitmap-get-lsb-idx
  (lambda (bitmap)
    (inexact->exact (round (logarithm (bitwise-and bitmap (* -1 bitmap)) 2)))))

(define bitmap-idx-set?
  (lambda (bitmap idx)
    (let ([val (bitwise-and (expt 2 idx) bitmap)])
      (cond ((equal? val 0) #f)
            (else #t)))))

(define bitmap-clear-bit
  (lambda (idx bitmap)
    (cond ((bitmap-idx-set? bitmap idx) 
            (let ([mask (bitwise-not (expt 2 idx))])
              (bitwise-and mask bitmap)))
          (else bitmap))))

(define bitmap-set-idx-iterator
  (lambda (bitmap)
    (cond ((= 0 bitmap) '())
          (else (let* ([lsb (bitmap-get-lsb-idx bitmap)]
                       [new-bitmap (bitmap-clear-bit lsb bitmap)])
                  (list lsb new-bitmap))))))

(define bitmap-get-set-indices
  (lambda (bitmap aggregator)
    (cond ((= 0 bitmap) aggregator)
          (else (let* ([idx (bitmap-get-lsb-idx bitmap)]
                       [new-bmp (bitmap-clear-bit idx bitmap)])
                  (bitmap-get-set-indices new-bmp (append (list idx) aggregator)))))))

(define extraZeros
  (lambda (number list)
    (if (equal? number 0)
        list
        (extraZeros (- number 1) (vector-append list (vector 0))))))

(define fold-right
  (lambda (func init arg-list)
    (cond ((null? arg-list) init)
          (else (fold-right func (func init (car arg-list)) (cdr arg-list))))))

(define bitmap-list-combine
  (lambda (init-bmp bmp-list)
    (fold-right bitwise-ior init-bmp bmp-list)))

(define traverse-bitmap
  (lambda (curr-traversing-bitmap depth-remaining aggregator bitmap-vector)
    (cond ((equal? depth-remaining 0) (bitwise-ior aggregator curr-traversing-bitmap))
          ((equal? aggregator (- (expt 2 (+ 1 (vector-length nameVector))) 1)) aggregator)
          ((equal? curr-traversing-bitmap 0) (bitwise-ior aggregator curr-traversing-bitmap)) ; Assumes default bitmap is zero
          (else (let* ([rec-indices (bitmap-get-set-indices curr-traversing-bitmap '())] ; Certainly valid since bitmap != 0
                       [index-to-bitmap (lambda (idx) (vector-ref bitmap-vector idx))] ;; which var
                       [rec-bitmaps (map index-to-bitmap rec-indices)]
                       [next-depth-traverse (lambda (child-bmp) (traverse-bitmap child-bmp (- depth-remaining 1) aggregator bitmap-vector))]
                       [recursion-bitmaps (map next-depth-traverse rec-bitmaps)]
                       [combined-rec-bmps (bitmap-list-combine aggregator recursion-bitmaps)])
                  (bitwise-ior curr-traversing-bitmap combined-rec-bmps))))))

(define empty-bitmap 0)

(define traverse-friends
  (lambda (name depth)
    (let* ([user-id (hash-ref nameTable name '())])
      (cond ((null? user-id) (empty-bitmap))
            (else (let ([id-bitmap (vector-ref friendshipVector user-id)])
                  (traverse-bitmap id-bitmap (- depth 1) id-bitmap friendshipVector)))))))

(define add-name-to-bmp
  (lambda (bmp name)
    (let ([name-id (hash-ref nameTable name '())])
      (cond ((null? name-id) bmp)
            (else (bitmap-set-bit bmp name-id))))))
     
(define create-blacklist
  (lambda (name-list)
    (fold-right add-name-to-bmp 0 name-list)))

(define bitmap-set-bit
  (lambda (idx bitmap)
    (bitwise-ior bitmap (expt 2 idx))))

(define mutual-friends
  (lambda (name1 name2 depth)
    (let* ([bmp1 (traverse-friends name1 depth)]
           [bmp2 (traverse-friends name2 depth)]
           [id1 (hash-ref nameTable name1)]
           [id2 (hash-ref nameTable name2)]
           [mutual (bitwise-and bmp1 bmp2)]
           [minus1 (bitmap-clear-bit id1 mutual)]
           [minus2 (bitmap-clear-bit id2 minus1)])
      minus2)))

(define bmp-to-namelist
  (lambda (bmp)
    (let* ([indices (bitmap-get-set-indices bmp '())]
           [names (map (lambda (idx) (vector-ref nameVector idx)) indices)])
      names)))
       
;(readFile "doc-example")
;(print nameVector)
;(print friendshipVector)
;(bmp-to-namelist (traverse-friends 'Sihan 3))
(readFile "test.txt")
;(print nameVector)
;(print friendshipVector)
;(bmp-to-namelist (mutual-friends 'Minas 'Sihan 1))
(bmp-to-namelist (mutual-friends 'Name556 'Name1117 8))
;
