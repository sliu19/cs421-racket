#lang racket
(require eopl)
(require trace/calltrace-lib)
(require "message-type.scm")

;;scanner
;;referred from textbook Appendix B
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

(define the-data 'uninitialized)

(define set-data
  (lambda(new-data)
    (set! the-data new-data)))

(define get-data
  (lambda () the-data))

(define new-name-struct
  (lambda () '()))

(define addDateSet
  (lambda (input dataset)
    (cases Friend input
      (friendship(name friendList)
                 (name-struct-insert name friendList dataset)))))



(define (reduce fn init list)
  (if (null? list) init
      (fn (car list)
          (reduce fn init (cdr list) ))))
 

(define name-struct-insert
  (lambda (person-name friends-list name-struct)
      (cons (list person-name friends-list) name-struct)))
 
(define name-struct-search
  (lambda (name-struct name)
    (cond ((null? name-struct) '())
          (else 
           (let* ([curr-pair (car name-struct)]
                  [remaining (cdr name-struct)]
                  [pair-name (car curr-pair)]
                  [pair-friends (cadr curr-pair)])
             (cond ((equal? name pair-name) pair-friends)
                   (else (name-struct-search remaining name))))))))
 
(define aggregate-friends
  (lambda (name-struct friend-name depth)
    ;; get the friend list at current depth
    (let* ([friend-list (remove-duplicates (name-struct-search name-struct friend-name))])
      (cond ((equal? 1 depth) friend-list)
            (else (let* ([new-depth (- depth 1)]
                         [recursive-lambda (lambda (next-friend-name)
                                             (aggregate-friends name-struct next-friend-name new-depth))]
                         [list-of-friend-list (map recursive-lambda friend-list)]
                         [full-recursive-friend-list (reduce append '() list-of-friend-list)]
                         [all-depths-recursive-friends (append full-recursive-friend-list friend-list)]
                         [all-depth-remove-dup (remove-duplicates all-depths-recursive-friends)])
                    (remove-duplicates all-depth-remove-dup)))))))
 
(define common-friends
  (lambda (name-struct name1 name2 depth)
    (let ([friends1 (aggregate-friends name-struct name1 depth)]
          [friends2 (aggregate-friends name-struct name2 depth)])
      (begin
        (print name2)
      (intersect friends1 friends2 (list name1 name2))))))
 
(define order-by-length
  (lambda (l1 l2)
    (let ([len1 (length l1)]
          [len2 (length l2)])
      (cond ((> len1 len2) (list l2 l1))
            (else (list l1 l2))))))
 
(define list-contains
  (lambda (list elem)
    (if (equal? #f (member elem list))
        #f ; Not found = member returns false
        #t)))
 
(define intersect-helper
  (lambda (l1 l2 blacklist accumulator)
    (cond ((null? l1) accumulator)
          (else 
           (let* ([test-elem (car l1)]
                  [remaining (cdr l1)]
                  [new-acc (cons test-elem accumulator)])
             (cond ((list-contains blacklist test-elem) (intersect-helper remaining l2 blacklist accumulator))
                   ((list-contains l2 test-elem) (intersect-helper remaining l2 blacklist new-acc))
                   (else (intersect-helper remaining l2 blacklist accumulator))))))))
 
(define (intersect list1 list2 blacklist)
  (let* ([ordering (order-by-length list1 list2)]
         [shorter (car ordering)]
         [longer (cadr ordering)])
    (intersect-helper shorter longer blacklist '())))
 
(define parseInput
  (lambda (listsOfStrings dataset)
    (if(null? (cdr listsOfStrings))
       (addDateSet (scan&parse (car listsOfStrings)) dataset)    
       (parseInput  (cdr listsOfStrings) (addDateSet (scan&parse (car listsOfStrings)) dataset)))))

(define readFile
 (lambda (path)
          (let [(input(file->lines path))]
              (parseInput input (new-name-struct)))))

(define handle-query-message
  (lambda (names depth msg-id reply-to)
    (let* ([name-struct (get-data)]
           [name1 (string->symbol (car names))]
           [name2 (string->symbol (cdr names))]
           [result-list (common-friends name-struct name1 name2 depth)]
           [response (response-msg msg-id result-list)])
      (begin
        ;(display (aggregate-friends name-struct name1 depth))
        ;(display (aggregate-friends name-struct name2 depth))
        (thread-send reply-to response)))))
        ;(display result-list)))))

(define the-recipient (thread (lambda ()
                                   (let loop()
                                     (match(thread-receive)
                                       [(? message-type? message)
                                        (cases message-type message
                                          (query-msg(names depth id reply-to)
                                                    (handle-query-message names depth id reply-to))
                                          (filename-msg(path) 
                                                       (set-data (readFile path)))
                                          (else '5))
                                        (loop)])))))



(provide the-recipient)

(thread-send the-recipient(filename-msg "test.txt"))

(thread-send the-recipient (query-msg (cons "Name626" "Name2387") 1 0 (current-thread)))


;(thread-send the-recipient (query-msg (cons "Name2250" "Name2121") 13 1 (current-thread)))

;(thread-send the-recipient (query-msg (cons "Name111" "Name1533") 16 2 (current-thread)))

;(thread-send the-recipient (query-msg (cons "Name1364" "Name1533") 16 3 (current-thread)))

;(thread-send the-recipient (query-msg (cons "Name1364" "Name1533") 16 4 (current-thread)))

;(thread-send the-recipient (query-msg (cons "Name1364" "Name1533") 16 5 (current-thread)))

;(thread-send the-recipient (query-msg (cons "Name1364" "Name1533") 16 6 (current-thread)))

;(thread-send the-recipient (query-msg (cons "Name1364" "Name1533") 16 7 (current-thread)))

;(thread-send the-recipient (query-msg (cons "Name1364" "Name1533") 16 8 (current-thread)))

;(thread-send the-recipient (query-msg (cons "Name1364" "Name1533") 16 9 (current-thread)))