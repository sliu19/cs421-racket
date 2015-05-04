#lang racket

(require eopl)
(require racket/place)

(define-datatype message-type message-type?
  (query-msg
    (names (lambda (x)
             (and (pair? x) 
                  (string? (car x)) 
                  (string? (cdr x)))))
    (depth integer?)
    (id integer?)
    (reply-to (lambda (x)
                (or (thread? x) 
                    (place-channel? x)))))
  (filename-msg
    (filename string?))
  (response-msg
    (id integer?)
    (result (list-of string?))))

(provide message-type message-type? query-msg filename-msg response-msg)

