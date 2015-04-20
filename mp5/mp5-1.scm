#lang eopl
;(require eopl)
(require trace/calltrace-lib)

(define (reduce fn init list)
  (if (null? list) init
      (fn (car list)
          (reduce fn init (cdr list) ))))


;=================================Spec&Grammar=====================================

;;scanner
;;referred from textbook Appendix B
(define spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)
    (arith-op ((or (or "-" "+") (or "*" "/"))) symbol)
    (compare-op ((or ">" "<")) symbol)
    ))

(define parse-op
  (lambda (op)
    (cond
      ((equal? op '+) +)
      ((equal? op '>) >)
      ((equal? op '<) <)
      ((equal? op '=) =)
      ((equal? op '-) -)
      ((equal? op '*) *)
      ((equal? op '/) /))))
      
;;parser
;;referred from textbook Appdendix B
(define grammar
  '((expression (number) num-exp)
    (expression (arith-op "(" expression (arbno "," expression) ")")arith-exp)
    (expression (compare-op "(" expression "," expression ")") compare-exp)
    (expression ("=""(" expression "," expression ")") compare-equ-exp)
    (expression ("proc""(" (arbno identifier) ")" expression "end") proc-exp)
    (expression ("(set" expression expression ")") set-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    (expression (obj-exp (arbno "."identifier)) object)
    (obj-exp ("begin" expression (arbno expression ";") "end")begin-exp)
    (obj-exp ("if" expression "then" expression "else" expression "end")if-exp)
    (obj-exp ("let" (arbno identifier "=" expression) "in" expression "end") let-exp) 
    (obj-exp ("letrec" (arbno identifier "=" expression) "in" expression "end") letrec-exp)
    (obj-exp ( "(" expression (arbno expression) ")") exp-exp)
    (obj-exp (identifier) var-exp)
    (obj-exp ("self") self-exp)
    (obj-exp ("super") super-exp)
    (obj-exp ("EmptyObj") empty-exp)
    (obj-exp ("extend" expression "with" (arbno MemberDecl)) extend-exp)
    (MemberDecl("public" identifier "=" expression ";") public-member)
    (MemberDecl("protected" identifier "=" expression";") protected-member)
    ))

;;sllgen from textbook appendix B
(sllgen:make-define-datatypes spec grammar)
(define scan&parse
  (sllgen:make-string-parser spec grammar))
;==============================Data Structure=======================================
(define empty-env
  (lambda () '()))
 
(define extend-env
  (lambda (key value env)
      (cond ((null? env) (list (list key value)))
            ((equal? (caar env) key) (append (list (list key value)) (cdr env)))
            (else (append (list (car env)) (extend-env key value (cdr env) ))))))

(define apply-helper
  (lambda (env key)
    (cond ((null? env) 'undefined)
          ((equal? key (caar env)) (cadar env))
          (else (apply-helper (cdr env) key)))))
 
(define apply-env
  (lambda (key env)
  (apply-helper env key)))


(define emptyObject
  (lambda ()
    (list (empty-env) '())))

(define subClass
  (lambda (super)
    (list (empty-env) super)))

;==============================Value-of Functions===================================
(define value-of
  (lambda (exp  env)
    (cond
      [(obj-exp? exp)
       (cases obj-exp exp
         (letrec-exp(id-list exp-list body)
                  (value-of body (add-env e)
         
       ]
      [(expression? exp)
       (cases expression exp
         (arith-exp (op exp exp-list)
            (let ([arglist (append (list exp) exp-list)])
              (reduce (parse-op op) (value-of exp env) (map (lambda (x) (value-of x env)) exp-list))))
         (compare-exp (op exp1 exp2)
                      ((parse-op op) (value-of exp1 env) (value-of exp2 env)))
         (num-exp (num) num)
         (true-exp() #t)
         (false-exp() #f)
         (else 'undefined))
         ]
      [(MemberDecl? exp)  ])))

(define add-env
  (lambda (id-list exp-list env)
    (if (or (null? var-list) (null? exp1-list))
        env
        ((extend-tenv (car var-list) newtype env)
          (add-env (cdr var-list) (cdr exp1-list) (extend-tenv (car var-list) newtype env) subst))))))



;===============================Object-interpreter===================================
(define object-interpreter
  (lambda (exp)
    (value-of (scan&parse exp) (empty-env))))


(trace object-interpreter)

(object-interpreter"<(1,2)")
