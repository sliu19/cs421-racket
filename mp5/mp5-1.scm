#lang eopl
;(require eopl)
(require trace/calltrace-lib)



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

;;parser
;;referred from textbook Appdendix B
(define grammar
  '((expression (arith-op "(" expression (arbno "," expression) ")")arith-exp)
    (expression (compare-op "(" expression "," expression ")") compare-exp)
    (expression ("=" "(" expression "," expression ")") compare-equ-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ("(set" expression expression ")") set-exp)
    (expression (number) num-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    (expression (obj-exp (arbno "."identifier) ) obj)
    (obj-exp ("begin" expression (arbno ";" expression) "end")begin-exp)
    (obj-exp ("if" expression "then" expression "else" expression)if-exp)
    (obj-exp ("let" (arbno identifier "=" expression) "in" expression) let-exp) 
    (obj-exp ("letrec" (arbno identifier "=" expression) "in" expression) letrec-exp)
    (obj-exp ( "(" expression (arbno expression) ")") exp-exp)
    (obj-exp(identifier) var-exp)
    (obj-exp("self") self-exp)
    (obj-exp("super") super-exp)
    (obj-exp("EmptyObj") empty-exp)
    (obj-exp("extend" expression "with" (arbno MemberDecl)) extend-exp)
    (MemberDecl("{public}" identifier "=" expression) public-mem)
    (MemberDecl("{protected}" identifier "=" expression) protected-mem)
    ))

;;sllgen from textbook appendix B
(sllgen:make-define-datatypes spec grammar)
(define scan&parse
  (sllgen:make-string-parser spec grammar))


;===============================Object-interpreter===================================
(define object-interpreter
  (lambda (exp)
    (scan&parse exp)))