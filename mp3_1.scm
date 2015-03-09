#lang eopl
(require trace/calltrace-lib)
;=================================Spec&Grammar=====================================
(define q1-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)
    (arith-op ((or "+" "-" "*" "/")) symbol)
    (compare-op ((or ">" "<" "=")) symbol)
    ))

(define q1-grammar
  '((expression (number) num-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp) 
    (expression ("letrec" (arbno identifier "=" expression) "in" expression) letrec-exp)
    (expression ("proc" "(" (arbno identifier) ")" expression) proc-exp)
    (expression ( "(" expression (arbno expression) ")") exp-exp)
    (expression ("newref" "(" expression ")") newRef-exp)
    (expression ("set" identifier expression)set-exp)
    (expression ("begin" expression (arbno ";" expression) "end")begin-exp)
    (expression ("if" expression "then" expression "else" expression)if-exp)
    (expression (arith-op "(" expression (arbno "," expression) ")")arith-exp)
    (expression (compare-op "(" expression "," expression ")") compare-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    (expression ("undefined") undefined-exp)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes q1-spec q1-grammar)

(define scan&parse
  (sllgen:make-string-parser q1-spec q1-grammar))

;=================================Interpreter=====================================
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?))
  (ref-val
   (ref reference?)))

(define-datatype proc proc?
    (procedure
      (bvar symbol?)
      (body expression?)
      (env environment?)))
  
(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar symbol?)
   (bval expval?)
   (next-env environment?))
  (extend-env-rec*
   (proc-names (list-of symbol?))
   (b-vars (list-of symbol?))
   (proc-bodies (list-of expression?))
   (next-env environment?)))

(define apply-env
  (lambda (search-sym env)
    (cases environment env
      (empty-env ()
                 (eopl:error 'apply-env "No binding for ~s" search-sym))
      (extend-env (bvar bval next-env)
                  (if (eqv? search-sym bvar)
                      bval
                      (apply-env next-env search-sym)))
      (extend-env-rec* (p-names b-vars p-bodies next-env)
                       (cond 
                         ((location search-sym p-names)
                          => (lambda (n)
                               (proc-val
                                (procedure 
                                 (list-ref b-vars n)
                                 (list-ref p-bodies n)
                                 env))))
                         (else (apply-env next-env search-sym)))))))

(define location
    (lambda (sym syms)
      (cond
        ((null? syms) #f)
        ((eqv? sym (car syms)) 0)
        ((location sym (cdr syms))
         => (lambda (n) 
              (+ n 1)))
        (else #f))))


;======================Allocate stack in the-store=======================
(define the-store 'uninitialized)

  ;; empty-store : () -> Sto
  ;; Page: 111
  (define empty-store
    (lambda () '()))
  
  ;; initialize-store! : () -> Sto
  ;; usage: (initialize-store!) sets the-store to the empty-store
  ;; Page 111
  (define initialize-store!
    (lambda ()
      (set! the-store (empty-store))))

  ;; get-store : () -> Sto
  ;; Page: 111
  ;; This is obsolete.  Replaced by get-store-as-list below
  (define get-store
    (lambda () the-store))

  ;; reference? : SchemeVal -> Bool
  ;; Page: 111
  (define reference?
    (lambda (v)
      (integer? v)))

  ;; newref : ExpVal -> Ref
  ;; Page: 111
  (define newref
    (lambda (val)
      (let ((next-ref (length the-store)))
        (set! the-store
              (append the-store (list val)))                     
        next-ref)))                     

  ;; deref : Ref -> ExpVal
  ;; Page 111
  (define deref 
    (lambda (ref)
      (list-ref the-store ref)))

  ;; setref! : Ref * ExpVal -> Unspecified
  ;; Page: 112
  (define setref!                       
    (lambda (ref val)
      (set! the-store
        (letrec
          ((setref-inner
             ;; returns a list like store1, except that position ref1
             ;; contains val. 
             (lambda (store1 ref1)
               (cond
                 ((null? store1)
                  (report-invalid-reference ref the-store))
                 ((zero? ref1)
                  (cons val (cdr store1)))
                 (else
                   (cons
                     (car store1)
                     (setref-inner
                       (cdr store1) (- ref1 1))))))))
          (setref-inner the-store ref)))))

(define report-invalid-reference
    (lambda (ref the-store)
      (eopl:error 'setref
        "illegal reference ~s in store ~s"
        ref the-store)))

  ;; get-store-as-list : () -> Listof(List(Ref,Expval))
  ;; Exports the current state of the store as a scheme list.
  ;; (get-store-as-list '(foo bar baz)) = ((0 foo)(1 bar) (2 baz))
  ;;   where foo, bar, and baz are expvals.
  ;; If the store were represented in a different way, this would be
  ;; replaced by something cleverer.
  ;; Replaces get-store (p. 111)
   (define get-store-as-list
     (lambda ()
       (letrec
         ((inner-loop
            ;; convert sto to list as if its car was location n
            (lambda (sto n)
              (if (null? sto)
                '()
                (cons
                  (list n (car sto))
                  (inner-loop (cdr sto) (+ n 1)))))))
         (inner-loop the-store 0))))


;=====================================Value-of========================================
(define value-of
  (lambda (exp env)
    (cond
      [(number? exp) exp]
      [(expression? exp)
       (cases expression exp
         (num-exp (number) number)
         (var-exp (var) (apply-env var env))
         (let-exp (var-list exp1-list exp2) (value-of-let var-list exp1-list exp2 env))
         (letrec-exp (var-list exp1-list body)(value-of-letrec) )
         (arith-exp(arith-op exp1 exp2) (value-of-arith-exp arith-op exp1 exp2 env))
         
         (set-exp (var value) (value-of-set var value env))
         (newRef-exp (exp) (ref-val (newref exp)))
         (begin-exp (exp1 exp2-list) (value-of-begin exp1 exp2-list env))
         (else exp))]
      [(expval? exp)
       (cases expval exp
         (num-val(value) value)
         (bool-val(bool) bool)
         (proc-val(proc) proc)
         (ref-val(ref) (deref ref)))])))

(define value-of-letrec
  (lambda(p-names b-vars p-bodies letrec-body env)
    (value-of letrec-body
              (extend-env-rec* p-names b-vars p-bodies env))))


(define value-of-set
  (lambda (var value env)
    (cases expval (apply-env var env)
      (ref-val(ref)(setref! ref (value-of value env)))
      (else (eopl:error"Invalid set")))))

(define value-of-arith-exp
  (lambda (arith-op exp1 exp2-list env)
    (if (null? exp2-list)
        (value-of exp1 env)
        (cond
          [(equal? arith-op '+) (value-of-arith-exp arith-op (num-exp (+ (value-of exp1 env) (value-of (car exp2-list) env))) (cdr exp2-list) env)]
          [(equal? arith-op '-) (value-of-arith-exp arith-op (num-exp (- (value-of exp1 env) (value-of (car exp2-list) env))) (cdr exp2-list) env)]
          [(equal? arith-op '*) (value-of-arith-exp arith-op (num-exp (* (value-of exp1 env) (value-of (car exp2-list) env))) (cdr exp2-list) env)]
          [(equal? arith-op '/) (value-of-arith-exp arith-op (num-exp (/ (value-of exp1 env) (value-of (car exp2-list) env))) (cdr exp2-list) env)]
          [else display "no match"]))))

(define value-of-let
  (lambda (var-list exp1-list exp2 env)
     (value-of exp2 (add-env var-list exp1-list env))))

(define value-of-begin
  (lambda (exp1 exps env)
    (letrec
        ((value-of-begins
          (lambda (e1 es)
            (let ((v1 (value-of e1 env)))
              (if (null? es)
                  v1
                  (value-of-begins (car es) (cdr es)))))))
      (value-of-begins exp1 exps))))

(define add-env
  (lambda (var-list exp1-list env)
    (if (null? (cdr var-list))
        (extend-env (car var-list) (value-of (car exp1-list) env) env)
        (extend-env (car var-list) (value-of (car exp1-list) env) (add-env (cdr var-list) (cdr exp1-list) env)))))



;==============================Wrap Func=================================
(define static-interpreter
  (lambda (exp)
    (initialize-store!)
    (value-of (value-of (scan&parse exp) (empty-env)) (empty-env))))


;=====================================Test========================================
(trace static-interpreter)
(trace value-of)
(trace value-of-let)
(trace value-of-arith-exp)
(trace value-of-begin)
(trace newref)
(trace setref!)
(trace add-env)
(trace scan&parse)
(trace value-of-set)
;(trace the-store)
;(display (scan&parse ">(3,+(1,2))"))
;(display (scan&parse "let x = 1 in let f = proc (y) +(x, y) in let x = 2 in (f 5)"))
;(display (scan&parse "let x = 1 in let f = proc (y) +(x, y) in let x = 2 in (f 5)"))
;(display (scan&parse "letrec ill = proc (x) (ill x) in let f = proc (y) 5 in (f (ill 2))"))

(static-interpreter "let x = newref(1) in begin set x 2;x end")
;(static-interpreter "let x = 5 y = 3 in begin +(x,y) end")
