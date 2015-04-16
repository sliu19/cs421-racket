;;Teammate with swei7
#lang eopl
(require trace/calltrace-lib)
;=================================Spec&Grammar=====================================
(define q1-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)
    (arith-op ((or (or "-" "+") (or "*" "/"))) symbol)
    (compare-op ((or ">" "<")) symbol)
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
    (expression ("=" "(" expression "," expression ")") compare-equ-exp)
    (expression ("true") true-exp)
    (expression ("false") false-exp)
    (expression ("undefined") undefined-exp)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes q1-spec q1-grammar)

(define scan&parse
  (sllgen:make-string-parser q1-spec q1-grammar))

;=================================Interpreter=====================================
;;refered from slides&book
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?))
  (ref-val
   (ref reference?)))

;;refered from slides&book
(define-datatype proc proc?
  (procedure
   (bvar list?)
   (body expression?)
   (env environment?)))

(define-datatype environment environment?
  (empty-env)
  (extend-env 
   (bvar symbol?)
   (bval expval?)
   (next-env environment?))
  (extend-env-rec*
   (proc-names list?)
   (proc-vars list?)
   (proc-bodies list?)
   (next-env environment?)))

;;refered from slides&book
(define apply-env
  (lambda (search-sym env)
    (cases environment env
      (empty-env ()
                 (undefined-exp ))
      (extend-env (bvar bval next-env)
                  (if (eqv? search-sym bvar)
                      bval
                      (apply-env  search-sym next-env)))
      (extend-env-rec* (procedureNamelist procedureVarList procedureBodyList next-env)
                       (cond 
                         [(location search-sym procedureNamelist)
                          => (lambda (n)
                               (if(null?(list-ref procedureVarList n))
                                  (value-of (list-ref procedureBodyList n) next-env )
                                  (proc-val
                                   (procedure 
                                    (list-ref procedureVarList n)
                                    (list-ref procedureBodyList n)
                                    env))))]
                         (else (apply-env search-sym  next-env)))))))

;;refered from slides&book
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
    (undefined-exp)))

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
;;refered from book
(define expval->num
  (lambda (v)
    (if (expval? v)
        (cases expval v
          (num-val (num) num)
          (else (expval-extractor-error 'num v)))
        v)))

(define expval->bool
  (lambda (v)
    (if (expval? v)
        (cases expval v
          (bool-val (bool) bool)
          (else 0))
        v)))

;;refered from book
(define expval->proc
  (lambda (v)
    (if(expval? v)
       (cases expval v
         (proc-val (proc) proc)
         (else (expval-extractor-error 'proc v)))
       v)))

;;refered from book
(define expval->ref
  (lambda (v)
    (if (expval? v)
        (cases expval v
          (ref-val (ref) ref)
          (else (expval-extractor-error 'reference v)))
        v)))
;;refered from slides&book
(define expval-extractor-error
  (lambda (variant value)
    (undefined-exp)))

(define autoDerefIfNeed
  (lambda (exp)
    (cases expval exp
      (ref-val(ref) (deref ref))
      (else exp))))

;=====================================Value-of========================================
(define value-of
  (lambda (exp env state)
    (cond
      [(number? exp) exp]
      [(expression? exp)
       (cases expression exp
         (num-exp (number) (num-val number))
         (var-exp (var) (apply-env var env))
         (true-exp () (bool-val #t))
         (false-exp () (bool-val #f))
         (undefined-exp () exp)
         (let-exp (var-list exp1-list exp2) (value-of-let var-list exp1-list exp2 env state))
         (letrec-exp (var-list exp1-list body)(value-of-letrec var-list exp1-list body env state) )
         (proc-exp(var-list exp) (proc-val (procedure var-list exp env)))
         (exp-exp(rator rand-list) (value-of-exp rator rand-list env state))
         (newRef-exp (exp) (ref-val (newref (value-of exp env state ))))
         (set-exp (var value) (value-of-set var value env state))
         (begin-exp (exp1 exp2-list) (value-of-begin exp1 exp2-list env state))
         (if-exp(exp1 exp2 exp3) (value-of-if exp1 exp2 exp3 env state))
         (arith-exp(arith-op exp1 exp2) (value-of-arith-exp arith-op exp1 exp2 env state))
         (compare-exp(compare-op exp1 exp2) (value-of-compare-exp compare-op exp1 exp2 env state))
         (compare-equ-exp(exp1 exp2)(value-of-compare-exp '= exp1 exp2 env state))
         (else exp))]
      [(expval? exp)
       (cases expval exp
         (proc-val(pr) exp)
         (else exp))])))

(define value-of-proc
  (lambda (var body env state)
    (lambda (val)
      (value-of body 
                (extend-env var val env) state))))

(define value-of-letrec
  (lambda(functionNamesList exp-list body env state)
    (let ([recEnv (letrec-getEnvRec functionNamesList exp-list env state)]
          [extendEnv (letrec-getEnv functionNamesList exp-list env state)])
      (value-of body 
                (getRecEnv recEnv extendEnv) 1))))

(define getRecEnv
  (lambda (revEnv extendEnv)
    (cases environment revEnv
      (extend-env-rec* (exp1 exp2 exp3 oldEnv)
                       (extend-env-rec*
                        exp1 
                        exp2
                        exp3
                        extendEnv))
      (else extendEnv))))

(define letrec-getEnv
  (lambda (functionNamesList exp-list env state)
    (if(null? (cdr exp-list))
       (cases expression (car exp-list)
         (proc-exp(var-list exp) env)
         (else (extend-env (car functionNamesList) (value-of (car exp-list) env state) env)))
       (cases expression (car exp-list)
         (proc-exp(var-list exp) env)
         (else (letrec-getEnv (cdr functionNamesList) (cdr exp-list) (extend-env (car functionNamesList) (value-of (car exp-list) env state) env ) state))))))

(define letrec-getEnvRec
  (lambda (functionNamesList exp-list env state)
    (if(null? (cdr exp-list))
       (cases expression (car exp-list)
         (proc-exp(var-list exp) (extend-env-rec* functionNamesList (list var-list) exp-list env))
         (else env))
       (cases expression (car exp-list)
         (proc-exp(var-list exp) 
                  (let ([prevEnv (letrec-getEnvRec (cdr functionNamesList)(cdr exp-list) env state)])
                    (cases environment prevEnv
                      (extend-env-rec* (nameList varList bodyList env)
                                       (extend-env-rec*
                                        (append nameList (list (car functionNamesList)))
                                        (append varList (list var-list))
                                        (append bodyList (list (car exp-list)))
                                        env))
                      (else env))))
         (else  env)))))

(define value-of-set
  (lambda (var value env state)
    (cond
      [(expval?(apply-env var env))
       (cases expval (apply-env var env)
         (ref-val(ref)(setref! ref (value-of value env state)))
         (else '33))];;do nothing
      [else (undefined-exp)])))

(define value-of-arith-exp
  (lambda (arith-op exp1 exp2-list env state)
    (if (null? exp2-list)
        (value-of exp1 env state)
        (cond
          [(equal? arith-op '+) (value-of-arith-exp arith-op (num-exp (+ (expval->num (autoDerefIfNeed (value-of exp1 env state))) (expval->num (autoDerefIfNeed (value-of (car exp2-list) env state))))) (cdr exp2-list) env state)]
          [(equal? arith-op '-) (value-of-arith-exp arith-op (num-exp (- (expval->num (autoDerefIfNeed (value-of exp1 env state))) (expval->num (autoDerefIfNeed (value-of (car exp2-list) env state))))) (cdr exp2-list) env state)]
          [(equal? arith-op '*) (value-of-arith-exp arith-op (num-exp (* (expval->num (autoDerefIfNeed (value-of exp1 env state))) (expval->num (autoDerefIfNeed (value-of (car exp2-list) env state))))) (cdr exp2-list) env state)]
          [(equal? arith-op '/) (value-of-arith-exp arith-op (num-exp (/ (expval->num (autoDerefIfNeed (value-of exp1 env state))) (expval->num (autoDerefIfNeed (value-of (car exp2-list) env state))))) (cdr exp2-list) env state)]
          [else display "no match"]))))

(define value-of-compare-exp
  (lambda (compare-op exp1 exp2 env state)
    (cond
      [(equal? compare-op '<) (bool-val (< (expval->num (autoDerefIfNeed (value-of exp1 env state))) (expval->num (autoDerefIfNeed (value-of exp2 env state)))))]
      [(equal? compare-op '=) (bool-val (= (expval->num (autoDerefIfNeed (value-of exp1 env state))) (expval->num (autoDerefIfNeed (value-of exp2 env state)))))]
      [(equal? compare-op '>) (bool-val (> (expval->num (autoDerefIfNeed (value-of exp1 env state))) (expval->num (autoDerefIfNeed (value-of exp2 env state)))))])))

(define value-of-let
  (lambda (var-list exp1-list exp2 env state)
    (value-of exp2 (add-env var-list exp1-list env state) state)))

(define value-of-exp 
  (lambda (rator rand-list env state)
    (let ((proc (expval->proc (autoDerefIfNeed (value-of rator env state))))
          (arg (value-of-arg rand-list env state)))
      (if (zero? state)
          (apply-procedure proc arg env  state)
          (apply-procedure-rec proc arg env state)))))

(define value-of-arg
  (lambda (arg-list env state)
    (if (null? (cdr arg-list))
        (list (value-of (car arg-list) env state))
        (append (list (value-of (car arg-list) env state)) (value-of-arg (cdr arg-list) env state)))))

(define value-of-begin
  (lambda (exp1 exps env state)
    (letrec
        ((value-of-begins
          (lambda (e1 es)
            (let ([v1 (value-of e1 env state)])
              (if (null? es)
                  (autoDerefIfNeed v1)
                  (value-of-begins (car es) (cdr es)))))))
      (value-of-begins exp1 exps))))

(define add-env
  (lambda (var-list exp1-list env state)
    (let ([newVal (value-of (car exp1-list) env state)])
      (if (null? (cdr var-list)) 
          (if (expval? newVal)
              (extend-env (car var-list) newVal env)
              env)
          (cond
            [(expval? newVal)  (extend-env (car var-list) newVal (add-env (cdr var-list) (cdr exp1-list) env state))]
            [else (add-env (cdr var-list) (cdr exp1-list) env state)])))))

(define add-env-proc
  (lambda (var-list exp1-list env state)
    (if (null? (cdr var-list))
        (cond 
          [(expression? (car exp1-list)) 
           (extend-env (car var-list) (autoDerefIfNeed (value-of (car exp1-list) env state)) env)]
          [else (extend-env (car var-list) (value-of (car exp1-list) env state) env)])
        (cond 
          [(expression? (car exp1-list)) 
           (extend-env (car var-list) (autoDerefIfNeed (value-of (car exp1-list) env state)) (add-env-proc (cdr var-list) (cdr exp1-list) env state))]
          [else (extend-env (car var-list) (value-of (car exp1-list) env state) (add-env-proc (cdr var-list) (cdr exp1-list) env state))]))))


;;SEE Lecture 7 slide p57
(define value-of-if
  (lambda (exp1 exp2 exp3 env state)
    (let ([val1 (value-of exp1 env state)])
      (cond
        [(equal? #t (expval->bool val1)) (value-of exp2 env state)]
        [(equal? #f (expval->bool val1))(value-of exp3 env state)]
        [else (undefined-exp)]))))

;;================Two cases to resolve letrec and curry==============
(define apply-procedure
  (lambda (proc1 arg env state)
    (cases proc proc1
      (procedure (var body saved-env)
                 (set! env (appendEnv env saved-env))
                 (let ((new-env (add-env-proc var arg env state)))
                   (value-of body new-env state))))))

(define appendEnv
  (lambda (env1 env2)
    (cases environment env1
      (empty-env  () env2)
      (extend-env (var value NextEnv)
                  (extend-env 
                    var
                    value
                    (appendEnv NextEnv env2)))
      (extend-env-rec* (exp1 exp2 exp3 NextEnv)
                       (extend-env-rec*
                        exp1
                        exp2
                        exp3
                        (appendEnv NextEnv env2)))
      )))

(define apply-procedure-rec
  (lambda (proc1 arg  env state)
    (cases proc proc1
      (procedure (var body saved-env)
                 ;;(set! env (appendEnv env saved-env))
                 (let ((new-env (add-env-proc var arg env state)))
                   (cases expression body
                     (proc-exp(var-list exp)
                              (value-of-exp body arg new-env state))
                     (else (value-of body new-env state))))))))


;==============================Wrap Func=================================
(define dynamic-interpreter
  (lambda (exp)
    (initialize-store!)
    (let ([result (value-of (scan&parse exp) (empty-env) 0)])
      (cond 
        [(expval? result)
         (cases expval result
           (ref-val(ref) (expval->num (deref ref)))
           (num-val(value) value)
           (bool-val(bool) 
                    (if bool
                        'true
                        'false))
           (proc-val(proc)  proc))]
        [(expression? result)
         (cases expression result
           (undefined-exp() 'undefined)
           (else result))]))))


;=====================================Test========================================
;(trace dynamic-interpreter)



;(dynamic-interpreter "let x = newref(1) in begin set x 2;x end");2
;(dynamic-interpreter "let x = let y = newref(1) in begin set y 2;y end in x");2
;(dynamic-interpreter "let x = newref(1) in let f= proc (y) set y 2 in begin (f x); x end");2
;(dynamic-interpreter "let f=proc(x y) +(x,y) g=proc(x y z) +(x,y,z) in (f (g 1 2 3)1)");7
;(dynamic-interpreter "let f = proc(x) proc(y) +(x,y) in let g= proc(x)proc(y)proc(z) +(x,y,z) in ((f (((g 1)2)3))1)");7
;(dynamic-interpreter "let f = newref (proc (x y) +(x,y)) in begin set f proc (x y) -(x,y); (f 5 1) end");4
;(dynamic-interpreter "newref(1)")
;(dynamic-interpreter "let x = newref(1) g = proc(x) begin set x 5;x end h = proc(x) begin set x +(x,7); x end f = proc(x y) +(x,y) in (f (h x) (g x))");13
;(dynamic-interpreter "let x = newref(1) g = proc(x) begin set x 5;x end h = proc(x) begin set x +(x,7); x end f = proc(x y) +(x,y) in (f (g x) (h x))");17
;(dynamic-interpreter "let x = let inc = proc (x) +(1,x) in inc in (x 5)");6
;(dynamic-interpreter "let f = let inc = proc (x) +(1,x) in inc in (f 5)");6
;(dynamic-interpreter "let g = let counter = newref(0) in proc(dummy) begin set counter +(counter,1);counter end in let a = (g 11) in let b = (g 11) in -(a,b)");-1
;(dynamic-interpreter"x");undefined
;(dynamic-interpreter "if 5 then 0 else 1");undefined
;(dynamic-interpreter "let x = undefined in x");undefined
;(dynamic-interpreter "let x = let y = set x 1 in y in x");undefined
;(dynamic-interpreter "let x = 5 in = (x, 5)");true
;(dynamic-interpreter "let x = newref(1) in = (x, 1)");true
;(dynamic-interpreter "letrec factorial = proc (x) if =(x,0) then  1 else *(x, (factorial -(x,1)))in (factorial 5)");120
;(dynamic-interpreter "letrec x = 1 x = +(x,2) in x");3
;(dynamic-interpreter "letrec f = proc (x) if =(x , 0) then 1 else *(x, (g -(x, 1))) g = proc (x) if =(x , 0) then 2 else *(x, (f -(x, 1))) in (f 3)");12
;(dynamic-interpreter "let x = 1 in let f = proc (y) +(x,y) in let x= 2 in (f 5)");7