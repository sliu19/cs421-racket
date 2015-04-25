#lang eopl
;(require eopl)
(require trace/calltrace-lib)

(define (reduce fn init list)
  (cond ((null? list) init)
        ((null? (cdr list)) (fn init (car list)))
        (else (fn init 
                  (reduce fn (car list) (cadr list) )))))

(define-datatype member member?
  (mem
   (publicity number?)
   (sym symbol?)
   (exp expression?)))

(define member->pub
  (lambda (exp)
    (cases member exp
      (mem(exp1 id exp) exp1))))

(define member->id
  (lambda (exp)
    (cases member exp
      (mem(exp1 id exp) id))))

(define member->exp
  (lambda (exp)
    (cases member exp
      (mem(exp1 id exp) exp))))

;==== References
(define instrument-newref (make-parameter #f))
;; the-store: a Scheme variable containing the current state of the
;; store.  Initially set to a dummy variable.
(define the-store 'uninitialized)

(define get-reference
  (lambda (ref-type)
    (cadr ref-type)))

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

(define newref
  (lambda (x)
    (list "ref-type" (newref-helper x))))

;; newref : ExpVal -> Ref
;; Page: 111
(define newref-helper
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store
            (append the-store (list val)))
      (when (instrument-newref)
        (eopl:printf 
         "newref: allocating location ~s with initial contents ~s~%"
         next-ref val))                     
      next-ref)))                     

(define deref
  (lambda (reftype)
    (deref-helper (cadr reftype))))

(define deref-helper
  (lambda (ref)
    ; Control reaches here after loc/val is extracted from environment. 
    ; Only ints are valid locations, and the int must be a valid location in the store.
    ; 0-index addressing.
    (cond ((number? ref) 
            (if (or (>= ref (length the-store))
                    (equal? 0 (length the-store)))
                'undefined 
                (list-ref the-store ref)))
          (else 'undefined))))

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

(define setref
  (lambda (ref-type val)
    (cond ((equal? 'undefined val) val)
          ((equal? 'undefined ref-type) ref-type)
          ((is-reference? ref-type) (begin 
                                      (setref-helper (cadr ref-type) val)
                                      ref-type))
          (else (begin 
                  (setref-helper ref-type val)
                  'undefined)))))

(define setref-helper
  (lambda (ref val)
    (set! the-store
          (letrec
              ((setref-inner
                ;; returns a list like store1, except that position ref1
                ;; contains val. 
                (lambda (store1 ref1)
                  (cond
                    ((null? store1)
                     'undefined)
                    ((equal? 0 ref1)
                     (cons val (cdr store1)))
                    (else
                     (cons
                      (car store1)
                      (setref-inner
                       (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))


(define is-reference? 
  (lambda (arg)
    (cond ((and (list? arg) (equal? 2 (length arg)) (equal? "ref-type" (car arg))) #t)
          (else #f))))


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
    (obj-exp ("begin" (arbno expression ";") "end")begin-exp)
    (obj-exp ("if" expression "then" expression "else" expression "end")if-exp)
    (obj-exp ("let" (arbno identifier "=" expression) "in" expression "end") let-exp) 
    (obj-exp ("letrec" (arbno identifier "=" expression) "in" expression "end") letrec-exp)
    (obj-exp ( "(" expression (arbno expression) ")") exp-exp)
    (obj-exp ("self") self-exp)
    (obj-exp ("super") super-exp)
    (obj-exp ("EmptyObj") empty-exp)
    (obj-exp ("extend" expression "with" (arbno MemberDecl)) extend-exp)
    (obj-exp (identifier) var-exp)
    (MemberDecl("public" identifier "=" expression ";") public-member)
    (MemberDecl("protected" identifier "=" expression";") protected-member)
    ))

;;sllgen from textbook appendix B
(sllgen:make-define-datatypes spec grammar)
(define scan&parse
  (sllgen:make-string-parser spec grammar))

(initialize-store!)

(define empty-env
  (lambda () '()))

(define extend-env
  (lambda (key value env-ref)
    (let* ([env (deref env-ref)])
      (cond ((null? env) (setref env-ref (list (list key value))))
            ((equal? (caar env) key) (setref env-ref (append (list (list key value)) (cdr env))))
            (else (setref env-ref (append (list (list key value))env)))))))

(define apply-helper
  (lambda (possibly-env-ref key)
    (let* ([env (if (is-reference? possibly-env-ref)
                    (deref possibly-env-ref)
                    possibly-env-ref)])
      (cond ((null? env) 'undefined)
            ((equal? key (caar env)) (cadar env))
            (else (apply-helper (cdr env) key))))))

(define begin-helper
  (lambda (exp-list env)
    (let ([first-exp (car exp-list)]
          [rest (cdr exp-list)])
      (if (null? rest)
          (value-of first-exp env)
          (begin
            (value-of first-exp env)
            (begin-helper rest env))))))

(define apply-env
  (lambda (key possibly-env-ref)
    (let* ([env (if (is-reference? possibly-env-ref)
                    (deref possibly-env-ref)
                    possibly-env-ref)]
           [result (apply-helper env key)])
      result)))

(define is-object?
  (lambda (x) (if (and (list? x) (not (null? x)) (equal? (car x) 'obj-type))
                  #t
                  #f)))

(define templ-extend-multi
  (lambda (id-list exp-list env-ref)
    (if (or (null? id-list) (null? exp-list))
        env-ref
        (begin 
          ; This behaves like let*, like how the spec asks for
          (extend-env (car id-list) (value-of (car exp-list) env-ref) env-ref)
          (templ-extend-multi (cdr id-list) (cdr exp-list) env-ref)))))

(define templ-extend-multi-rec
  (lambda (id-list exp-list env-ref)
    (if (or (null? id-list) (null? exp-list))
        env-ref
        (let* [(new-exp (car exp-list))
               (new-value (if (expression? new-exp)
                            (cases expression new-exp
                              (proc-exp(arg-list body)
                                      (list 'proc-type (list arg-list body) '()))
                              (else (templ-constructor 'raw-exp new-exp '())))
                            (templ-constructor 'raw-exp new-exp '())))]
          (begin
            (extend-env (car id-list) new-value env-ref)
            (templ-extend-multi-rec (cdr id-list) (cdr exp-list) env-ref))))))



(define templ-constructor
  (lambda (code payload opt)
    (list code payload opt)))

(define templ-get-code
  (lambda (t)
    (car t)))

(define templ-get-payload
  (lambda (t)
    (cadr t)))

(define templ-set-opt
  (lambda (templ newopt)
    (list (templ-get-code templ) (templ-get-payload templ) newopt)))

(define templ-get-opt
  (lambda (t)
    (caddr t)))

(define emptyObject
  (lambda ()
    (templ-constructor 'obj-type (list (newref (empty-env)) '()) '() ) ))

(define subClass
  (lambda (super)
    (case (templ-get-code super)
      ('obj-type (let ([super-struct (templ-get-payload super)])
                   (templ-constructor 'obj-type (list (newref (empty-env)) super-struct) '())))
      (else (templ-constructor 'terminal 'undefined '())))))

(define obj-get-env
  (lambda (obj)
    (car (templ-get-payload obj))))
(define obj-get-super
  (lambda (obj)
    (cadr (templ-get-payload obj))))

(define get-type
  (lambda (x)
    (cond ((and (list? x) (not (null? x))) (car x)) 
          (else 'no-type))))

(define resolve-typed-value
  (lambda (val env-ref)
    (let ([payload (templ-get-payload val)])
      (case (get-type val)
        ('no-type val)
        ('terminal (cadr val))
        ('raw-exp (resolve-typed-value (value-of payload env-ref) env-ref))
        (else val)))))

(define make-protection
  (lambda (prot-val)
    (list 'prot-type prot-val)))

(define add-member-to-env
  (lambda (mem-list env)
    (if (null? mem-list)
        env
        (let* ([member-id (member->id (value-of (car mem-list) env))]
               [member-exp (member->exp (value-of (car mem-list) env))]
               [member-prot (make-protection (member->pub (value-of (car mem-list) env)))]
               [member-obj (list 'raw-exp member-exp member-prot)])
          (cond ((expression? member-exp)
                 (cases expression member-exp
                   (proc-exp (arg-list body) 
                             (let ([proc-templ (templ-constructor 'proc-type (list arg-list body) '())])
                               (begin 
                                 (extend-env member-id proc-templ env)
                                 (add-member-to-env (cdr mem-list) env))))
                   (else (begin
                           (extend-env member-id member-obj env) 
                           (add-member-to-env (cdr mem-list) env)))))
                 (else (begin
                         (extend-env member-id member-obj env) 
                         (add-member-to-env (cdr mem-list) env))))))))

(define extend-multi 
  (lambda (env-ref arg-list evaluated-args)
    (if (or (null? arg-list) (null? evaluated-args))
        env-ref
        (begin
          (extend-env (car arg-list) (car evaluated-args) env-ref)
          (extend-multi env-ref (cdr arg-list) (cdr evaluated-args))))))

(define list-last
  (lambda (list)
    (cond ((null? (cdr list)) (car list))
          (else (list-last (cdr list))))))

(define get-id-for-set 
  (lambda (exp1)
    (cond ((expression? exp1)
           ; TODO handle proc case? 
           ; proc probably cannot return identifier b/c automatically retrieves value for the identifier 
           (cases expression exp1
             (object (obj-expression id-list)
                     (if (not (null? id-list))
                         (list-last id-list)
                         (cases obj-exp obj-expression
                           (var-exp (id) id)
                           (else '()))))
             (else '() ))))))

(define find-enclosing-env-helper 
  (lambda (obj-struct id-list set-id prior-recursion-stack-env val-exp)
    (cond ((null? id-list) (extend-env set-id val-exp 'terminal prior-recursion-stack-env)) ; (set A bla) A is looked up in global-env
          ((null? (cdr id-list)) ; The identifier is found at this level of recursion
            (let* ([found-templ (recursive-seek obj-struct (car id-list))] ;; TODO search recursive
                   [obj-env-ref (car obj-struct)]
                   [found-payload (templ-get-payload found-templ)])
              (if (equal? found-payload 'undefined)
                  ;; The id does not exist in the environments
                  (templ-constructor 'terminal 'undefined '())
                  ;; The id was found in the object environment
                  (extend-env (car id-list) val-exp obj-env-ref))))
                  ;(templ-constructor 'terminal obj-env-ref '()))))
          (else ; There are more identifiers which must be resolved
           (let* ([top-id (car id-list)]
                  [rem-id (cdr id-list)]
                  [obj-env (car obj-struct)]
                  [found-templ (recursive-seek obj-struct top-id)]
                  [found-payload (templ-get-payload found-templ)])
             (cond ((equal? found-payload 'undefined) (templ-constructor 'terminal 'undefined '())) ; this level ID was not found
                   (else (case (templ-get-code found-templ)
                           ('obj-type (let ([new-obj-struct (templ-get-payload found-templ)]) ;recurse, passing in new object type and the current object environment
                                        (find-enclosing-env-helper new-obj-struct rem-id set-id obj-env)))
                           (else (templ-constructor 'terminal 'undefined '())))))))))) ;for non-objects, cannot for .ID operation
                         
                           
              

(define find-enclosing-env 
  (lambda (expr set-id env val-exp)
    (cond ((expression? expr)
           (cases expression expr
             ;; Type of expression -> object expr : Case for A.B.x etc.
             (object (obj-expr id-list)
                     (cases obj-exp obj-expr
                       ;; Var type of obj-expr : A.B.x case as well
                       (var-exp (var-id)
                                ; What kind of value is extracted from the var-id
                                (let ([found-templ (apply-env var-id env)])
                                  (case (templ-get-code found-templ)
                                    ('obj-type (let* ([obj-struct (templ-get-payload found-templ)]
                                                      ; Since obj-exp is evaluated to object type, we can no longer look inside global env
                                                      [id-environment (find-enclosing-env-helper obj-struct id-list set-id env val-exp)])
                                                 id-environment))
                                    (else (templ-constructor 'terminal 'undefined '())))))
                       (else (templ-constructor 'terminal 'undefined '()))))
             (else (templ-constructor 'terminal 'undefined '())))))))
                                    

(define value-of
  (lambda (exp  env)
    (cond
      ((obj-exp? exp)
       (cases obj-exp exp
         
         (if-exp (exp1 exp2 exp3)
                 (let [(result (resolve-typed-value (value-of exp1 env) env))]
                   (cond ((boolean? result)
                          (if result
                              (value-of exp2 env)
                              (value-of exp3 env)))
                          [else 'undefined])))
         
         (let-exp (id-list exp-list body)
                  (let* ([extended-env (templ-extend-multi id-list exp-list env)])
                    (value-of body extended-env)))
         
         (letrec-exp(id-list exp-list body)
                 (let* ([extended-env (templ-extend-multi-rec id-list exp-list env)])
                    (value-of body extended-env)))
         
         (exp-exp (first-exp rest-exp-list)
                  (let* ([proc-templ (value-of first-exp env)]
                         [proc-struct (templ-get-payload proc-templ)]
                         [args-list (car proc-struct)]
                         [proc-body (cadr proc-struct)]
                         [evaluated-args-tmpl (map (lambda (x) (value-of x env)) rest-exp-list)]
                         [new-env (extend-multi env args-list evaluated-args-tmpl)])
                    (value-of proc-body new-env)))
         
         ;emptyObj
         (empty-exp() (emptyObject))
         
         (extend-exp (exp mem-list)
                     (let* [(obj (value-of exp env))]
                       (case (get-type obj)
                         ('obj-type (let* ([subclass (subClass obj)]
                                           [subclass-env (obj-get-env subclass)])
                                      (begin
                                        ; Update entries in subclass environment
                                        (add-member-to-env mem-list subclass-env)
                                        ; Return subclass object
                                        subclass))))))
         
         ; Extract the last object-template which was set for self
         (self-exp () (let ([self-templ (apply-env 'self env)])
                        (if (equal? self-templ 'undefined)
                             (templ-constructor 'terminal 'undefined '())
                             self-templ)))
                   ;(value-of (var-exp 'self) env))
         
         ; Same as self, but additionally extract super if self returns object-type
         (super-exp() (let ([self-templ (apply-env 'self env)])
                        (if (equal? self-templ 'undefined)
                            (templ-constructor 'terminal 'undefined '())
                            (case (templ-get-code self-templ)
                              ('obj-type (let* ([object-struct (templ-get-payload self-templ)])
                                              (templ-constructor 'obj-type (cadr object-struct) '())))
                              (else (templ-constructor 'terminal 'undefined '()))))))
         ;         (cadr (value-of (var-exp 'self) env))) 
         
         (begin-exp (exp-list) (if (null? exp-list)
                                   'undefined
                                   (begin-helper exp-list env)))
         
         ; TODO : Need to perform additional action
         (var-exp (var) (apply-env var env))
         
         (else exp)))
      [(expression? exp)
       (cases expression exp
         
         (arith-exp (op exp exp-list)
            (let* ([arglist (append (list exp) exp-list)]
                   [exp1-val (resolve-typed-value (value-of exp env) env)]
                   [reduce-vals (map (lambda (x) (resolve-typed-value (value-of x env) env)) exp-list)])
              
              (templ-constructor 'terminal (reduce (parse-op op) exp1-val reduce-vals) '())))
         
         (compare-exp (op exp1 exp2)
                      (let ([bool-val ((parse-op op) (resolve-typed-value (value-of exp1 env) env) (resolve-typed-value (value-of exp2 env) env))])
                        (templ-constructor 'terminal bool-val '())))

         (num-exp (num) (list 'terminal num '()))
         
         ; proc-exp
         ; looks like you cannot pass arguments to proc
         ; procs return body exp for dynamic dispatch
         (proc-exp (arg-list body) (list 'proc-type (list arg-list body) '()))
    
         ; set-exp
         ; val exp also dynamic binding, so we do not evaluate here
         (set-exp (exp1 val-exp)
                  (let* ([calc-val (value-of val-exp env)] ; Assuming the value-of returns a template.
                         [set-id (get-id-for-set exp1)]
                         [env-tmpl (find-enclosing-env exp1 set-id env val-exp)]) ;sneakily add the value as well
                    env-tmpl))
                         
                         ;[env-ref (templ-get-payload env-tmpl)]
                         ;; set-id may be null. The implicit reference must be stored by identifier
                         ;[protection (templ-get-opt env-tmpl set-id)] ; This function is flawed
                         ;[final-val (templ-set-opt calc-val protection)])
                    ;(if (equal? env-ref 'undefined)
                        ;; Set is invalid : either identifier is not found, or the protection prevents the identifier from being set.
                        ;(templ-constructor 'terminal 'undefined '())
                        ;(extend-env set-id final-val env))))
         
         (compare-equ-exp (exp1 exp2)
                          (let* ([v1 (resolve-typed-value (value-of exp1 env) env)]
                                 [v2 (resolve-typed-value (value-of exp2 env) env)])
                            (templ-constructor 'terminal (= v1 v2) '())))
         (true-exp() (list 'terminal #t))
         (false-exp() (list 'terminal #f))
         (object (obj-exp id-list) (value-of-object obj-exp id-list env) )
         (else (templ-constructor 'terminal 'undefined '())))
         ]
      [(MemberDecl? exp) 
       (cases MemberDecl exp
         (public-member(id exp) (mem 1 id exp))
         (protected-member(id exp) (mem -1 id exp)))]
      [else exp])))

(define exp-is-self-or-super 
  (lambda (exp)
          (cases obj-exp exp
            (self-exp() #t)
            (super-exp() #t)
            (else #f))))

(define is-protected
  (lambda (prot-val)
    (cond ((null? prot-val) #f)
          ((equal? (cadr prot-val) -1) #t)
          (else #f))))

(define recursive-seek
  (lambda (obj-struct id)
    (if (null? obj-struct)
        (templ-constructor 'terminal 'undefined '())
        (let* ([local-env (car obj-struct)]
               [super-obj-struct (cadr obj-struct)]
               [local-found (apply-env id local-env)])
          (if (equal? 'undefined local-found)
              (recursive-seek super-obj-struct id)
              local-found)))))
  
(define val-of-obj-recursive
  (lambda (templ-struct id-list is-self-or-super env) ; any general templ
    (if (null? id-list)
        ;; no more identifiers, pass the template. no guarantee this is return value (i.e. may be used in expr-expr.)
        templ-struct
        (case (templ-get-code templ-struct)
          ; Handle types here (recursively)
          
          ; For raw-exp and proc types, evaluate payload and recurse. Recursive check if valid obj is produced
          ('raw-exp (let* ([expr (templ-get-payload templ-struct)]
                           [evaluated-templ (value-of expr env)])
                      (val-of-obj-recursive evaluated-templ id-list is-self-or-super env)))
          
          ('proc-type (let* ([proc-struct (templ-get-payload templ-struct)]
                             [proc-id-list (car proc-struct)]
                             [proc-body (cadr proc-struct)])
                        ; a.b.x etc. kind of grammer cannot pass arguments
                        (val-of-obj-recursive (value-of proc-body env) id-list is-self-or-super env)))
           
          ('obj-type (let* ([obj-struct (templ-get-payload templ-struct)]
                            [found-templ (recursive-seek obj-struct (car id-list))])
                       ;(begin 
                       ;  (extend-env 'self templ-struct env) ; A.x Set self to A's template object 
                         (cond ((equal? 'undefined found-templ) (templ-constructor 'terminal 'undefined '()))
                               (else 
                                ; template found
                                (let ([protection-code (templ-get-opt found-templ)])
                                  (cond ((not (is-protected protection-code)) 
                                         (val-of-obj-recursive found-templ (cdr id-list) #f env)) ; OK - public or no prot
                                        ((and (is-protected protection-code) is-self-or-super) 
                                         (val-of-obj-recursive found-templ (cdr id-list) #f env)) ; OK - protect, but super/self
                                        (else (templ-constructor 'terminal 'undefined '()))))))))
          
          (else (templ-constructor 'terminal 'undefined '()))))))

(define is-self-set?
  (lambda (env-ref)
    (if (equal? 'undefined (apply-env 'self env-ref))
        #f
        #t)))
  
(define value-of-object
  (lambda (obj-exp id-list env)
    (let* ([templ-struct (value-of obj-exp env)]
           [is-self-or-super (exp-is-self-or-super obj-exp)])
      (if (null? id-list)          
          templ-struct
          (begin ;set self
            (cond ((not (is-self-set? env)) (extend-env 'self templ-struct env)))
            (val-of-obj-recursive templ-struct id-list is-self-or-super env))))))
          

(define object-interpreter
  (lambda (exp)
    (let ([env-ref (newref (empty-env))])
      (boolean-printer (resolve-typed-value (value-of (scan&parse exp) env-ref) env-ref)))))

(define boolean-printer
  (lambda (x)
    (cond ((equal? x #t) 'true)
          ((equal? x #f) 'false)
          (else x))))

(trace value-of)
(trace object-interpreter)
(trace templ-extend-multi-rec)
(trace templ-get-payload)
(trace templ-constructor)
(trace extend-multi )


;(object-interpreter "letrec fact = proc (n)
;                       if =(n, 0) then 1 else *(n, (fact -(n, 1))) end end
;         in (fact 5) end" )


(provide object-interpreter)
