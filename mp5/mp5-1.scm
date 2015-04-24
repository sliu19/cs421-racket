#lang eopl
;(require eopl)
(require trace/calltrace-lib)

(define (reduce fn init list)
  (if (null? list) init
      (fn (car list)
          (reduce fn init (cdr list) ))))

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

(define deref-loc
  (lambda (loc)
    (deref-helper loc)))

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
                                      (write 'inside-setref)
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

(initialize-store!)
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
;==============================Data Structure=======================================
(define empty-env
  (lambda () '()))
 

;Env: (key （exp protection）)   ;;protection 1:public   0:non-member     -1:protected
(define extend-env
  (lambda (key value possibly-env-ref)
    (let* ([env (if (is-reference? possibly-env-ref)
                    (deref possibly-env-ref)
                    possibly-env-ref)])
      (cond ((null? env) (begin 
                           (write 'inside-null)
                           (setref possibly-env-ref (list (list key value)))
                           possibly-env-ref))
            ((equal? (caar env) key) (begin 
                                       (setref possibly-env-ref (append (list (list key value)) (cdr (deref possibly-env-ref))))
                                       possibly-env-ref))
            (else 
             (begin
               (setref possibly-env-ref (append (list (list key value))env))
               possibly-env-ref))))))

(define apply-helper
  (lambda (possibly-env-ref key)
    (let* ([env (if (is-reference? possibly-env-ref)
                    (deref possibly-env-ref)
                    possibly-env-ref)])
      (cond ((null? env) 'undefined)
            ((equal? key (caar env))
             ;(if (expression? (cadar env))
             (cadar env))
            ; (car env)))
            (else (apply-helper (cdr env) key))))))
 
(define apply-env
  (lambda (key possibly-env-ref)
    (let* ([env (if (is-reference? possibly-env-ref)
                    (deref possibly-env-ref)
                    possibly-env-ref)]
           [result (apply-helper env key)])
      (if (equal? 'undefined result)
          'undefined
          (if (expression? (car result))
              (value-of (car result) possibly-env-ref)
              (car result))))))

;Bug? How is this getting the right value?
(define apply-env-protection
  (lambda (key env)
    (let [(result (apply-helper env key))]
      (if (equal? 'undefined result)
          'undefined
          (cadr result)))))
;          (if (expression? (car result))
;              (value-of (car result) env)
;              (car result))))))
   

(define emptyObject
  (lambda ()
    (list (newref (empty-env)) '())))

(define emptyObject?
  (lambda (obj)
    (if (and (equal? '() (car obj)) (equal? '() (cadr obj)))
        #t
        #f)))

(define subClass
  (lambda (self super)
    (list self super)))

;in publicity field #t is public 
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

(define obj-env
  (lambda (obj)
    (car obj)))

(define env-obj-is-protected
  (lambda (id env)
    (let ([protection-type (apply-env-protection id env)])
      (cond 
        ((equal? protection-type 'undefined) 'undefined)
        ((equal? protection-type -1) #t)
        (else #f)))))
(define env-obj-is-public
  (lambda (id env)
    (let ([protection-type (apply-env-protection id env)])
      (cond 
        ((equal? protection-type 'undefined) 'undefined)
        ((equal? protection-type 1) #t)
        (else #f)))))


;==============================Value-of Functions===================================
; Helper to find the environment corresponding to the identifier list (id-list)
(define set-env-helper 
  (lambda (obj id-list val-exp bt-self-or-super env)
    (if (equal? 1 (length id-list))
        (let ([val-from-env (apply-env (car id-list) (obj-env obj))])
          ; does the id even exist
          (if (equal? val-from-env 'undefined)
              'undefined
              
              ; handle protection cases
              (if (env-obj-is-public (car id-list) (obj-env obj))
                  ; public case : extend environment
                  (extend-env (car id-list) (list val-exp 1) (obj-env obj))
                  ; protected case : is accessible if called from self/super
                  (if bt-self-or-super
                      (extend-env (car id-list) (list val-exp -1) (obj-env obj))
                      ; scope not allowed
                      'undefined))))
                  
                   
        ; the list of IDs is length >1 => consume car of list = some member variable of obj
        (let* ([recurse-obj (apply-env (car id-list) (obj-env obj))]
               [is-public (env-obj-is-public (car id-list) (obj-env obj))]
               [remainder-list (cdr id-list)])
          ;; id list will never be a self or super so there will not be valid protected types
          (if is-public
              (set-env-helper recurse-obj remainder-list val-exp #f env)
              ; is protected
              (if bt-self-or-super
                  (set-env-helper recurse-obj remainder-list val-exp #f env)
                  'undefined
              ))))))

(define (list-last-element l)
  (cond ((null? (cdr l)) (car l))
        (else (list-last-element (cdr l)))))

(define begin-helper
  (lambda (exp-list env)
    (let ([first-exp (car exp-list)]
          [rest (cdr exp-list)])
      (if (null? rest)
          (value-of first-exp env)
          (begin
            (value-of first-exp env)
            (begin-helper rest env))))))

(define (zip . xss) (apply map list xss))

(define add-id-to-object-pairs 
  (lambda (id-exp-pairs env)
    (if (null? id-exp-pairs) 
        env 
        (let* ([pair (car id-exp-pairs)]
               [rest (cdr id-exp-pairs)]
               [id (car pair)]
               [expr (cadr pair)]
               [is-obj-creation (if (expression? expr)
                                    (cases expression expr
                                      (object (exp id-list) 
                                              (cases obj-exp exp
                                                (extend-exp (exp dec-lis) #t)
                                                (else #f)))
                                      (else #f))
                                    #f)]
               [existing-obj (apply-env id env)]
               [extended-obj (if (equal? existing-obj 'undefined)
                                 'undefined
                                 (list (append (list existing-obj) (list id)) 0))]
               [extended-env (if is-obj-creation
                                 (extend-env id extended-obj env)
                                 env)])
          extended-env))))

(define value-of
  (lambda (exp  env)
    (cond
      [(obj-exp? exp)
       (cases obj-exp exp
         
         (if-exp(exp1 exp2 exp3)
                (let [(result (value-of exp1 env))]
                  (cond
                    [(boolean? result)
                     (if result
                         (value-of exp2 env)
                         (value-of exp3 env))]
                    [else 'undefined])))
         
         (let-exp (id-list exp-list body)
                  (let* ([extended-env (add-env id-list exp-list env)])
                        ;[id-exp-pairs (zip id-list exp-list)]
                        ;[env-obj-with-ids (add-id-to-object-pairs id-exp-pairs extended-env)])
                    (value-of body extended-env)))
         
         (letrec-exp(id-list exp-list body)
                  (value-of body (add-env-rec id-list exp-list env)))
         
         (exp-exp (first-exp rest-list) 
                  (let* ([exp-list (cons first-exp rest-list)]
                         [exp-list-length (length exp-list)]
                         [env-list (replicate env exp-list-length)]
                         [value-list (map value-of exp-list env-list)])
                    (list-last value-list)))
         
         ;emptyObj
         (empty-exp() (emptyObject))
         (extend-exp(exp mem-list)
                    (subClass (add-mem mem-list env) (value-of exp env)))
         (self-exp ()
                   (value-of (var-exp 'self) env))
         (super-exp()
                  (cadr (value-of (var-exp 'self) env))) 
         (var-exp (var) (apply-env var env))
         
         ;begin
         (begin-exp (exp-list)
                    (if (equal? 0 (length exp-list))
                        'undefined
                        (begin-helper exp-list env)))
         
         (else  exp))
       ]
      [(expression? exp)
       (cases expression exp
         
         (arith-exp (op exp exp-list)
            (let ([arglist (append (list exp) exp-list)])
              (reduce (parse-op op) (value-of exp env) (map (lambda (x) (value-of x env)) exp-list))))
         
         (compare-exp (op exp1 exp2)
                      ((parse-op op) (value-of exp1 env) (value-of exp2 env)))

         (num-exp (num) num)
         
         ; proc-exp
         ; looks like you cannot pass arguments to proc
         ; procs return body exp for dynamic dispatch
         (proc-exp (arg-list body) (arg-list body))
    
         ; set-exp
         ; val exp also dynamic binding, so we do not evaluate here
         (set-exp (exp1 val-exp)
                  (cond  
                    ((expression? exp1)
                     (cases expression exp1
                       
                       
                       (object (object-exp id-list) 
                               ; For handling protection classes, we can access protected members 
                               ; only from super and self keywords
                               (cases obj-exp object-exp
                                 ;; TODO recursive searching
                                 (self-exp ()(let* ([obj (value-of object-exp env)])
                                               (set-env-helper obj id-list val-exp #t env)))
                                 
                                 (super-exp ()(let* ([obj (value-of object-exp env)])
                                                (set-env-helper obj id-list val-exp #t env)))
                                 
                                 (else (let* ([obj (value-of object-exp env)])
                                         (set-env-helper obj id-list val-exp #f env)))))
                       
                       
                       ; None of other expressions can give an identifier
                       (else 'undefined)))
                    
                    
                    
                    ; Setting Identifiers shouldnt even be allowed by the grammar.
                    ((obj-exp? exp1)
                     (cases obj-exp exp1
                       (var-exp (id) 
                                ; protection class?
                                (extend-env id val-exp env))
                       (else 'undefined)))
                    ))
         
         (compare-equ-exp (exp1 exp2)
                      (= (value-of exp1 env) (value-of exp2 env)))
        

         (true-exp() #t)
         
         (false-exp() #f)

         (object (obj obj-list) (value-of-object obj obj-list env) )

         (else 'undefined))
         ]
      [(MemberDecl? exp) 
       (cases MemberDecl exp
         (public-member(id exp) (mem 1 id exp))
         (protected-member(id exp) (mem -1 id exp)))]
      [else exp])))

(define add-env
  (lambda (id-list exp-list env)
    (if (or (null? id-list) (null? exp-list))
        env
        (extend-env (car id-list) (list (value-of (car exp-list) env) 0) (add-env (cdr id-list) (cdr exp-list) env)))))

(define add-env-rec
  (lambda (id-list exp-list env)
    (if (or (null? id-list) (null? exp-list))
        env
        (extend-env (car id-list) (list (car exp-list) 0) (add-env (cdr id-list) (cdr exp-list) env)))))

(define add-mem
  (lambda (mem-list env)
    (if (null? mem-list)
        env
        (extend-env (member->id (value-of (car mem-list) env))(list (member->exp (value-of (car mem-list) env))(member->pub (value-of (car mem-list) env))) (add-mem (cdr mem-list) env)))))

(define value-of-object
  (lambda (obj obj-list env)
    (let [(obj (value-of obj env))]
      (if (null? obj-list)
          obj
          (if (null? (cdr obj-list))   
              (search-value (car obj-list) obj)
              (let* [(result (value-of obj env))
                     (env (extend-env 'self result env))]              
                (value-of-object (search-value (car obj-list) obj) (cdr obj-list) env)))))))
    
(define search-value
  (lambda (obj-id obj)
    (if (emptyObject? obj)
        'undefined
        (let [(result (value-of obj-id (obj-env obj)))]
          (if (equal? 'undefined result)
              (search-value obj-id (cadr obj))
              (if (env-obj-is-public obj-id (obj-env obj))
                  
                   (apply-env result (obj-env obj))
                  ;;Not right, check for self and super
                  (if (or (equal? obj-id 'self) (equal? obj-id 'super))
                      result
                      'undefined)))))))

(define replicate
  (lambda (element n)
    (cond
      ((zero? n)
        '())
      (else
        (cons element (replicate element (- n 1)))))))

(define list-last
  (lambda (l)
    (if (equal? (length l) 1)
      (car l)
      (list-last (cdr l)))))


;===============================Object-interpreter===================================
(define object-interpreter
  (lambda (exp)
    (value-of (scan&parse exp) (newref (empty-env)))))


(trace object-interpreter)
(trace scan&parse)
(trace value-of)
(trace add-env)
(trace apply-helper)
(trace add-mem)
(trace apply-env)
(trace value-of-object)
(trace obj-env)
(trace subClass)
(trace extend-env)
(trace search-value)
(trace deref)
(trace setref-helper)
(trace setref)
(trace env-obj-is-public)
(trace add-id-to-object-pairs)


;(object-interpreter "extend EmptyObj with public a =3;  protected b = 2; public c = 1;")
;(object-interpreter "letrec a =b b = 3 in a end");3
;(object-interpreter "let a =2 b = 3 c =4  in +(a,b,c) end");9
;(object-interpreter "let a =4  in a end");
;(object-interpreter "let ob = extend EmptyObj with public x =1; in ob.x end");1
;(scan&parse "a.b.c.x")

;(object-interpreter "let a = extend EmptyObj with public b = extend EmptyObj with public c = extend EmptyObj with public x = 5 ; ; ; in a.b.c.x end");1


;(object-interpreter "let ob = extend EmptyObj with public x =1; in begin (set ob.x 2) ; ob.x; end end")

