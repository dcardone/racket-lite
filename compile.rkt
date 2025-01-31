#lang racket
(provide (all-defined-out))
(require "ast.rkt")
(require "compile-ops.rkt")
(require "types.rkt")
(require a86/ast)

(define rax 'rax)
(define rbx 'rbx) ; heap
(define rsp 'rsp) ; stack
(define rdi 'rdi) ; arg
(define r15 'r15) ; stack pad (non-volatile)

;; Prog -> Asm
(define (compile p)
  (match p
    [(Prog ds e)
     (prog (Global 'entry)
           (Extern 'peek_byte)
           (Extern 'read_byte)
           (Extern 'write_byte)
           (Extern 'raise_error)
           (Label 'entry)
           (Push rbx)    ; save callee-saved register
           (Push r15)
           (Mov rbx rdi) ; recv heap pointer

           (compile-e e '())
           (Pop r15)     ; restore callee-save register
           (Pop rbx)
           (Ret)
           (compile-defines ds)
           (Label 'err)
           pad-stack
           (Call 'raise_error))]))

;; [Listof Defn] -> Asm
(define (compile-defines ds)
  (match ds
    ['() (seq)]
    [(cons d ds)
     (seq (compile-define d)
          (compile-defines ds))]))

;; Defn -> Asm
(define (compile-define d)
  (match d
    [(Defn f fun)
     (compile-fun f fun)]))

;; Id Fun -> Asm
(define (compile-fun f fun)
  (match fun
    [(FunPlain xs e)
     (seq (Label (symbol->label f))
          (Cmp 'r11 (length xs))
          (Jne 'err)
          (compile-e e (reverse xs))
          (Add rsp (* 8 (length xs)))
          (Ret))]
    [(FunRest xs x e)
     (seq (seq (Label (symbol->label f))
               ;; Check arity
               (Cmp 'r11 (length xs))
               (Jl 'err) ;; should jump if not enough args provided
               (Sub 'r11 (length xs))
               ;; start popping extra args off stack
               (build-rest-list)
               (compile-e e (cons x (reverse xs)))
               (Add rsp (* 8 (add1 (length xs))))
               (Ret)))]
    [(FunCase cs) (let ((argnum (argument-nums cs)))
                    (seq (Label (symbol->label f))
                         (choose-fun f argnum cs 0)
                   (compile-fun-case f cs 0)))]))

                             
(define (argument-nums cs)
  (match cs
    ['() '()]
    [(cons c cs)
     (match c
       [(FunPlain xs e) (cons (length xs) (argument-nums cs))]
       [(FunRest xs x e) (cons (length xs) (argument-nums cs))])]))

(define (choose-fun f argnum cs count)
  (match argnum
    ['() (seq)]
    [(cons arg argnum)
     (match cs
       ['() (seq)]
       [(cons c cs)
         (match c
           [(FunPlain xs e)
              (seq (Cmp 'r11 (length xs))
                   (Je (symbol->label (string->symbol (string-append (symbol->string f) (number->string (length xs)) (number->string count)))))
                   (choose-fun f argnum cs (add1 count)))]
           [(FunRest xs x e) (seq (Cmp 'r11 (length xs))
                                  (Jge (symbol->label (string->symbol (string-append (symbol->string f) (number->string (length xs)) "rest" (number->string count)))))
                                  (choose-fun f argnum cs (add1 count)))])])]))
                             
       
       

(define (compile-fun-case f cs count)
  (match cs
    ['() (seq)]
    [(cons c cs)
     (match c
       [(FunPlain xs e) (seq (compile-fun (string->symbol (string-append (symbol->string f) (number->string (length xs)) (number->string count))) c)
                             (compile-fun-case f cs (add1 count)))]
       [(FunRest xs x e) (seq (compile-fun (string->symbol (string-append (symbol->string f) (number->string (length xs)) "rest" (number->string count))) c)
                             (compile-fun-case f cs (add1 count)))])]))
    

(define (build-rest-list)
  (let ((loop (gensym 'loop)) (end (gensym 'end)) (emptyend (gensym 'emptyend)))
    (seq (Mov 'r10 (value->bits '()))
         (Cmp 'r11 0)
         (Je emptyend)
         (Mov (Offset rbx 0) 'r10)
         (Pop 'r10)
         (Mov (Offset rbx 8) 'r10)
         (Add rbx 16)
         (Sub 'r11 1)
    
         (Label loop)
         (Cmp 'r11 0)
         (Je end)
         
         

         ;; write cons pointer to rbx
         (Mov 'r9 rbx)
         (Sub 'r9 16)
         (Xor 'r9 type-cons)
         (Mov (Offset rbx 0) 'r9)

         ;; pop next arg into r10
         (Pop 'r10)
         (Mov (Offset rbx 8) 'r10)
         (Add rbx 16)
              
         (Sub 'r11 1)
         (Jmp loop)



         (Label end)
         (Mov 'r10 rbx)
         (Sub 'r10 16)
         (Xor 'r10 type-cons)
         (Label emptyend)
         
         
         
         (Push 'r10))))


;; type CEnv = (Listof [Maybe Id])
;; Expr CEnv -> Asm
(define (compile-e e c)
  (match e
    [(Lit d) (compile-value d)]
    [(Eof) (compile-value eof)]
    [(Var x) (compile-variable x c)]
    [(Prim0 p) (compile-prim0 p)]
    [(Prim1 p e) (compile-prim1 p e c)]
    [(Prim2 p e1 e2) (compile-prim2 p e1 e2 c)]
    [(Prim3 p e1 e2 e3) (compile-prim3 p e1 e2 e3 c)]
    [(If e1 e2 e3)
     (compile-if e1 e2 e3 c)]
    [(Begin e1 e2)
     (compile-begin e1 e2 c)]
    [(Let x e1 e2)
     (compile-let x e1 e2 c)]
    [(App f es)
     (compile-app f es c)]
    [(Apply f es e)
     (compile-apply f es e c)]))

;; Value -> Asm
(define (compile-value v)
  (cond [(string? v) (compile-string v)]
        [else        (Mov rax (value->bits v))]))

;; Id CEnv -> Asm
(define (compile-variable x c)
  (let ((i (lookup x c)))
    (seq (Mov rax (Offset rsp i)))))

;; String -> Asm
(define (compile-string s)
  (let ((len (string-length s)))
    (if (zero? len)
        (seq (Mov rax type-str))
        (seq (Mov rax len)
             (Mov (Offset rbx 0) rax)
             (compile-string-chars (string->list s) 8)
             (Mov rax rbx)
             (Xor rax type-str)
             (Add rbx
                  (+ 8 (* 4 (if (odd? len) (add1 len) len))))))))

;; [Listof Char] Integer -> Asm
(define (compile-string-chars cs i)
  (match cs
    ['() (seq)]
    [(cons c cs)
     (seq (Mov rax (char->integer c))
          (Mov (Offset rbx i) 'eax)
          (compile-string-chars cs (+ 4 i)))]))

;; Op0 -> Asm
(define (compile-prim0 p)
  (compile-op0 p))

;; Op1 Expr CEnv -> Asm
(define (compile-prim1 p e c)
  (seq (compile-e e c)
       (compile-op1 p)))

;; Op2 Expr Expr CEnv -> Asm
(define (compile-prim2 p e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (compile-op2 p)))

;; Op3 Expr Expr Expr CEnv -> Asm
(define (compile-prim3 p e1 e2 e3 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons #f c))
       (Push rax)
       (compile-e e3 (cons #f (cons #f c)))
       (compile-op3 p)))
;; Expr Expr Expr CEnv -> Asm
(define (compile-if e1 e2 e3 c)
  (let ((l1 (gensym 'if))
        (l2 (gensym 'if)))
    (seq (compile-e e1 c)
         (Cmp rax (value->bits #f))
         (Je l1)
         (compile-e e2 c)
         (Jmp l2)
         (Label l1)
         (compile-e e3 c)
         (Label l2))))
;; Expr Expr CEnv -> Asm
(define (compile-begin e1 e2 c)
  (seq (compile-e e1 c)
       (compile-e e2 c)))

;; Id Expr Expr CEnv -> Asm
(define (compile-let x e1 e2 c)
  (seq (compile-e e1 c)
       (Push rax)
       (compile-e e2 (cons x c))
       (Add rsp 8)))

;; Id [Listof Expr] CEnv -> Asm
;; The return address is placed above the arguments, so callee pops
;; arguments and return address is next frame
(define (compile-app f es c)
  (let ((r (gensym 'ret)))
    (seq (Lea rax r)
         (Push rax)
         (compile-es es (cons #f c))
         ;; Communicated number of arguments
         (Mov 'r11 (length es))
         (Jmp (symbol->label f))
         (Label r))))

;; Id [Listof Expr] Expr CEnv -> Asm
(define (compile-apply f es e c)
  (let ((loop (gensym 'loop)) (end (gensym 'end)) (r (gensym 'ret)))
    (seq (Lea rax r)
         (Push rax)
         (Mov 'r11 0)
         (compile-es-arity es c)
         (compile-e e c)
         (Cmp rax (value->bits '()))
         (Je end)
         ;; check to make sure e is a list
         (assert-cons rax) ;; this will clobber r9 values
         ;; list in rax, start traversing and pushing elements
         (Label loop)
         (Xor rax type-cons)
         (Mov 'r9 (Offset rax 8))
         (Push 'r9) ;; push element
         (Add 'r11 1)

         (Mov 'r9 (Offset rax 0))
         (Cmp 'r9 (value->bits '())) ;; check if cdr is empty list
         (Je end)
         
         (Mov rax (Offset rax 0)) ;; load next address
         (Jmp loop)
         
         (Label end)
         (Jmp (symbol->label f))
         (Label r))))

(define (compile-es-arity es c)
  (match es
    ['() '()]
    [(cons e es)
     (seq (compile-e e c)
          (Push rax)
          (Add 'r11 1)
          (compile-es-arity es (cons #f c)))]))
     


         

;; [Listof Expr] CEnv -> Asm
(define (compile-es es c)
  (match es
    ['() '()]
    [(cons e es)
     (seq (compile-e e c)
          (Push rax)
          (compile-es es (cons #f c)))]))

;; Id CEnv -> Integer
(define (lookup x cenv)
  (match cenv
    ['() (error "undefined variable:" x)]
    [(cons y rest)
     (match (eq? x y)
       [#t 0]
       [#f (+ 8 (lookup x rest))])]))

