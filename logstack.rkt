#lang racket

(struct fact
  (a b relation negated?) #:transparent)

(define (run code)
  (logstack (string->list code) '()))

(define (logstack code stack)
  ;(display (format "~a " (first (append code '("."))))) ;; testing
  ;(print-stack stack)
  (if (empty? code)
      stack
      (case (first code)
        [(#\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z
          #\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z
          ) (logstack (rest code) (push-fact (first code) stack))]
        [(#\?) (logstack (rest code) (test-output stack))]
        [(#\~) (logstack (rest code) (test-swap stack))]
        [(#\& #\|) (logstack (rest code) (and-or stack (first code)))]
        [(#\^ #\: #\=) (logstack (rest code) (compound stack (first code)))]
        [(#\!) (logstack (rest code) (cons (negate (first stack)) (rest stack)))]
        [(#\/) (logstack (rest code) (append (list (second stack) (first stack)) (drop stack 2)))]
        [(#\;) (logstack (rest code) (cons (first stack) stack))]
        [(#\$) (logstack (rest code) (rest stack))]
        [(#\@) (logstack (rest code) (append (rest stack) (list (first stack))))]
        [(#\*) (logstack (rest code) (cons (fact (fact #\p #f #f #f) (fact #\p #f #f #t) #\& #f) stack))]
        [(#\%) (logstack (rest code) (cons (fact (fact #\p #f #f #f) (fact #\p #f #f #t) #\| #f) stack))]
        [(#\() (logstack (ls-loop code stack) (rest stack))]
        [(#\.) (logstack '() stack)]
        [(#\#) (print-stack stack) (logstack (rest code) stack)]
        [else (logstack (rest code) stack)])))

(define (print-stack stack)
  (display "[ ")
  (map (λ (f) (display (format "~a " (print-fact f)))) stack)
  (display "]\n")
  (values))

(define (print-fact f)
   (case (fact-relation f)
     [(#\& #\|) (format "(~a~a~a)" (print-fact (fact-a f)) (fact-relation f) (print-fact (fact-b f)))]
     [(#f) (format "~a~a" (if (fact-negated? f) "!" "") (fact-a f))]))
     

(define (push-fact name stack)
  (cons (fact name #f #f #f) stack))

(define (test-output stack)
  (if (prove (first stack) (rest stack))
      (display "yes\n")
      (display "no\n"))
  (rest stack))

(define (test-swap stack)
  (if (prove (first stack) (rest stack))
      (append (list (third stack) (second stack)) (drop stack 3))
      (rest stack)))

(define (and-or stack relation)
  (cons (fact (first stack) (second stack) relation #f) (drop stack 2)))

(define (compound stack relation)
  (case relation
    [(#\^) (cons (fact (fact (negate (first stack)) (second stack) #\& #f)
                       (fact (first stack) (negate (second stack)) #\& #f) #\| #f)
                 (drop stack 2))]
    [(#\:) (cons (fact (negate (second stack)) (first stack) #\| #f) (drop stack 2))]
    [(#\=) (cons (fact (fact (first stack) (second stack) #\& #f)
                       (fact (negate (first stack)) (negate (second stack)) #\& #f) #\| #f)
                 (drop stack 2))]))

(define (ls-loop code stack)
  (define loop-length (match-bracket (rest code)))
  (if (prove (first stack) (rest stack))
      (append (rest (take code loop-length)) code)
      (drop code (+ loop-length 1))))

(define (match-bracket code (length 0) (brackets 1))
  (cond
    [(= brackets 0) length]
    [(equal? (first code) #\() (match-bracket (rest code) (+ length 1) (+ brackets 1))]
    [(equal? (first code) #\)) (match-bracket (rest code) (+ length 1) (- brackets 1))]
    [else (match-bracket (rest code) (+ length 1) brackets)]))

;;;; logic engine (very ugly and I think pretty inefficient)

(define (negate f)
  ;; rewrites negated propositions so only atomic propositions are negated, for ease of processing
  (if (fact-relation f)
      (case (fact-relation f)
        [(#\&) (fact (negate (fact-a f))
                     (negate (fact-b f))
                     #\| #f)]
        [(#\|) (fact (negate (fact-a f))
                     (negate (fact-b f))
                     #\& #f)]
        [else (error "unsupported relation")])
      (fact (fact-a f) #f #f (not (fact-negated? f)))))

(define (prove f stack)
  (define (prove-internal f stack)
    (foldl (λ (x a)
             (if (fact-relation f) ;; decompose the fact to be proved into the required atomic facts
                 (case (fact-relation f)
                   [(#\&) (if (and (prove-internal (fact-a f) stack)
                                   (prove-internal (fact-b f) stack))
                              #t
                              a)]
                   [(#\|) (if (or (prove-internal (fact-a f) stack)
                                  (prove-internal (fact-b f) stack)
                                  (prove-internal (fact-a f) (list (negate (fact-b f))))) ;; tautology identifier untested due to currently broken or recognition
                              #t
                              a)]
                   [else (error (format "unsupported relation: ~a" (fact-relation f)))])
                 (case (fact-relation x) ;; prove all possible atomic facts
                   [(#\&) (prove-internal f (append (list (fact-a x) (fact-b x)) (remove x stack)))]
                   [(#\|) (if (prove-internal (negate (fact-b x)) (remove x stack)) ;; if one side can be proven false, we can add the other to our information
                              (prove-internal f (append (list (negate (fact-b x)) (fact-a x)) (remove x stack)))
                              (if (prove-internal (negate (fact-a x)) (remove x stack))
                                  (prove-internal f (append (list (negate (fact-a x)) (fact-b x)) (remove x stack)))
                                  a))]
                   [(#f) (if (or
                              (and (equal? (fact-a f) (fact-a x))
                                   (equal? (fact-negated? f) (fact-negated? x)))
                              (prove-internal (negate x) (remove x stack))) ;; contradiction
                             #t
                             a)]
                   [else (error "unsupported relation")])))
           #f
           (remove-duplicates stack))) ;; otherwise it really blows up
  (define stack-or (if (empty? stack) (cons (fact #f #f #f #f) stack) (remove-duplicates stack))) ;; dummy stack forces tautology check to run at least once even with otherwise empty stack
  (if (prove-internal f stack-or)
      #t
      (let ((ors (foldl (λ (item l) (if (equal? (fact-relation item) #\|) (cons item l) l)) '() stack-or)))
        (if (empty? ors)
            #f
            (and (prove-internal f (cons (fact-a (first ors)) (remove (first ors) stack-or)))
                 (prove-internal f (cons (fact-b (first ors)) (remove (first ors) stack-or))))))))


(define (shell stack)
  (print-stack stack)
  (display "> ")
  (shell (logstack (string->list (read-line)) stack)))

(if (equal? (vector-length (current-command-line-arguments)) 0)
  (shell '())
  (run (vector-ref (current-command-line-arguments) 0)))

(values)

;; example programs writeen while trying to establish comutational class

;(run "AB %%%%%%%% (%@ %/(%@ CD)(B%CDE)$)%/(CDE)(ABCD)$") ;; take the parity of a number, represented in unary by a string of tautologies, while saving the number itself
;(run "%%%%%%% AB  @@ (%@ %/(CD)(BCD)$)B ") ;; divide a number by two (rounding up)

;; repeatedly print n mod 2, then divide it by two and repeat. allows us to encode binary data on the stack. (does crash on a one-length input)
;(run "AB %%%%%%%%%%%%%%%%%%%%%%%%%%%% ((%@ %/(%@ CD)(B%CDE)$)%/(CDE)(ABCDE)$ %/(*?CD)(%?CD)$ @@ (%@ %/(CD)(BCD)$)B @@%/~)")

;; as above, but keep some other useless stuff on the stack just to show that we can
;(run "YZ %%%% AB %%%%%% ((%@ %/(%@ CD)(B%CDE)$)%/(CDE)(ABCDE)$ %/(*?CD)(%?CD)$ @@(%@)Z@@ (%@ %/(CD)(BCD)$)B @@(%@)Z@@%/~)")

;; as above, but keep a count +1 for each no and -1 for each yes. breaks if there are more yesses than nos
;(run "YZ AB %%%%%%%%%% ((%@ %/(%@ CD)(B%CDE)$)%/(CDE)(ABCDE)$ %/(*? #@@@%(%@)Z@@$(%@)B%# CD)(%? @@%/(CD)(ZCD)$(%@)Z@@(%@)B CD)$ @@(%@)Z@@ (%@ %/(CD)(BCD)$)B @@(%@)Z@@%/~)")

;; recognise correctly nested brackets (including (()()), not just a^nb^n)
;; %%%%%%%%%%%%%%%%%%%%%%%%%%%%%: (()) - yes
;; %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%: ())) - no
;; %%%%%%%%%%%%%%%%%%%%%%%%%: ((() - no
;(run "YZ AB %%%%%%%%%%%%%%%%%%%%%%%%%%%%%: ((%@ %/(%@ CD)(B%CDE)$)%/(CDE)(ABCDE)$ %/(@@@%(%@)Z@@$(%@)B% CD)(@@%/(CD)(*?.)$(%@)Z@@(%@)B CD)$ @@(%@)Z@@ (%@ %/(CD)(BCD)$)B @@(%@)Z@@%/~) $$(*?.)%?")


;; brainfuck translation
;; A B C                                   {set up three-cell tape}
;; %                                       {+}
;; %/(ab)(%A(%B(C/ab)(Bab)$/ab)(Aab)$ab)$  {- (has to figure out which delimiter to put back)}
;; (%@)%A(%B(C/ab)(Bab)$/ab)(Aab)$@        {>} broken for nonzero dest cell(?)
;; >> is < on a looping three-cell tape
;; %(%/( ,,, %%ab)(%A(%B(C/ab)(Bab)$/ab)(Aab)$abc)$)  {[,,,]}
