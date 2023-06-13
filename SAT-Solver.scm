;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise 1


;; (list-of? A? v) Takes two arguments, 
;;The first argument, A?, is a predicate that can be applied to any value
;;The second argument, v, is an arbitrary μScheme value.
;;Then returns #t if v is a list of values, each of which satisfies A? 
;;and false otherwise

;; laws:
;; (list-of? A? '()) = #t
;; (list-of? A? (cons a as)) = (all? A? (cons a as))
;; (list-of? A? v) = #f, where v is not a list


(define list-of? (A? v)
        (if (null? v)
                #t
                (if (pair? v)
                        (all? A? v)
                        #f)))


        (check-assert (list-of? number? '()) )
        (check-assert (not (list-of? number? 1)) )
        (check-assert (list-of? number? '(1 2 3)) )
        (check-assert (not (list-of? number? '(1 #f 3))) )
        (check-assert (not (list-of? number? '(#t 2 3))) )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise 2

(record not [arg])
(record or  [args])
(record and [args])

;; (formula? x) Takes one argument x, an arbitrary μScheme value
;;Then returns #t if the value represents a Boolean formula and #f otherwise

;; laws:
;; (formula? x) = #t ,where x is a symbol
;; (formula? (make-not f)) = (formula? (not-arg)) 
;; (formula? (make-or fs)) = (list-of? formula? (or-args))
;; (formula? (make-and fs)) = (list-of? formula? (and-args))
;; (formula? x) = #f ,where x is not a symbol or a listed record

(define formula? (x) 
        (if (symbol? x)
                #t
                (if (not? x)
                        (formula? (not-arg x))
                        (if (or? x)
                                (list-of? formula? (or-args x))
                                        (if (and? x)
                                                (list-of? formula? (and-args x))
                                                        #f)))))

        
        (check-assert (formula? 'a) )
        (check-assert (not (formula? 1)) )
        (check-assert (formula? (make-not 'a)) )
        (check-assert ( not(formula? (make-not 1))) )
        (check-assert (formula? (make-or '(a b c))) )
        (check-assert (not (formula? (make-or '(a 2 c)))) )
        (check-assert (formula? (make-and '(a b c))) )
        (check-assert (not (formula? (make-and '(a 2 c)))) )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise 3


;; (eval-formula f env) Takes two arguments
;;The first agrmuent, f is a formula 
;;The second argument, env is a env(an association list)
;;Then if the formula f is satisfied in the given environment,
;;returns #t; otherwise, it returns #f

;; laws:
;;(eval-formula f env) = (find f env), where f is a symbol
;;(eval-formula (make-not f) env) = (not (find (not-arg) env))
;;(eval-formula (make-or fs) env) = (exists? (lambda(f)
;;                             (eval-formula f env)) fs) 
;;(eval-formula (make-and fs) env) = (all? (lambda(f) (eval-formula f env)) fs) 

(define eval-formula (f env)
  (if (symbol? f)
          (find f env)
          (if (not? f)
                  (not (find (not-arg f) env))
                  (if (or? f)
                          (exists? (lambda(f) (eval-formula f env)) (or-args f))
                          (if (and? f)
                                  (all? (lambda(f) (eval-formula f env)) 
                                                        (and-args f))
                                  #f)))))


        (val tester '((x #t) (y #f)))
        (check-assert (eval-formula 'x tester) )
        (check-assert (not (eval-formula 'y tester)) )
        (check-assert (eval-formula (make-not 'y) tester) )
        (check-assert (not (eval-formula (make-not 'x) tester)) )
        (check-assert (eval-formula (make-or '(x y)) tester) )
        (check-assert (not (eval-formula (make-or '(y y)) tester)) )
        (check-assert (eval-formula (make-and '(x x)) tester) )
        (check-assert (not (eval-formula (make-and '(x y)) tester)) )
      

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;  Exercise 4


;; (solve-sat f fail succ) Takes three arguments
;;The first argument, f a formula
;;The second argument, fail a failure continuation
;;The third argument, succ a success continuation
;;Then searches for a satisfying assignment—which is, a mapping of 
;;Boolean variables to Boolean values that makes the formula true and 
;;returns that


(define solve-sat (f fail succ) 
  (letrec      
    ([solve-formula    
      ;;(solve-formula f bool cur fail succeed) 
      ;;Takes in a formula f, a boolean bool, an assosiation list 
      ;;                        cur, a failure continuation fail,
      ;;and a success continuation succeed
      ;;Then extends assignment cur to find an assignment that 
      ;;                      makes the single f equal to bool
      ;;Returns nothing
      ;;Laws
      ;;(solve-formula x             bool cur fail succeed) == 
      ;;  (solve-symbol x bool cur fail succeed), where x is a symbol
      ;;(solve-formula (make-not f)  bool cur fail succeed) ==
      ;;          (solve-formula f not (bool) cur fail succeed)
      ;;(solve-formula (make-or  fs) #t   cur fail succeed) ==
      ;;                     (solve-any fs #t cur fail succeed) 
      ;;(solve-formula (make-or  fs) #f   cur fail succeed) ==
      ;;                     (solve-all fs #f cur fail succeed)
      ;;(solve-formula (make-and fs) #t   cur fail succeed) == 
      ;;                     (solve-all fs #t cur fail succeed)
      ;;(solve-formula (make-and fs) #f   cur fail succeed) == 
      ;;                     (solve-any fs #f cur fail succeed)    
        (lambda (f bool cur fail succeed) 
          (if (symbol? f)
            (solve-symbol f bool cur fail succeed)
              (if (not? f)
                (solve-formula (not-arg f) (not bool) cur fail succeed)
                (if (&&(or? f) bool)
                  (solve-any (or-args f) #t cur fail succeed)
                  (if (&&(or? f)(not bool))
                    (solve-all (or-args f) #f cur fail succeed)
                    (if (&&(and? f) bool)
                      (solve-all (and-args f) #t cur fail succeed)
                      (if (&&(and? f)(not bool))
                        (solve-any (and-args f) #f cur fail succeed)
                        (fail))))))))]
           [solve-all
          ;;(solve-all fs bool cur fail succeed)
          ;;Takes in a list of formulas fs, a boolean bool, an assosiation
          ;;                        list cur, a failure continuation fail,
          ;;and a success continuation succeed
          ;;Then extends cur to find an assignment that makes every
          ;;                   formula in the list fs equal to bool
          ;;Returns nothing
          ;;Laws:
          ;;(solve-all '()         bool cur fail succeed) == (succeed cur fail)
          ;;(solve-all (cons f fs) bool cur fail succeed) == (solve-formula
          ;;  f bool cur fail (lambda (cur resume) solve-all fs bool cur 
          ;;  resume succeed))
            (lambda (fs bool cur fail succeed)
              (if (null? fs)   
                (succeed cur fail)
                (solve-formula (car fs) bool cur fail
                ;;(Succeed cur resume)
                ;;Takes in an assosiation list cur, and a function resume
                ;;Assuming f is successful, calls solve-all again with the 
                ;;                                     rest of the list fs
                ;;Returns nothing   
                  (lambda (cur resume) (solve-all (cdr fs) bool cur resume
                                                             succeed)))))]
                  [solve-any
                ;;(solve-any fs bool cur fail succeed)
                ;;Takes in a list of formulas fs, a boolean bool, an 
                ;;  assosiation list cur, a failure continuation fail,
                ;;and a success continuation succeed
                ;;Then extends cur to find an assignment that makes any one
                ;;                                  of the fs equal to bool
                ;;Returns nothing
                ;;laws:
                ;;(solve-any '()         bool cur fail succeed) == (fail)
                ;;(solve-any (cons f fs) bool cur fail succeed) == (solve-
                ;;                          formula f bool cur (lambda () 
                ;;           solve-all fs bool cur fail succeed) succeed)
                   (lambda (fs bool cur fail succeed)
                     (if (null? fs)   
                       (fail)
                       (solve-formula (car fs) bool cur
                       ;;(fail)
                       ;;Takes no arguments
                       ;;Assuming f is unsuccessful, calls solve-all again
                       ;;                     with the rest of the list fs
                       ;;Returns nothing   
                         (lambda () (solve-any (cdr fs) bool cur fail 
                                                succeed)) succeed)))]
                   [solve-symbol
                ;;(solve-symbol x bool cur fail succeed)
                ;;Takes in a symbol x, a boolean bool, an assosiation list 
                ;;                       cur, a failure continuation fail,
                ;;and a success continuation succeed
                ;;Then if x is bound to bool in cur, succeeds with
                ;;    environment cur and resume continuation fail
                ;;If x is bound to (not bool) in cur, fails
                ;;If x is not bound in cur, extends cur with a binding of
                ;;            x to bool, then succeeds with the extended 
                ;;environment and continuation fail
                ;;Returns nothing
                ;;Laws:
                ;;(solve-symbol x bool cur fail succeed) == (succeed
                ;;  (bind x bool cur) fail), where x is not bound in cur
                ;;(solve-symbol x bool cur fail succeed) == (succeed cur
                ;;                         fail), where x is bool in cur
                ;;(solve-symbol x bool cur fail succeed) == (fail), where
                ;;                                x is (not bool) in cur
                    (lambda (x bool cur fail succeed)
                     (if (= (find x cur) '())
                       (succeed (bind x bool cur) fail)
                       (if (= (find x cur) bool)
                         (succeed cur fail)
                         (fail)        )))])
                           (solve-formula f #t '() fail succ)))
                        


        (check-assert (function? solve-sat)); correct name
        (check-error  (solve-sat)); not 0 arguments
        (check-error  (solve-sat 'x)); not 1 argument
        (check-error  (solve-sat 'x (lambda () 'fail))); not 2 args
        (check-error  (solve-sat 'x (lambda () 'fail) 
                        (lambda (c r)'succeed) 'z)); not 4 args

        (check-error (solve-sat 'x (lambda () 'fail) (lambda () 'succeed))) 
        ; success continuation expects 2 arguments, not 0
        (check-error (solve-sat 'x (lambda () 'fail) (lambda (_) 'succeed)))
        ; success continuation expects 2 arguments, not 1
        (check-error (solve-sat                                             
        ; failure continuation expects 0 arguments, not 1
                      (make-and (list2 'x (make-not 'x)))
                      (lambda (_) 'fail)
                      (lambda (_) 'succeed))) 

        (check-expect; x can be solved
         (solve-sat 'x (lambda () 'fail)
            (lambda (cur resume) 'succeed))
            'succeed)

        (check-expect; x is solved by '((x #t))
          (solve-sat 'x (lambda () 'fail)
            (lambda (cur resume) (find 'x cur)))
              #t)

        (check-expect; (make-not 'x) can be solved
         (solve-sat (make-not 'x)
             (lambda () 'fail)
             (lambda (cur resume) 'succeed))
              'succeed)

        (check-expect; (make-not 'x) is solved by '((x #f))
          (solve-sat (make-not 'x)
            (lambda () 'fail)
            (lambda (cur resume) (find 'x cur)))
              #f)

        (check-expect; (make-and (list2 'x (make-not 'x))) cannot be solved
          (solve-sat (make-and (list2 'x (make-not 'x)))
            (lambda () 'fail)
            (lambda (cur resume) 'succeed))
              'fail)

        (check-expect; (make-and '(x y z)) should succeed
          (solve-sat (make-and '(x y z))
            (lambda () 'fail)
            (lambda (cur resume) 'succeed))
              'succeed)

        (check-expect; or should succeed
          (solve-sat (make-or ( list2 'x (make-not 'x) ))
            (lambda () 'fail)
            (lambda (cur resume) 'succeed))
            'succeed)

        (check-expect; or should succeed
          (solve-sat (make-or (list2 (make-and (list2 'x (make-not 'x))) 
                                                      (make-not 'x)))
            (lambda () 'fail)
            (lambda (cur resume) 'succeed))
              'succeed)

        (check-expect; or should fail
          (solve-sat (make-or (list2 (make-and (list2 'x (make-not 'x))) 
                                 (make-and (list2 'x (make-not 'x))) ))
            (lambda () 'fail)
            (lambda (cur resume) 'succeed))
              'fail)

