from sicp422_lazy_evaluator import install_rules, test_one

def test():
    # lcons the procedure equivalent for primitive cons, but supporting lazy pair and lazy list
    # lcons does not force input parameters, therefore it allows lazy evaluation
    # lcons is implemented via message-passing, it returns lazy pair as a procedure
    # it has operations: lst-ref, lst-display-topn, lst-map, lst-add, lst-scale
    shared_lib = '''
      (define (lcons a b)
        (lambda (op)
          (if (equal? op "car")
            a
            (if (equal? op "cdr")
              b '()))))
      (define (lcar p) (p "car"))
      (define (lcdr p) (p "cdr"))

      (define (lst-ref p n)
        (if (null? p)
          '()
          (if (= n 0) (lcar p)
            (lst-ref (lcdr p) (- n 1)))))

      (define (lst-display-topn p n)
        (define (lst-display-topn-iter q m)
          (if (not (or (= m 0) (null? q)))
            (begin
              (if (not (= m n)) (display " "))
              (begin
                (display (lcar q))
                (lst-display-topn-iter (lcdr q) (- m 1))))))
        (lst-display-topn-iter p n))

      (define (lst-map f p)
        (if (null? p)
          '()
          (lcons (f (lcar p)) (lazy (lst-map f (lcdr p))))))

      (define (lst-add p1 p2)
        (if (or (null? p1) (null? p2))
          '()
          (lcons (+ (lcar p1) (lcar p2)) (lazy (lst-add (lcdr p1) (lcdr p2))))))

      (define (lst-scale p s)
        (define (f x) (* x s))
        (lst-map f p))
    '''
    # infinite stream can be defined recursively via lazy
    # finite list and infinite stream share the same lst-scale function
    test_one(shared_lib + \
      '''
      (define ls-ints (lcons 1 (lcons 2 (lcons 3 (lcons 4 '())))))
      (define ls-evens (lst-scale ls-ints 2))
      (display "ls-evens: ")
      (lst-display-topn ls-evens 4)
      
      (newline)

      (define st-ones (lcons 1 (lazy st-ones)))
      (define st-ints (lcons 1 (lazy (lst-add st-ints st-ones))))
      (define st-evens (lst-scale st-ints 2))
      (display "st-evens: ")
      (lst-display-topn st-evens 4)
      ''',
      output='ls-evens: 2 4 6 8\nst-evens: 2 4 6 8',
      result='#<undef>'
    )
    # calculateing natural e, see sicp354_diff_equation.py
    # unfortunately, lst-ref recursion quickly results in "max stack depth exceeded"
    # that's why we can only use small steps, and cannot get very accurate
    # this can be solved either via tail call optimization, or iteration without procedure call
    # but I won't do that
    test_one(shared_lib + \
      '''
      (define (solve f y0 dt)
        (define y (lcons y0 (lazy (lst-add y (lst-scale dy dt)))))
        (define dy (lst-map f y))
        y)
      (define (f y) y)
      (define steps 50)
      (define st-e (solve f 1 (/ 1 steps)))
      (define e1 (lst-ref st-e steps))
      
      (display "e = ")
      (display e1)
      (and (> e1 2.69) (< e1 2.74))
      ''',
      result='#t'
    )

if __name__ == '__main__':
    install_rules()
    test()