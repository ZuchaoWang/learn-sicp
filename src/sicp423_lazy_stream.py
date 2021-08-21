from sicp422_lazy_evaluator import install_rules, test_one

def test():
    test_one(
      '''
      (define (lcons a b)
        (lambda (op)
          (if (equal? op "car")
            a
            (if (equal? op "cdr")
              b '()))))
      (define (lcar p) (p "car"))
      (define (lcdr p) (p "cdr"))

      (define (lst-display-topn p n)
        (define (lst-display-topn-iter q m)
          (if (not (or (= m 0) (null? q)))
            (begin
              (if (not (= m n)) (display " "))
              (begin
                (display (lcar q))
                (lst-display-topn-iter (lcdr q) (- m 1))))))
        (lst-display-topn-iter p n))

      (define (lst-add p1 p2)
        (if (or (null? p1) (null? p2))
          '()
          (lcons (+ (lcar p1) (lcar p2)) (lazy (lst-add (lcdr p1) (lcdr p2))))))

      (define (lst-scale p s)
        (if (null? p)
          '()
          (lcons (* (lcar p) s) (lazy (lst-scale (lcdr p) s)))))

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

if __name__ == '__main__':
    install_rules()
    test()