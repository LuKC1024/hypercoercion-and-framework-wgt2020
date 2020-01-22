#lang racket
(require pict)
(require pict/convert)
(require slideshow/code)
(require file/convertible)

(define even-odd-pict
  (vl-append
   (code (define (even [n : Dyn]) : Dyn
           (if (= n 0) #t (odd (- n 1))))
         (define (odd [n : Int]) : Bool
           (if (= n 0) #f (even (- n 1)))))))

(write-bytes
 (convert even-odd-pict 'png-bytes)
 (open-output-file "even-odd.png"))