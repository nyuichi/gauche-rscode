(define-module rscode
  (use srfi-27)
  (export
    make-rscode
    rs-encode
    rs-decode
  ))

(select-module rscode)


(define (make-polynomial deg)
  (make-list (+ deg 1) 0))

(define (polynomial-deg poly)
  (- (length poly) 1))

(define (polynomial-copy poly)
  (list-copy poly))

(define (ref-polynomial poly i)
  (ref poly (- (polynomial-deg poly) i)))

(define (remove-first-zeros list)
  (if (null? list)
      list
      (if (zero? (car list))
	  (remove-first-zeros (cdr list))
	  list)))

(define (shrink-polynomial poly)
  (reverse (remove-first-zeros (reverse poly))))

(define (polynomial= poly1 poly2)
  (equal? (shrink-polynomial poly1)
	  (shrink-polynomial poly2)))

(define (get-real-deg poly)
  (- (length (shrink-polynomial poly)) 1))

(define (polynomial-zero? poly)
  (null? poly))



(define-class <galois-field-2> ()
  ((max-exp :init-keyword :max-exp)
   (exp2val :init-keyword :exp2val) 
   (val2exp :init-keyword :val2exp)))

(define (get-poly-from-n n)
  (case n
    ((3) #x03)
    ((4) #x03)
    ((8) #x1d)
    (else (error "Sorry, the specified field is not supported yet."))))

(define (init-galois-field-2 gf2 prim-poly)
  (let ((tmp 1))
    (dotimes (i (~ gf2 'max-exp))
	     (set! (~ gf2 'exp2val i) tmp)
	     (set! (~ gf2 'val2exp tmp) i)
	     (set! tmp (logxor (logand (ash tmp 1)
	     			       (~ gf2 'max-exp))
	     		       (if (zero? (logand tmp (ash (+ (~ gf2 'max-exp) 1) -1)))
	     			   0
	     			   prim-poly))))
    (set! (~ gf2 'val2exp 0) (~ gf2 'max-exp))))



(define (make-galois-field-2 n prim-poly)
  (let* ((max-exp (- (expt 2 n) 1))
	 (gf2 (make <galois-field-2>
		:max-exp max-exp
		:exp2val (make-list max-exp 0)
		:val2exp (make-list (+ max-exp 1) 0))))
    (init-galois-field-2 gf2 prim-poly)
    gf2))


(define (gf2-add gf2 . rest)
  (apply logxor rest))

(define (gf2-mul gf2 a b)
  (if (or (zero? a) (zero? b))
      0
      (let* ((exp2val (~ gf2 'exp2val))
	     (val2exp (~ gf2 'val2exp))
	     (max-exp (~ gf2 'max-exp))
	     (index (mod (+ (~ val2exp a) (~ val2exp b)) max-exp)))
	(~ exp2val index))))

(define (gf2-pow gf2 a exp)
  (if (zero? a)
      0
      (begin (set! exp (mod exp (~ gf2 'max-exp)))
	     (let* ((exp2val (~ gf2 'exp2val))
		    (val2exp (~ gf2 'val2exp))
		    (max-exp (~ gf2 'max-exp))
		    (index (mod (* (~ val2exp a) exp) max-exp)))
	       (~ exp2val index)))))

(define (gf2-div gf2 a b)
  (if (zero? a)
      0
      (if (zero? b)
	  (error "divide by zero")
	  (let* ((exp2val (~ gf2 'exp2val))
		 (val2exp (~ gf2 'val2exp))
		 (max-exp (~ gf2 'max-exp))
		 (index (mod (- (~ val2exp a) (~ val2exp b)) max-exp)))
	    (~ exp2val index)))))

(define (gf2-pow-a gf2 exp)
  (~ gf2 'exp2val (mod exp (~ gf2 'max-exp))))

(define (gf2-log-a gf2 val)
  (~ gf2 'val2exp val))

(define (add-offset offset list)
  (if (zero? offset)
      list
      (add-offset (- offset 1) (cons 0 list))))

(define (max-length-polys lists)
  (apply max (map length lists)))

(define (expand-poly list n)
  (if (null? list)
      (make-list n 0)
      (cons (car list)
	    (expand-poly (cdr list) (- n 1)))))

(define (expand-polys lists)
  (let ((len (max-length-polys lists)))
    (map (lambda (lst) (expand-poly lst len)) lists)))

(define (gf2-mul-poly gf2 a b)
  (apply map (lambda rest (apply gf2-add gf2 rest))
	 (expand-polys
	  (map (lambda (j offset)
		 (add-offset offset (map (lambda (i) (gf2-mul gf2 i j)) a)))
	       b
	       (iota (+ (polynomial-deg b) 1))))))

(define (gf2-divmod-poly gf2 a b)
  (let ((real-b-deg (get-real-deg b)))
    (when (< real-b-deg 0)
	  (error "Devide by zero poly"))
    (let ((denominator (~ b real-b-deg))
	  (q (make-polynomial (- (polynomial-deg a) real-b-deg)))
	  (r (polynomial-copy a)))
      (do ((i (polynomial-deg q) (- i 1)))
	  ((< i 0))
	(set! (~ q i) (gf2-div gf2 (~ r (+ i real-b-deg)) denominator))
	(do ((j 0 (+ j 1)))
	    ((> j real-b-deg))
	  (set! (~ r (+ i j)) (gf2-add gf2 (~ r (+ i j)) (gf2-mul gf2 (~ b j) (~ q i))))))
      (values q r))))

(define (gf2-div-poly gf2 a b)
  (receive (q r) (gf2-divmod-poly gf2 a b)
	   q))

(define (gf2-mod-poly gf2 a b)
  (receive (q r) (gf2-divmod-poly gf2 a b)
	   r))

(define (gf2-add-poly gf2 . rest)
  (apply map (lambda args (apply gf2-add gf2 args)) (expand-polys rest)))

(define (gf2-dif-poly gf2 a)
  (let ((ans (make-polynomial (polynomial-deg a))))
    (do ((i 1 (+ i 2)))
	((> i (polynomial-deg a)))
      (set! (~ ans (- i 1)) (~ a i)))
    ans))

(define (gf2-calc-poly gf2 a b)
  (apply gf2-add gf2 (map (lambda (c i) (gf2-mul gf2 c (gf2-pow gf2 b i))) a (iota (+ (polynomial-deg a) 1)))))

(define (get-generator-polynomial-for-rs gf2 error-words)
  (fold (lambda (i s)
	  (gf2-mul-poly gf2 s (list (gf2-pow-a gf2 i)
				    (gf2-pow-a gf2 0))))
	(list 1)
	(iota error-words)))

(define-syntax swap!
  (syntax-rules ()
    ((_ a b)
     (let ((tmp a))
       (set! a b)
       (set! b tmp)))))

(define (gf2-solve-key-equation gf2 a b)
  (let ((m (polynomial-copy a))
	(n (polynomial-copy b))
	(x (list 0))
	(y (list 1)))
    (when (< (get-real-deg m) (get-real-deg n))
	  (swap! n m))
    (while (and (not (polynomial-zero? n))
		(>= (get-real-deg n) (get-real-deg y)))
	   (receive (q r) (gf2-divmod-poly gf2 m n)
		    (let ((z (gf2-add-poly gf2 (gf2-mul-poly gf2 q y) x)))
		      (set! x y)
		      (set! y z)
		      (set! m n)
		      (set! n r))))
    (let ((h (list (car y))))
      (values (gf2-div-poly gf2 y h)
	      (gf2-div-poly gf2 n h)))))

(define-class <rscode> ()
  ((gf2         :init-keyword :gf2)
   (g           :init-keyword :g)
   (num-total-words :init-keyword :num-total-words)
   (num-data-words  :init-keyword :num-data-words)
   (num-error-words :init-keyword :num-error-words)))

(define (make-rscode num-total-words num-data-words :optional (gf2-exp 8) (gf2-prim-poly #f))
  (let* ((gf2 (make-galois-field-2 gf2-exp (or gf2-prim-poly (get-poly-from-n gf2-exp))))
         (num-error-words (- num-total-words num-data-words))
         (g   (get-generator-polynomial-for-rs gf2 num-error-words)))
    (make <rscode>
          :gf2 gf2
          :g g
          :num-total-words num-total-words
          :num-data-words  num-data-words
          :num-error-words num-error-words)))


(define (rs-encode rscode data-words)
  ;; TODO: check data-words size
  (let* ((gf2 (~ rscode 'gf2))
         (I (add-offset (~ rscode 'num-error-words) (map (cut gf2-pow-a gf2 <>) (reverse data-words))))
         (g (~ rscode 'g)))
    (gf2-add-poly gf2 (gf2-mod-poly gf2 I g) I)))


(define (rs-decode rscode encoded-words)
  ;;
  (let* ((gf2 (~ rscode 'gf2))
         (r (polynomial-copy encoded-words))
         (num-total-words (~ rscode 'num-total-words))
         (num-error-words (~ rscode 'num-error-words))
         (s (map (lambda (i) (gf2-calc-poly gf2 r (gf2-pow-a gf2 i)))
                 (iota num-error-words)))
         (z (add-offset num-error-words '(1))))
;    (print "syndrome:" s)
    (receive (sigma omega) (gf2-solve-key-equation gf2 z s)
;      (print "sigma:" sigma)
;      (print "omega:" omega)
      (let* ((x (list 0 1))
             (denom (gf2-mul-poly gf2 x (gf2-dif-poly gf2 sigma))))
;        (print "denom:" denom)
        (dotimes (i (- num-total-words 1))
          (when (zero? (gf2-calc-poly gf2 sigma (gf2-pow-a gf2 (- (~ gf2 'max-exp) i))))
            (set! (~ r i) (gf2-add gf2 (~ r i)
                                   (gf2-div gf2
                                            (gf2-calc-poly gf2 omega (gf2-pow-a gf2 (- (~ gf2 'max-exp) i)))
                                            (gf2-calc-poly gf2 denom (gf2-pow-a gf2 (- (~ gf2 'max-exp) i))))))))))
;    (drop r num-error-words)))
    (map (cut gf2-log-a gf2 <>) (reverse (drop r num-error-words)))))

