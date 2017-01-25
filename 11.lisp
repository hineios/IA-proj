;Alterações necessárias devido a união de entregas
#|procura-a
	procura-g
	pcua
	pcug|#

(defmacro while (test do &body body)
  "Execute body while the test is true."
  (assert (eq do 'do))
  `(do () ((not ,test) nil) ,@body))

(defmacro for-each (var in list do &body body)
  "Execute body for each element of list.  VAR can be a list or tree
  of variables, in which case the elements are destructured."
  (assert (eq in 'in)) (assert (eq do 'do))
  (typecase var
    (symbol `(dolist (,var ,list) ,@body))
    (cons (let ((list-var (gensym)))
	    `(dolist (,list-var ,list)
	       (destructuring-bind ,var ,list-var ,@body))))
    (t (error "~V is an illegal variable in (for each ~V in ~A ...)"
	      var list))))

(defmacro for (var = start to end do &body body)
  "Execute body with var bound to succesive integers."
  (cond ((eq var 'each) ; Allow (for each ...) instead of (for-each ...)
	 `(for-each ,= ,start ,to ,end ,do ,@body))
	(t (assert (eq = '=)) (assert (eq to 'to)) (assert (eq do 'do))
	   (let ((end-var (gensym "END")))
	     `(do ((,var ,start (+ 1 ,var)) (,end-var ,end))
		  ((> ,var ,end-var) nil)
		,@body)))))

(defmacro deletef (item sequence &rest keys &environment env)
  "Destructively delete item from sequence, which must be SETF-able."
  (multiple-value-bind (temps vals stores store-form access-form)
      (get-setf-expansion sequence env)
    (assert (= (length stores) 1))
    (let ((item-var (gensym "ITEM")))
    `(let* ((,item-var ,item)
	    ,@(mapcar #'list temps vals)
	    (,(first stores) (delete ,item-var ,access-form ,@keys)))
      ,store-form))))

(defmacro define-if-undefined (&rest definitions)
  "Use this to conditionally define functions, variables, or macros that
  may or may not be pre-defined in this Lisp.  This can be used to provide
  CLtL2 compatibility for older Lisps."
  `(progn
     ,@(mapcar #'(lambda (def)
		   (let ((name (second def)))
		     `(when (not (or (boundp ',name) (fboundp ',name)
				     (special-form-p ',name)
				     (macro-function ',name)))
		       ,def)))
	       definitions)))


;;; -*- Mode: Lisp; Syntax: Common-Lisp; -*- File: utilities/queue.lisp

;;;; The Heap Implementation of Priority Queues

;;; The idea is to store a heap in an array so that the heap property is
;;; maintained for all elements: heap[Parent(i)] <= heap[i].  Note that we
;;; start at index 0, not 1, and that we put the lowest value at the top of
;;; the heap, not the highest value.

;; These could be made inline

(defun heap-val (heap i key) (declare (fixnum i)) (funcall key (aref heap i)))
(defun heap-parent (i) (declare (fixnum i)) (floor (- i 1) 2))
(defun heap-left (i) (declare (fixnum i)) (the fixnum (+ 1 i i)))
(defun heap-right (i) (declare (fixnum i)) (the fixnum (+ 2 i i)))

(defun heapify (heap i key)
  "Assume that the children of i are heaps, but that heap[i] may be 
  larger than its children.  If it is, move heap[i] down where it belongs.
  [Page 143 CL&R]."
  (let ((l (heap-left i))
	(r (heap-right i))
	(N (- (length heap) 1))
	smallest)
    (setf smallest (if (and (<= l N) (<= (heap-val heap l key)
					 (heap-val heap i key)))
		       l i))
    (if (and (<= r N) (<= (heap-val heap r key) (heap-val heap smallest key)))
	(setf smallest r))
    (when (/= smallest i)
      (rotatef (aref heap i) (aref heap smallest))
      (heapify heap smallest key))))

(defun heap-extract-min (heap key)
  "Pop the best (lowest valued) item off the heap. [Page 150 CL&R]."
  (let ((min (aref heap 0)))
    (setf (aref heap 0) (aref heap (- (length heap) 1)))
    (decf (fill-pointer heap))
    (heapify heap 0 key)
    min))

(defun heap-insert (heap item key)
  "Put an item into a heap. [Page 150 CL&R]."
  ;; Note that ITEM is the value to be inserted, and KEY is a function
  ;; that extracts the numeric value from the item.
  (vector-push-extend nil heap)
  (let ((i (- (length heap) 1))
	(val (funcall key item)))
    (while (and (> i 0) (>= (heap-val heap (heap-parent i) key) val))
      do (setf (aref heap i) (aref heap (heap-parent i))
	       i (heap-parent i)))
    (setf (aref heap i) item)))

(defun make-heap (&optional (size 100))
  (make-array size :fill-pointer 0 :adjustable t))

(defun heap-sort (numbers &key (key #'identity))
  "Return a sorted list, with elements that are < according to key first."
  ;; Mostly for testing the heap implementation
  ;; There are more efficient ways of sorting (even of heap-sorting)
  (let ((heap (make-heap))
	(result nil))
    (for each n in numbers do (heap-insert heap n key))
    (while (> (length heap) 0) do (push (heap-extract-min heap key) result))
    (nreverse result)))


;;;; The Queue datatype

;;; We can remove elements form the front of a queue.  We can add elements in
;;; three ways: to the front, to the back, or ordered by some numeric score.
;;; This is done with the following enqueing functions, which make use of the
;;; following implementations of the elements:
;;;   ENQUEUE-AT-FRONT - elements are a list
;;;   ENQUEUE-AT-END   - elements are a list, with a pointer to end
;;;   ENQUEUE-BY-PRIORITY - elements are a heap, implemented as an array
;;; The best element in the queue is always in position 0.

;;; The heap implementation is taken from "Introduction to Algorithms" by
;;; Cormen, Lieserson & Rivest [CL&R], Chapter 7.  We could certainly speed
;;; up the constant factors of this implementation.  It is meant to be clear
;;; and simple and O(log n), but not super efficient.  Consider a Fibonacci
;;; heap [Page 420 CL&R] if you really have large queues to deal with.

(defstruct q
  (key #'identity)
  (last nil)
  (elements nil))

;;;; Basic Operations on Queues

(defun make-empty-queue () (make-q))

(defun empty-queue? (q)
  "Are there no elements in the queue?"
  (= (length (q-elements q)) 0))

(defun queue-front (q)
  "Return the element at the front of the queue."
  (elt (q-elements q) 0))

(defun remove-front (q)
  "Remove the element from the front of the queue and return it."
  (if (listp (q-elements q))
      (pop (q-elements q))
    (heap-extract-min (q-elements q) (q-key q))))

;;;; The Three Enqueing Functions

(defun enqueue-at-front (q items)
  "Add a list of items to the front of the queue."
  (setf (q-elements q) (nconc items (q-elements q))))

(defun enqueue-at-end (q items)
  "Add a list of items to the end of the queue."
  ;; To make this more efficient, keep a pointer to the last cons in the queue
  (cond ((null items) nil)
	((or (null (q-last q)) (null (q-elements q)))
	 (setf (q-last q) (last items)
	       (q-elements q) (nconc (q-elements q) items)))
	(t (setf (cdr (q-last q)) items
		 (q-last q) (last items)))))

(defun enqueue-by-priority (q items key)
  "Insert the items by priority according to the key function."
  ;; First make sure the queue is in a consistent state
  (setf (q-key q) key)
  (when (null (q-elements q))
    (setf (q-elements q) (make-heap)))
  ;; Now insert the items
  (for each item in items do
       (heap-insert (q-elements q) item key)))


;;;; PORBLEMA.LISP
;;;;
;;;;
;;;;
;;;;


(defstruct problema
	(estado-inicial nil)
	(solucao?)
	(accoes)
	(resultado)
	(custo-caminho)
	(heuristica-admissivel-inicial)
	(heuristica-admissivel)
	(heuristica-nao-admissivel-inicial)
	(heuristica-nao-admissivel)
	(heuristica-consistente-inicial)
	(heuristica-consistente))

(defun profundidade (estado) (length estado))

(defun faz-subtarefa (&key dia hora id)
	(list dia hora id))

(defun eq-subtarefa (subtarefa1 subtarefa2)
	(equal  subtarefa1 subtarefa2))

(defun eq-tarefa (tarefa1 tarefa2)
	(equal tarefa1 tarefa2))

(defun tarefas-repetidas (estado)
	(loop as tarefa in estado do
		(if (eq (rest estado) nil) nil)
		(if (member tarefa (rest estado) :test #'eq-tarefa)
			(return t))
		(setf estado (rest estado))))
		
(defun sobrepoe-subtarefa (subtarefa1 subtarefa2)
	(and 	(= (second subtarefa1) (second subtarefa2))
				(= (first subtarefa1) (first subtarefa2))
				(not (eq (third subtarefa1) (third subtarefa2)))))


(defun sobrepoe-tarefa (tarefa1 tarefa2)
	(let ((sobrepoe? NIL)
				(terminou? NIL))
		(loop as subtarefa1 in tarefa1 do
			(if terminou?
				(loop-finish)
			(loop as subtarefa2 in tarefa2 do
				(if terminou? 
					(loop-finish)
				(when (sobrepoe-subtarefa subtarefa1 subtarefa2)
					(setf sobrepoe? t
								terminou? t)
					(loop-finish))))))
		sobrepoe?))

(defun existe-estado (subtarefa estado)
	(loop as tarefa in estado do
		(loop as alternativa in tarefa do
			(if (equal subtarefa alternativa)
					(return t))))
	nil)

(defun mesma-tarefa (subtarefa tarefa)
	(loop as alternativa in tarefa do
		(loop as subtarefa1 in alternativa do
			(if (eq-subtarefa subtarefa subtarefa1)
				t))
	(return nil)))

(defun acede-custo-subtarefa (subtarefa)
	(+ (* (first subtarefa) 24) (second subtarefa)))

(defun acede-custo-tarefa (tarefa)
	(let ((custo-max 0)
				(custo-min (* 365 24))
				(custo 0))
		(loop as subtarefa in tarefa do
			(if (> (setf custo (acede-custo-subtarefa subtarefa)) custo-max)
				(setf custo-max custo))
			(if (< custo custo-min)
				(setf custo-min custo)))
		(cons custo-min custo-max)))

(defun verifica-alternativas-invalidas (alt1 alt2 pesquisa)
	(let ((sol? nil))
		(loop as tarefa in pesquisa do
	     (if (and (member alt1 tarefa :test #'eq-subtarefa) (member alt2 tarefa :test #'eq-subtarefa) (not (eq alt1 alt2))) 
					(setf sol? t)))
		sol?))

(defun make-initial-queue (problema funcao-fila)
  (let ((q (make-empty-queue))
		(accoes nil)
		(nos-gerados nil))
	(setf accoes (funcall (problema-accoes problema) (problema-estado-inicial problema)))
	(loop as accao in accoes do
		(setf nos-gerados (append nos-gerados (list (funcall (problema-resultado problema) accao (problema-estado-inicial problema))))))
    (funcall funcao-fila q nos-gerados)
    q))

(defun ordena-accoes (problema accoes)
	(let ((ordenada nil)
				(prox nil)
				(melhor-custo 10000)
				(custo-actual 0))
		(loop while (not (= (length accoes) (length ordenada))) do
			(loop as accao in accoes do
				(setf custo-actual (funcall (problema-custo-caminho problema) accao))
				(if (and (< custo-actual melhor-custo) (not (member accao ordenada :test #'eq-subtarefa)))
					(setf prox accao 
								melhor-custo custo-actual)))
			(setf ordenada (append (list prox) ordenada))
			(setf melhor-custo 10000))
		(setf ordenada (reverse ordenada))
		ordenada))

(defun heuristica-consistente (problema estado)
	(- (funcall (problema-heuristica-consistente-inicial problema)) (funcall (problema-heuristica-consistente problema) estado)))

(defun heuristica-admissivel (problema estado)
	(- (funcall (problema-heuristica-admissivel-inicial problema)) (funcall (problema-heuristica-admissivel problema) estado)))

(defun heuristica-nao-admissivel (problema estado)
	(- (funcall (problema-heuristica-nao-admissivel-inicial problema)) (funcall (problema-heuristica-nao-admissivel problema) estado)))

(defun ordena-heuristica (problema estados heuristica)
	(let ((ordenada nil)
				(prox nil) 
				(melhor-heuristica 10000)
				(heuristica-actual 0))		
			(loop as estado in estados do
				(setf heuristica-actual (funcall heuristica problema estado))
				(cond ((not (< heuristica-actual melhor-heuristica)) (setf ordenada (append (list estado) ordenada)))
							((equal prox nil) (setf prox estado melhor-heuristica heuristica-actual))
							(t (setf ordenada (append (list prox) ordenada) prox estado melhor-heuristica heuristica-actual))))
		(setf ordenada (append (list prox) ordenada))
		ordenada))	

(defun ordena-A* (problema estados heuristica)
	(let ((ordenada nil)
				(prox nil)
				(melhor-heuristica 10000)
				(heuristica-actual 0))
		(loop as estado in estados do
				(setf heuristica-actual (+ (funcall (problema-custo-caminho problema) estado) (funcall heuristica problema estado)))
				(cond ((not (< heuristica-actual melhor-heuristica)) (setf ordenada (append (list estado) ordenada)))
							((equal prox nil) (setf prox estado melhor-heuristica heuristica-actual))
							(t (setf ordenada (append (list prox) ordenada) prox estado melhor-heuristica heuristica-actual))))
		(setf ordenada (append (list prox) ordenada))
		ordenada))

(defun ordena-rbfs (problema filhos heuristica)
	(let ((ordenada nil)
				(prox nil)
				(melhor-heuristica 1000)
				(heuristica-actual 0))
		(loop while (not (= (length filhos) (length ordenada))) do
			(loop as filho in filhos do
				(setf heuristica-actual (+ (funcall (problema-custo-caminho problema) filho) (funcall heuristica problema filho)))
				(if (and (< heuristica-actual melhor-heuristica) (not (member filho ordenada :test #'(lambda (t1 t2) (equal t1 t2)))))
					(setf prox filho 
								melhor-heuristica heuristica-actual)))
			(setf ordenada (append (list prox) ordenada))
			(setf melhor-heuristica 10000))
		(setf ordenada (reverse ordenada))
		ordenada))

(defun expande (problema node)
	(let ((nos nil)
				(accoes (funcall (problema-accoes problema) node))
				(teste nil))
		(loop as accao in accoes do
			(setf teste (funcall (problema-resultado problema) accao node))
			(let ((sol? t))
				(loop as tarefa1 in teste do
					(loop as tarefa2 in teste do
						(if (sobrepoe-tarefa tarefa1 tarefa2)
							(setf sol? nil))))
				(if sol? (setf nos (append nos (list teste))))))
		nos))

(defun gera-heuristica (lista-tarefas)
    (declare (ignore lista-tarefas))
    #'heuristica-nao-admissivel)

(defun mesmas-subtarefas (tarefa1 tarefa2)
	(let ((sol? t))
		(loop as subtarefa in tarefa1 do
			(if (not(member subtarefa tarefa2 :test #'(lambda (st1 st2) (and (= (first st1) (first st2)) (= (second st1) (second st2)) (eq (third st1) (third st2))))))
					(setf sol? nil)))
		sol?))

(defun mesmas-tarefas (state1 state2)
	(let ((sol? t))
		(loop as estado in state1 do
			(if (not(member estado state2 :test #'(lambda (t1 t2) (and ( = (length t1) (length t2)) (mesmas-subtarefas t1 t2)))))
				(setf sol? nil)))
	sol?))

(defun fechado? (node closed)
		(let ((sol? nil))
			(dolist (estado closed)
				(if ( = (length estado) (length node))
							(if(mesmas-tarefas node estado)
								(setf sol? t))))
		sol?))

(defun dec-heuristica (menores heuristica)
	(cond ((null menores) heuristica)
				((member (car menores) (cdr menores) :test (lambda (t1 t2) (equal t1 t2))) (dec-heuristica (cdr menores) (1- heuristica)))
				(t (dec-heuristica (cdr menores) heuristica))))


#| Formulação que, a cada passo, apenas tenta executar uma tarefa|#
(defun formulacao-problema (l)
	(make-problema
		:solucao? #'(lambda (estado)
			(let ((sol? t)
						(terminou? NIL))
				(if (= (length l) (length estado))
					(loop as tarefa1 in estado do
						(loop as tarefa2 in estado do
							(if (sobrepoe-tarefa tarefa1 tarefa2)
								(setf sol? NIL
								      terminou? nil))
							(if (verifica-alternativas-invalidas tarefa1 tarefa2 l)
								(setf sol? NIL
								      terminou? t))))
					(setf sol? NIL))
				(if (tarefas-repetidas estado)
					(setf sol? nil))
				sol?))
		:accoes #'(lambda (estado) 
			(let ((accoes-aux nil)
						(proxima-tarefa? nil))
				(loop as tarefa in l do
					(setf accoes-aux nil
								proxima-tarefa? nil)
					(loop as alternativa in tarefa do
						(if (member alternativa estado :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn (setf proxima-tarefa? t)
											(loop-finish))
						(setf accoes-aux (append accoes-aux (list alternativa)))))
					(if (not proxima-tarefa?)
						(loop-finish)))
				accoes-aux))
		:resultado #'(lambda (accao estado) (append estado (list accao)))
		:custo-caminho #'(lambda (estado) 
		  (let ((custo 0)
						(exploradas nil))
				(loop as tarefa in estado do
					(loop as subtarefa in tarefa do
							(if (eq exploradas nil)
								(setf custo (1+ custo) exploradas (append exploradas (list subtarefa)))
							(if (not (member subtarefa exploradas :test #'eq-subtarefa))
								(setf custo (1+ custo)
											exploradas (append exploradas (list subtarefa)))	))))
				custo))
		:heuristica-admissivel-inicial #'(lambda ()
			(let ((heuristica 0)
						(menor 1000))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (< (length alternativa) menor)
							(setf menor (length alternativa))))
					(setf heuristica (+ heuristica menor) menor 1000))
				heuristica))
		:heuristica-admissivel #'(lambda (estado)
			(let ((valor 0)
						(menor 1000))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (< (length alternativa) menor)
									(setf menor (length alternativa))))
							(setf valor (+ valor menor) menor 1000)))))
				valor))
		:heuristica-nao-admissivel-inicial #'(lambda ()
			(let ((heuristica 0)
						(maior 0))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (> (length alternativa) maior)
							(setf maior (length alternativa))))
					(setf heuristica (+ heuristica maior) maior 0))
				heuristica))
		:heuristica-nao-admissivel #'(lambda (estado)
			(let ((valor 0)
						(maior 0))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (> (length alternativa) maior)
									(setf maior (length alternativa))))
							(setf valor (+ valor maior) maior 0)))))
				valor))
		:heuristica-consistente-inicial #'(lambda ()
			(let ((heuristica 0)
						(menor 1000)
						(menor-alternativa nil)
						(menores nil))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (< (length alternativa) menor)
							(setf menor (length alternativa) menor-alternativa alternativa)))
					(setf heuristica (+ heuristica menor) menor 1000 menores (append menores menor-alternativa)))
				(setf heuristica (dec-heuristica menores heuristica))
				heuristica))
		:heuristica-consistente #'(lambda (estado)
			(let ((heuristica 0)
						(menor 1000)
						(menor-alternativa nil)
						(menores nil))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (< (length alternativa) menor)
									(setf menor (length alternativa) menor-alternativa alternativa)))
							(setf heuristica (+ heuristica menor) menor 1000 menores (append menores menor-alternativa))))))
				(setf heuristica (dec-heuristica menores heuristica))
				heuristica))))

#| Formulação que, a cada passo, tenta executar todas as tarefas |#
(defun formulacao-problema1 (l)
	(make-problema 
		:solucao? #'(lambda (estado)
			(let ((sol? t)
						(terminou? NIL))
				(if (= (length l) (length estado))
					(loop as tarefa1 in estado do
						(loop as tarefa2 in estado do														
							(if (sobrepoe-tarefa tarefa1 tarefa2)
								(setf sol? NIL
								      terminou? nil))
							(if (verifica-alternativas-invalidas tarefa1 tarefa2 l)
								(setf sol? NIL
								      terminou? t))))
					(setf sol? NIL))
				(if (tarefas-repetidas estado)
					(setf sol? nil))
				sol?))
		:accoes #'(lambda (estado) 
			(let ((accoes nil))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(setf accoes (append accoes (list alternativa)))))
				(if (>= (length estado) (length l))
					(setf accoes nil))
				accoes))
		:resultado #'(lambda (accao estado) (append estado (list accao)))
		:custo-caminho #'(lambda (estado) 
		  (let ((custo 0)
						(exploradas nil))
				(loop as tarefa in estado do
					(loop as subtarefa in tarefa do
							(if (eq exploradas nil)
								(setf custo (1+ custo) exploradas (append exploradas (list subtarefa)))
							(if (not (member subtarefa exploradas :test #'eq-subtarefa))
								(setf custo (1+ custo)
											exploradas (append exploradas (list subtarefa)))	))))
				custo))
		:custo-caminho #'(lambda (estado) 
		  (let ((custo 0)
						(exploradas nil))
				(loop as tarefa in estado do
					(loop as subtarefa in tarefa do
							(if (eq exploradas nil)
								(setf custo (1+ custo) exploradas (append exploradas (list subtarefa)))
							(if (not (member subtarefa exploradas :test #'eq-subtarefa))
								(setf custo (1+ custo)
											exploradas (append exploradas (list subtarefa)))	))))
				custo))
		:heuristica-admissivel-inicial #'(lambda ()
			(let ((heuristica 0)
						(menor 1000))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (< (length alternativa) menor)
							(setf menor (length alternativa))))
					(setf heuristica (+ heuristica menor) menor 1000))
				heuristica))
		:heuristica-admissivel #'(lambda (estado)
			(let ((valor 0)
						(menor 1000))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (< (length alternativa) menor)
									(setf menor (length alternativa))))
							(setf valor (+ valor menor) menor 1000)))))
				valor))
		:heuristica-admissivel #'(lambda (estado)
			(let ((valor 0)
						(menor 1000))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (< (length alternativa) menor)
									(setf menor (length alternativa))))
							(setf valor (+ valor menor) menor 1000)))))
				valor))
		:heuristica-nao-admissivel-inicial #'(lambda ()
			(let ((heuristica 0)
						(maior 0))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (> (length alternativa) maior)
							(setf maior (length alternativa))))
					(setf heuristica (+ heuristica maior) maior 0))
				heuristica))
		:heuristica-nao-admissivel #'(lambda (estado)
			(let ((valor 0)
						(maior 0))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (> (length alternativa) maior)
									(setf maior (length alternativa))))
							(setf valor (+ valor maior) maior 0)))))
				valor))
		:heuristica-consistente-inicial #'(lambda ()
			(let ((heuristica 0)
						(menor 1000)
						(menor-alternativa nil)
						(menores nil))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (< (length alternativa) menor)
							(setf menor (length alternativa) menor-alternativa alternativa)))
					(setf heuristica (+ heuristica menor) menor 1000 menores (append menores menor-alternativa)))
				(setf heuristica (dec-heuristica menores heuristica))
				heuristica))
		:heuristica-consistente #'(lambda (estado)
			(let ((heuristica 0)
						(menor 1000)
						(menor-alternativa nil)
						(menores nil))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (< (length alternativa) menor)
									(setf menor (length alternativa) menor-alternativa alternativa)))
							(setf heuristica (+ heuristica menor) menor 1000 menores (append menores menor-alternativa))))))
				(setf heuristica (dec-heuristica menores heuristica))
				heuristica))))


#| Formulação que, a cada passo, tenta executar todas as tarefas que ainda não foram realizadas. |#
(defun formulacao-problema2 (l)
	(make-problema 
		:solucao? #'(lambda (estado)
			(= (length estado) (length l)))
		:accoes #'(lambda (estado) 
			(let ((accoes nil)
						(accoes-aux nil)
						(proxima-tarefa? nil))
				(loop as tarefa in l do
					(setf accoes-aux nil
								proxima-tarefa? nil)
					(loop as alternativa in tarefa do
						(if (member alternativa estado :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn (setf proxima-tarefa? t)
											(loop-finish))
						(setf accoes-aux (append accoes-aux (list alternativa)))))
					(if (not proxima-tarefa?)
						(setf accoes (append accoes accoes-aux))))
				accoes))
		:resultado #'(lambda (accao estado) (append estado (list accao)))
		:custo-caminho #'(lambda (estado) 
		  (let ((custo 0)
						(exploradas nil))
				(loop as tarefa in estado do
					(loop as subtarefa in tarefa do
							(if (eq exploradas nil)
								(setf custo (1+ custo) exploradas (append exploradas (list subtarefa)))
							(if (not (member subtarefa exploradas :test #'eq-subtarefa))
								(setf custo (1+ custo)
											exploradas (append exploradas (list subtarefa)))))))
				custo))
		:heuristica-admissivel-inicial #'(lambda ()
			(let ((heuristica 0)
						(menor 1000))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (< (length alternativa) menor)
							(setf menor (length alternativa))))
					(setf heuristica (+ heuristica menor) menor 1000))
				heuristica))
		:heuristica-admissivel #'(lambda (estado)
			(let ((valor 0)
						(menor 1000))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (< (length alternativa) menor)
									(setf menor (length alternativa))))
							(setf valor (+ valor menor) menor 1000)))))
				valor))
		:heuristica-admissivel #'(lambda (estado)
			(let ((valor 0)
						(menor 1000))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (< (length alternativa) menor)
									(setf menor (length alternativa))))
							(setf valor (+ valor menor) menor 1000)))))
				valor))
		:heuristica-nao-admissivel-inicial #'(lambda ()
			(let ((heuristica 0)
						(maior 0))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (> (length alternativa) maior)
							(setf maior (length alternativa))))
					(setf heuristica (+ heuristica maior) maior 0))
				heuristica))
		:heuristica-nao-admissivel #'(lambda (estado)
			(let ((valor 0)
						(maior 0))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (> (length alternativa) maior)
									(setf maior (length alternativa))))
							(setf valor (+ valor maior) maior 0)))))
				valor))
		:heuristica-consistente-inicial #'(lambda ()
			(let ((heuristica 0)
						(menor 1000)
						(menor-alternativa nil)
						(menores nil))
				(loop as tarefa in l do
					(loop as alternativa in tarefa do
						(if (< (length alternativa) menor)
							(setf menor (length alternativa) menor-alternativa alternativa)))
					(setf heuristica (+ heuristica menor) menor 1000 menores (append menores menor-alternativa)))
				(setf heuristica (dec-heuristica menores heuristica))
				heuristica))
		:heuristica-consistente #'(lambda (estado)
			(let ((heuristica 0)
						(menor 1000)
						(menor-alternativa nil)
						(menores nil))
				(loop as tarefa in l do
					(loop as tarefa-estado in estado do
						(if (member tarefa-estado tarefa :test #'(lambda (t1 t2) (equal t1 t2)))
							(progn(loop as alternativa in tarefa do
								(if (< (length alternativa) menor)
									(setf menor (length alternativa) menor-alternativa alternativa)))
							(setf heuristica (+ heuristica menor) menor 1000 menores (append menores menor-alternativa))))))
				(setf heuristica (dec-heuristica menores heuristica))
				heuristica))))


;;;; Algoritmos de procura em árvore em Espaço de Estados

(defun procura-a (problem queuing-fn)
	(let ((nodes (make-initial-queue problem queuing-fn))
				(node nil))
		(loop (if (empty-queue? nodes) (RETURN nil))
			(setq node (remove-front nodes))
			(if (funcall (problema-solucao? problem) node) 
				(RETURN node))
			(funcall queuing-fn nodes (expande problem node)))))


(defun procura-g (problem queuing-fn)
	(let ((nodes (make-initial-queue problem queuing-fn))
				(node nil)
				(fechados (list)))
		(loop (if (empty-queue? nodes) (RETURN nil))
			(setq node (remove-front nodes))
			(if (funcall (problema-solucao? problem) node) 
				(RETURN node))
			(if (not(fechado? node fechados))
				(progn (setf fechados (append fechados (list node)))(funcall queuing-fn nodes (expande problem node)))))))


(defun plpa (problema)
	(procura-a problema #'enqueue-at-end))

(defun plpg (problema)
	(procura-a problema #'enqueue-at-end))

(defun pppa (problema)
	(procura-a problema #'enqueue-at-front))

(defun pppg (problema)
	(procura-a problema #'enqueue-at-front))

(defun ppla (problema limite &optional (estado (problema-estado-inicial problema)))
	(cond ((funcall (problema-solucao? problema) estado) estado)
				((>= (profundidade estado) limite) nil)
				(t (loop as n in (expande problema estado) do
					(let ((solucao (ppla problema limite n)))
						(when solucao (RETURN solucao)))))))

(defun pplg (problema limite &optional (estado (problema-estado-inicial problema)))
	(let ((fechados nil))
		(cond ((funcall (problema-solucao? problema) estado) estado)
				((>= (profundidade estado) limite) nil)
				(t (loop as n in (expande problema estado) do
					(if(not (fechado? n fechados))
					(progn (setf fechados (append fechados n))
					(let ((solucao (ppla problema limite n)))
						(when solucao (RETURN solucao))))))))))

(defun ppia (problema)
	(loop for depth from 0 to 999999999 do
			(let ((solution (ppla problema depth)))
				(unless (eq solution nil) (RETURN solution)))))

(defun ppig (problema)
	(loop for depth from 0 to 999999999 do
			(let ((solution (pplg problema depth)))
				(unless (eq solution nil) (RETURN solution)))))

(defun pcua (problema &optional (estado (problema-estado-inicial problema)))
	(let ((accoes (expande problema estado)))
		(setf accoes (ordena-accoes problema accoes))
		(loop
			(cond ((funcall (problema-solucao? problema) estado) (return estado))
						((null accoes) (progn
														 (setf estado (butlast estado))
														 (return estado)))
						(t (setf estado (car accoes))
							 (setf accoes (cdr accoes))
							 (setf estado (pcua problema estado)))))))

(defun pcug (problema &optional (estado (problema-estado-inicial problema)))
	(let ((accoes (expande problema estado))
			  (fechados nil))
		(setf accoes (ordena-accoes problema accoes))
		(loop
			(cond ((funcall (problema-solucao? problema) estado) (return estado))
						((null accoes) (progn
														 (setf estado (butlast estado))
														 (return estado)))
						(t (setf estado (car accoes))
							 (setf accoes (cdr accoes))
							 (if (not (fechado? accoes fechados))
									(progn (append fechados (list (first accoes))) (setf estado (first accoes))))
							 (setf estado (pcua problema estado)))))))
				 
(defun pga (problema heuristica &optional (estado (problema-estado-inicial problema)))
	(let ((accoes (expande problema estado)))
		(setf accoes (ordena-heuristica problema accoes heuristica))
		(loop
			(cond ((funcall (problema-solucao? problema) estado) (return estado))
						((null accoes) (progn
														 (setf estado (butlast estado))
														 (return estado)))
						(t (setf estado (car accoes))
							 (setf accoes (cdr accoes))
							 (setf estado (pcua problema estado)))))))

(defun pgg (problema heuristica &optional (estado (problema-estado-inicial problema)))
	(let ((accoes (expande problema estado))
				(fechados nil))
		(setf accoes (ordena-heuristica problema accoes heuristica))
		(loop
			(cond ((funcall (problema-solucao? problema) estado) (return estado))
						((null accoes) (progn
														 (setf estado (butlast estado))
														 (return estado)))
						(t (setf estado (car accoes))
							 (setf accoes (cdr accoes))
							 (if (not (fechado? accoes fechados))
									(progn (append fechados (list (first accoes))) (setf estado (first accoes))))
							 (setf estado (pcua problema estado)))))))

(defun pA*a (problema heuristica &optional (estado (problema-estado-inicial problema)))
	(let ((accoes (expande problema estado)))
		(setf accoes (ordena-A* problema accoes heuristica))
		(loop
			(cond ((funcall (problema-solucao? problema) estado) (return estado))
						((null accoes) (progn
														 (setf estado (butlast estado))
														 (return estado)))
						(t (setf estado (car accoes))
							 (setf accoes (cdr accoes))
							 (setf estado (pcua problema estado)))))))

(defun pA*g (problema heuristica &optional (estado (problema-estado-inicial problema)))
	(let ((accoes (expande problema estado))
				(fechados nil))
		(setf accoes (ordena-A* problema accoes heuristica))
		(loop
			(cond ((funcall (problema-solucao? problema) estado) (return estado))
						((null accoes) (progn
														 (setf estado (butlast estado))
														 (return estado)))
						(t (setf estado (car accoes))
							 (setf accoes (cdr accoes))
							 (if (not (fechado? accoes fechados))
									(progn (append fechados (list (first accoes))) (setf estado (first accoes))))
							 (setf estado (pcua problema estado)))))))

(defun rbfs (problema heuristica &optional (estado (problema-estado-inicial problema)) (melhor-alt 100000))
	(let ((accoes (expande problema estado)))
		(setf accoes (ordena-rbfs problema accoes heuristica))
		(loop
			(cond ((funcall (problema-solucao? problema) estado) (return estado))
						((or (null accoes) (> (funcall heuristica problema (car accoes)) melhor-alt)) (progn
																																								 (setf estado (butlast estado))
																																								 (return estado)))
						(t (setf estado (car accoes))
							 (setf accoes (cdr accoes))
							 (setf estado (rbfs problema heuristica estado (funcall heuristica problema (cadr accoes)))))))))


;;;; CSP


(defstruct csp
	(variaveis)
	(dominio)
	(restricoes))

(defun alldiff (estado)
	(cond ((null estado) t)
				((member (car estado) (cdr estado) :test (lambda (t1 t2) (if (or (equal t1 0) (equal t2 0)) nil (equal t1 t2)))) nil)
				(t (alldiff (cdr estado)))))

(defun tarefas-iguais (estado tarefas)
	(let ((conta 0))
		(loop as tarefa in tarefas do
			(loop as alternativa in tarefa do
				(if (member alternativa estado :test (lambda (t1 t2) (if (or (equal t1 0) (equal t2 0)) nil (equal t1 t2))))
					(setf conta (1+ conta))))
				(if (> conta 1)
					(return t)
				(progn (setf conta 0) nil)))))
		
(defun tarefas-sobrepostas (estado)
	(cond ((null estado) nil)
				((member (car estado) (cdr estado) :test (lambda (t1 t2) (if (or (equal t1 0) (equal t2 0)) nil (sobrepoe-tarefa t1 t2)))) t)
				(t (tarefas-sobrepostas (cdr estado)))))

(defun variaveis-livres (estado)
	(member 0 estado))

(defun proxima-variavel (estado)
	(cond ((null estado) 0)
				((equal (car estado) 0) 0)
				(t (1+ (proxima-variavel (cdr estado))))))

(defun sem-solucao (estado)
	(cond ((null estado) t)
				((not (equal (car estado) 0)) nil)
				(t (sem-solucao (cdr estado)))))

(defun faz-csp (l)
	(make-csp
		:variaveis #'(lambda ()
									 (make-list (length l) :initial-element 0))
		:dominio #'(lambda ()
								 (let ((dominio nil))
									(loop as tarefa in l do
									 (setf dominio (append dominio tarefa)))
									 dominio))
		:restricoes #'(lambda (estado)
										(and (alldiff estado) (not (tarefas-iguais estado l)) (not (tarefas-sobrepostas estado))))))

(defun psr (csp &optional (estado (funcall (csp-variaveis csp))))
	(let ((dominio (funcall (csp-dominio csp)))
				(index (proxima-variavel estado)))
		(loop
			(cond ((and (funcall (csp-restricoes csp) estado) (not (variaveis-livres estado))) (return estado))
						((and (sem-solucao estado) (null dominio)) (return nil))
						((null dominio) (progn
															(setf (nth (1- (proxima-variavel estado)) estado) 0)
															(return estado)))
						((not (funcall (csp-restricoes csp) estado)) (setf dominio (cdr dominio)))
						(t (progn 
									(setf (nth index estado) (car dominio))
									(setf estado (psr csp estado))
									(setf dominio (cdr dominio))))))))
