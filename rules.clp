
(defrule update-time
?cur-time <- (current-time ?time)
(order (event-time ?new-time&:(neq ?time ?new-time)&:(< ?new-time 9999)))
(not (order (event-time ?any-time &:(< ?any-time ?new-time)))) ;jump to the time when the first event happens
=>
(retract ?cur-time)
(assert (current-time ?new-time)))


(defrule arrival-to-machine
(current-time ?time) ; the current time is the arrival time of the order
?order<-(order (number ?ordern) (units ?un) (location arrival) (event-time ?time) (process-plan ?first-operation $?rest-operation)) 
?machine<-(machine (number ?machn) (operation ?first-operation ?operation-time) (order-processing nil) (busy-time ?busyt)) ; the machine is open
(queue ?machn) ; the queue is empty
=>
;(printout t "Move order " ?ordern " to machine " ?machn " at time " ?time crlf)
(modify ?machine (order-processing ?ordern) (busy-time = (+ ?busyt (* ?un ?operation-time))))
(modify ?order (location machine) (event-time = (+ ?time (* ?un ?operation-time))) (process-plan $?rest-operation)))


(defrule arrival-to-queue
(current-time ?time) ; the current time is the arrival time of the order
?order<-(order (number ?ordern) (location arrival) (event-time ?time) (process-plan ?first-operation $?)) 
(not (machine (number ?machn) (operation ?first-operation ?operation-time) (order-processing nil))) ; the machine is occupied
?queue<-(queue ?machn $?orders) ; the queue may or may not be empty
(machine (number ?machn) (operation ?first-operation ?operation-time) (order-processing ?ordernow))
(order (number ?ordernow) (event-time ?time-low)) ; the time the machine becomes free
=>
;(printout t "Move order " ?ordern " to queue " ?machn " at time " ?time crlf)
(modify ?order (location queue) (event-time ?time-low))
(retract ?queue)
(assert (queue ?machn $?orders ?ordern)))


(defrule queue-to-machine
(current-time ?time) ; the current time is the time we anticipated an order would leave the queue
?order<-(order (number ?ordern) (units ?un) (location queue) (event-time ?time) (process-plan ?first-operation $?rest-operation))
(not (order (location machine) (event-time ?time))) ; no other order need to be removed from machine at this time
?machine<-(machine (number ?machn) (operation ?first-operation ?operation-time)  (order-processing nil) (busy-time ?busyt)) ;the machine is open
?queue<-(queue ?machn ?ordern $?orders) ; the order has been in the queue longer than any other order
=>
;(printout t "Move order " ?ordern " from queue " ?machn " to machine " ?machn " at time " ?time crlf)
(modify ?order (location machine) (event-time = (+ ?time (* ?un ?operation-time))) (process-plan $?rest-operation))
(modify ?machine (order-processing ?ordern) (busy-time = (+ ?busyt (* ?un ?operation-time))) )
(retract ?queue)
(assert (queue ?machn $?orders)))


(defrule queue-to-queue
(current-time ?time) ; the current time is the time we anticipated an order would leave the queue
?order<-(order (number ?ordern) (location queue) (event-time ?time) (process-plan ?first-operation $?rest-operation))
(not (order (location machine) (event-time ?time))) ; no other order need to be removed from machine at this time
(not (order (location arrival) (event-time ?time))) ; no other order arrives at this time
(machine (number ?machn) (operation ?first-operation ?operation-time) (order-processing ?ordernow) ) ; the machine is occupied
(order (number ?ordernow) (event-time ?time-low)) ; the time the machine becomes free
=>
; (printout t "Order " ?ordern " remains in queue " ?machn " at time " ?time crlf)
(modify ?order (event-time ?time-low)))


(defrule machine-to-queue
(declare (salience 1))
(current-time ?time) ; the current time is the time when an order's processing in a machine is finished
?order<-(order (number ?ordern) (location machine) (event-time ?time) (process-plan ?first-operation $?rest-operation)) ; the order has at least one additional operation to complete
?machine<-(machine (number ?machn) (order-processing ?ordern))
(not (and (order (number ?otherorder) (location machine) (event-time ?time) (process-plan $?))
	  (machine (number ?othermachine &:(< ?othermachine ?machn)) (order-processing ?otherorder)))) ; this is the lowest numbered machine with an order finishing at this time because the policy of first-come-first-serve
(machine (number ?othermachn) (operation ?first-operation ?operation-time))
?queue<-(queue ?othermachn $?orders)
=>
;(printout t "Move order " ?ordern " from machine " ?machn " to queue " ?othermachn " at time " ?time crlf)
(retract ?queue)
(assert (queue ?othermachn $?orders ?ordern))
(modify ?order (location queue)) ; the event-time will be changed in the situation queue-to-queue or queue-to-machine
(modify ?machine (order-processing nil)))


(defrule machine-to-leave
(current-time ?time) ; the current time is the time when an order's processing in a machine is finished
?order<-(order (number ?ordern) (location machine) (event-time ?time) (process-plan) (actual-ship-time nil)); the order has no more operation to complete
?machine<-(machine (number ?machn) (order-processing ?ordern))
(not (and (order (number ?otherorder) (location machine) (event-time ?time))
	  (machine (number ?othermachine &:(< ?othermachine ?machn)) (order-processing ?otherorder))))
=>
;(printout t "Order " ?ordern " leaves machine " ?machn " with all operations completed" crlf)
(modify ?order (location depart) (event-time 9999) (actual-ship-time ?time)) ; set event-time to a flag value of 9999
(modify ?machine (order-processing nil)))


(defrule machine-utilization-report
(declare (salience 1))
(current-time ?time&:(< ?time 9999)) ; the current time when all the orders have leave the machine
(not (order (event-time ?ordert&:(< ?ordert 9999))))
=>
(printout t crlf crlf " MACHINE UTILIZATION REPORT :" crlf crlf)
(format t "%-9s| %-9s| %-9s" Machine# Busy-Time Idle-Time) 
(printout t crlf)
)

(defrule idle-time
(current-time ?time) ; the current time when all the orders have leave the machine
(not (order (event-time ?ordert&:(< ?ordert 9999))))
?machine <-(machine (number ?machn) (busy-time ?busyt) (idle-time ?idlet&:(= ?idlet 0)))
(not (machine (number ?anothern&:(< ?anothern ?machn)) (idle-time 0)))
=>(modify ?machine (idle-time =(- ?time ?busyt)))
(format t "%-9d| %-9d| %-9d" ?machn ?busyt (- ?time ?busyt))
(printout t crlf))
;(printout t " Machine " ?machn "'s busy time is " ?busyt " , and its idle time is " (- ?time ?busyt) "." crlf))


(defrule set-current-time
?cur <-(current-time ?time&:(< ?time 9999))
(not (machine (idle-time ?idlet&:(= 0 ?idlet))))
=>
(retract ?cur)
(assert (current-time 9999)))

(defrule shipped-orders-report
(declare (salience 1))
(current-time 9999)
=>
(printout t crlf crlf " SHIPPED ORDERS REPORT :" crlf crlf)
(format t "%-9s| %-16s| %-16s" Order# Actual-Ship-Time Scheduled-Ship-Time) 
(printout t crlf))


(defrule scheduled-actual-ship-time
(current-time 9999)
?order<- (order (number ?ordern&:(< ?ordern 9999)) (location depart) (actual-ship-time ?actualt) (scheduled-ship-time ?schedt))
(not (order (number ?anothern&:(< ?anothern ?ordern)) (location depart)))
=>
(modify ?order (number 9999))
(format t "%-9d| %-16d| %-16d" ?ordern ?actualt ?schedt)
(printout t crlf))
;(printout t "The order " ?ordern "'s actual ship time is " ?actualt " while its scheduled ship time is " ?schedt " ." crlf))

