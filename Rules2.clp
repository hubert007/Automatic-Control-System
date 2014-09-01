(defrule update-time
?cur-time <- (current-time ?time)
(order (event-time ?new-time&:(neq ?time ?new-time)&:(< ?new-time 9999)))
(not (order (event-time ?any-time &:(< ?any-time ?new-time)))) 
=>
;jump to the time when the first event happens
(retract ?cur-time)
(assert (current-time ?new-time))) 

(defrule update-idle-until-time
;if a  machine is idle until current time updates, the machine's idle-until time should be updated, too. and this should be the executed before any other executions.
(declare (salience 1))
(current-time ?time)
?machine<-(machine (idle-until ?utime&:(< ?utime ?time)))
=>
(modify ?machine (idle-until ?time)))

(defrule discard-order-with-0-unit
;When executing other rules, it may produce order with 0 uinits. We need to discard this kind of order
?order<-(order (currentunits 0))
=>
(retract ?order))


(defrule arrival-to-machine
; the current time is the arrival time of the order
(current-time ?time)
; the processing time of the first operation of the order    
(define ?first-operation ?optime)      
?order<-(order (number ?ordern) (currentunits ?un&:(> ?un 0)) (location arrival) (event-time ?time) (process-plan ?first-operation $?rest-operation))

(not (order (number ?fordern&:(< ?fordern ?ordern)) (event-time ?time)))

; the machine that can process the first-operation directly is open
?machine<-(machine (number ?machn)(currentop ?first-operation) (status idle) (idle-until ?utime) (busy-time ?btime))
; the queue is empty
(queue ?machn) 
=>
; when the order contains multi units , split it into two parts, and process one unit a time
(modify ?order (location machine ?machn) (currentunits 1) (event-time = (+ ?time ?optime)) (process-plan $?rest-operation)) 
(modify ?order (currentunits (- ?un 1)))
(modify ?machine (status busy) (idle-until =(+ ?time ?optime)) (busy-time (+ ?btime ?optime))))




(defrule  arrival-to-queue-need-converting
; the current time is the arrival time of the order
(current-time ?time) 
?order<-(order (number ?ordern)(currentunits ?un&:(> ?un 0)) (location arrival) (event-time ?time) (process-plan ?first-operation $?rest-operation))
; the machine that become idle earliest need switching time before processing the order
?machine<-(machine (number ?machn)(switchingtime $?others1 ?first-operation ?stime $?others2)(idle-until ?utime) (busy-time ?btime))

(not (order (number ?fordern&:(< ?fordern ?ordern)) (event-time ?time)))

;if the machine's queue is empty, its current opertaion is diffrent from the first-operation of the order
(or 
  (and 
     (machine (number ?machn)(currentop ?operation&:(neq ?operation ?first-operation)))
     (queue ?machn))

;if the machine's queue is not empty, the last order's opertaion in the queue is different from the first-operation of the order
  (and 
     (queue ?machn $?orders ?order1)
     (order (number ?order1) (location queue ?machn)(event-time ?etime) (process-plan ?op&:(neq ?op ?first-operation) $?rests))
     (not (order (number ?order1) (location queue ?machn) (event-time ?oetime&:(> ?oetime ?etime))))))

; the time when other machines become idle is late than that of the machine we choose disregard of the possible switiching time
(not
	(machine (number ?othern1)(idle-until ?itime1&:(< ?itime1 ?utime))))



; if there are several machines that become idle at the same time, and they are the ealiest ones,  we choose the one with smallest switching time or smallest switching number
;there is no machine that has smaller switching time than the machine we choose if there idle-until time is the same.
(not 
	(machine (number ?nothern1) (switchingtime $?notherns1 ?first-operation ?noptime1&:(< ?noptime1 ?stime) $? notherns11) (idle-until ?nitime1&:(= ?nitime1 ?utime))))

;there is no machine that has smaller number than the machine we choose if the idle-until time and the switching time is the same.

(not 
	(machine (number ?nothern2&:(< ?nothern2 ?machn)) (switchingtime $?notherns2 ?first-operation ?noptime2&:(= ?noptime2 ?stime) $? notherns21) (idle-until ?nitime2&:(= ?nitime2 ?utime))))

; there is no machine that can process the order directly when it is the order's turn when the idle-until time is the same.

(not    (and
	(machine (number ?nothern3) (currentop ?first-operation) (idle-until ?nitime3&:(= ?nitime3 ?utime)))
        (queue ?nothern3)))

(not    (and
	(machine (number ?nothern4) (idle-until ?nitime4&:(= ?nitime4 ?utime)))
	(queue ?nothern4 $?ods4 ?lastod)
	(order (number ?lastod) (location queue ?nothern4) (event-time ?lasttime) (process-plan ?first-operation $?lastops))
	(not (order(number ?lastod)(location queue ?nothern4)(event-time ?alasttime&:(> ?alasttime ?lasttime))))))

;the queue can be either empty or not
?queue<-(queue ?machn $?ods)
(define ?first-operation ?optime)
=>
;split orders, and the event time of the order with one unit is the time when the machine finish converting
(modify ?order (currentunits 1) (location queue ?machn) (event-time ?utime) )
(modify ?order (currentunits =(- ?un 1)))
(modify ?machine (idle-until = (+ ?utime (+ ?optime ?stime))))
(retract ?queue)
(assert (queue ?machn $?ods ?ordern)))




(defrule  arrival-to-queue-process-directly
; the current time is the arrival time of the order
(current-time ?time) 
?order<-(order (number ?ordern) (currentunits ?un&:(> ?un 0)) (location arrival) (event-time ?time) (process-plan ?first-operation $?rest-operation))
; the machine can process the order directly when it become idle

(not (order (number ?fordern&:(< ?fordern ?ordern)) (event-time ?time)))
?machine<-(machine (number ?machn)(status ?st&:(neq ?st idle))(idle-until ?utime) (busy-time ?btime))

;if the machine's queue is empty, its current opertaion is the same as the first-operation of the order
(or 
(and 
(machine (number ?machn)(currentop ?first-operation))
(queue ?machn))



;if the machine's queue is not empty, the last order's opertaion in the queue is the same as the first-operation of the order
(and 
(queue ?machn $?orders ?order1)
(order (number ?order1) (location queue ?machn)(event-time ?etime) (process-plan ?first-operation $?rests))
(not (order (number ?order1) (location queue ?machn) (event-time ?oetime&:(> ?oetime ?etime))))))

; the time when other machines become idle is late than that of the machine we choose disregard of the possible switiching time
(not
	(machine (number ?othern1)(idle-until ?itime1&:(< ?itime1 ?utime))))



; if there are several machines that become idle at the same time, and they are the ealiest ones,  we choose the smallest machine number.
; there is no machine that has a samller number than the machine we choose, and has the same idle-until time, and can process the order directly when it is the order's turn

(not    (and
	(machine (number ?nothern3&:(< ?nothern3 ?machn)) (currentop ?first-operation) (idle-until ?nitime3&:(= ?nitime3 ?utime)))
        (queue ?nothern3)))

(not    (and
	(machine (number ?nothern4&:(< ?nothern4 ?machn)) (idle-until ?nitime4&:(= ?nitime4 ?utime)))
	(queue ?nothern4 $?ods4 ?lastod)
	(order (number ?lastod) (location queue ?nothern4) (event-time ?lasttime) (process-plan ?first-operation $?lastops))
	(not (order(number ?lastod)(location queue ?nothern4)(event-time ?alasttime&:(> ?alasttime ?lasttime))))))


;the queue can be either empty or not
?queue<-(queue ?machn $?ods)
(define ?first-operation ?optime)
=>
;split orders, and the event time of the order with one unit is the time when the machine finish converting
(modify ?order  (currentunits 1)(location queue ?machn) (event-time ?utime) )
(modify ?order (currentunits =(- ?un 1)))
(modify ?machine (idle-until = (+ ?optime ?utime )))
(retract ?queue)
(assert (queue ?machn $?ods ?ordern)))


(defrule queue-to-machine
; the current time is the time an order is anticipated to leave the machine or the machine finishes converting. the machine can now process the first operation of the order directly

(current-time ?time)

?machine<-(machine (number ?machn) (currentop ?first-operation)(status ?s&:(neq ?s busy))(busy-time ?btime))


; the order has been in the queue longer than any other orders
?queue<-(queue ?machn ?ordern $?rests)

?order<-(order (number ?ordern) (location queue ?machn) (event-time ?time) (process-plan ?first-operation $?restop))



(not (order (number ?fordern&:(< ?fordern ?ordern))(location queue ?whatqueue) (event-time ?time)))


(define ?first-operation ?optime)
=>
(modify ?machine (status busy) (busy-time =(+ ?btime ?optime)))
(modify ?order (location machine ?machn) (event-time =(+ ?time ?optime)) (process-plan ?restop))
(retract ?queue)
(assert (queue ?machn $?rests)))


(defrule queue-to-queue
;the current time is the time an order is anticipated to leave the machine. and the machine needs converting before processing the next order
(current-time ?time)
?machine <- (machine (number ?machn) (currentop ?diffop) (switchingtime $?others1 ?first-operation ?stime $?others2)(status idle) (busy-time ?btime))
?order<-(order (number ?ordern) (location queue ?machn) (event-time ?time)
(process-plan ?first-operation&:(neq ?first-operation ?diffop) $?restop))
=>
(modify ?machine(currentop ?first-operation) (status switch) (busy-time =(+ ?btime ?stime)))
(modify ?order (event-time =(+ ?time ?stime))))




(defrule machine-to-machine
(declare (salience 1))
(current-time ?time)
?lmachine<-(machine (number ?lmachn) (status busy))
?order<-(order (number ?ordern) (location machine ?lmachn) (event-time ?time) (process-plan ?first-operation $?restop))
; the machine can process the order directly when it become idle
?machine<-(machine (number ?machn) (currentop ?first-operation) (status idle)(idle-until ?utime) (busy-time ?btime))
(queue ?machn)
(define ?first-operation ?optime)
=>
(modify ?lmachine(status idle))
(modify ?order (location machine ?machn) (event-time =(+ ?time ?optime))(process-plan $?restop))
(modify ?machine(status busy) (idle-until =(+ ?time ?optime))(busy-time =(+ ?btime ?optime))))





(defrule machine-to-queue-need-switching
; the order is put in queue again when its current operation has been finished. this should be done before processing the new arrival order which arrives at the same time. 
(declare (salience 1))
(current-time ?time)
?lmachine<-(machine (number ?lmachn) (status busy))
?order<-(order (number ?ordern) (location machine ?lmachn) (event-time ?time) (process-plan ?first-operation $?restop))


?machine<-(machine (number ?machn&:(neq ?machn ?lmachn))(switchingtime $?others1 ?first-operation ?stime $?others2)(idle-until ?utime) (busy-time ?btime))

;(not (order (number ?exorder&:(< ?exorder ?ordern))(location machine ?amachn) (event-time ?time)))

;if the machine's queue is empty, its current opertaion is diffrent from the first-operation of the order
(or 
  (and 
	(machine (number ?machn)(currentop ?operation&:(neq ?operation ?first-operation)))
	(queue ?machn))

;if the machine's queue is not empty, the last order's opertaion in the queue is different from the first-operation of the order
  (and 
	(queue ?machn $?orders ?order1)
	(order (number ?order1) (location queue ?machn)(event-time ?etime) (process-plan ?op&:(neq ?op ?first-operation) $?rests))
	(not (order (number ?order1) (location queue ?machn) (event-time ?oetime&:(> ?oetime ?etime))))))

; the time when other machines become idle is late than that of the machine we choose disregard of the possible switiching time
(not
	(machine (number ?othern1)(idle-until ?itime1&:(< ?itime1 ?utime))))


; if there are several machines that become idle at the same time, and they are the ealiest ones,  we choose the one with smallest switching time or smallest switching number
;there is no machine that has smaller switching time than the machine we choose if there idle-until time is the same.
(not 
	(machine (number ?nothern1) (switchingtime $?notherns1 ?first-operation ?noptime1&:(< ?noptime1 ?stime) $? notherns11) (idle-until ?nitime1&:(= ?nitime1 ?utime))))

;there is no machine that has smaller number than the machine we choose if the idle-until time and the switching time is the same.

(not 
	(machine (number ?nothern2&:(< ?nothern2 ?machn)) (switchingtime $?notherns2 ?first-operation ?noptime2&:(= ?noptime2 ?stime) $? notherns21) (idle-until ?nitime2&:(= ?nitime2 ?utime))))

; there is no machine that can process the order directly when it is the order's turn when the idle-until time is the same.

(not    (and
	(machine (number ?nothern3) (currentop ?first-operation) (idle-until ?nitime3&:(= ?nitime3 ?utime)))
        (queue ?nothern3)))

(not    (and
	(machine (number ?nothern4) (idle-until ?nitime4&:(= ?nitime4 ?utime)))
	(queue ?nothern4 $?ods4 ?lastod)
	(order (number ?lastod) (location queue ?nothern4) (event-time ?lasttime) (process-plan ?first-operation $?lastops))
	(not (order(number ?lastod)(location queue ?nothern4)(event-time ?alasttime&:(> ?alasttime ?lasttime))))))

;the queue can be either empty or not
?queue<-(queue ?machn $?ods)
(define ?first-operation ?optime)
=>
(modify ?lmachine(status idle))
(modify ?order(location queue ?machn)(event-time ?utime))
(modify ?machine(idle-until =(+ ?utime (+ ?optime ?stime))))
(retract ?queue)
(assert (queue ?machn $?ods ?ordern)))



(defrule machine-to-original-queue-need-switching
; the order is put in queue again when its current operation has been finished. this should be done before processing the new arrival order which arrives at the same time. 
(declare (salience 1))
(current-time ?time)

?order<-(order (number ?ordern) (location machine ?machn) (event-time ?time) (process-plan ?first-operation $?restop))


?machine<-(machine (number ?machn)(switchingtime $?others1 ?first-operation ?stime $?others2)(idle-until ?utime) (busy-time ?btime))

;(not (order (number ?exorder&:(< ?exorder ?ordern)) (location machine ?amachn) (event-time ?time)))

;if the machine's queue is empty, its current opertaion is diffrent from the first-operation of the order
(or 
  (and 
	(machine (number ?machn)(currentop ?operation&:(neq ?operation ?first-operation)))
	(queue ?machn))

;if the machine's queue is not empty, the last order's opertaion in the queue is different from the first-operation of the order
  (and 
	(queue ?machn $?orders ?order1)
	(order (number ?order1) (location queue ?machn)(event-time ?etime) (process-plan ?op&:(neq ?op ?first-operation) $?rests))
	(not (order (number ?order1) (location queue ?machn) (event-time ?oetime&:(> ?oetime ?etime))))))

; the time when other machines become idle is late than that of the machine we choose disregard of the possible switiching time
(not
	(machine (number ?othern1)(idle-until ?itime1&:(< ?itime1 ?utime))))


; if there are several machines that become idle at the same time, and they are the ealiest ones,  we choose the one with smallest switching time or smallest switching number
;there is no machine that has smaller switching time than the machine we choose if there idle-until time is the same.
(not 
	(machine (number ?nothern1) (switchingtime $?notherns1 ?first-operation ?noptime1&:(< ?noptime1 ?stime) $? notherns11) (idle-until ?nitime1&:(= ?nitime1 ?utime))))

;there is no machine that has smaller number than the machine we choose if the idle-until time and the switching time is the same.

(not 
	(machine (number ?nothern2&:(< ?nothern2 ?machn)) (switchingtime $?notherns2 ?first-operation ?noptime2&:(= ?noptime2 ?stime) $? notherns21) (idle-until ?nitime2&:(= ?nitime2 ?utime))))

; there is no machine that can process the order directly when it is the order's turn when the idle-until time is the same.

(not    (and
	(machine (number ?nothern3) (currentop ?first-operation) (idle-until ?nitime3&:(= ?nitime3 ?utime)))
        (queue ?nothern3)))

(not    (and
	(machine (number ?nothern4) (idle-until ?nitime4&:(= ?nitime4 ?utime)))
	(queue ?nothern4 $?ods4 ?lastod)
	(order (number ?lastod) (location queue ?nothern4) (event-time ?lasttime) (process-plan ?first-operation $?lastops))
	(not (order(number ?lastod)(location queue ?nothern4)(event-time ?alasttime&:(> ?alasttime ?lasttime))))))

;the queue can be either empty or not
?queue<-(queue ?machn $?ods)
(define ?first-operation ?optime)
=>
(modify ?order(location queue ?machn)(event-time ?utime))
(modify ?machine(status idle)(idle-until =(+ ?utime (+ ?optime ?stime))))
(retract ?queue)
(assert (queue ?machn $?ods ?ordern)))




(defrule machine-to-queue-process-directly
; the order is put in queue again when its current operation has been finished. this should be done before processing the new arrival order which arrives at the same time. 
(declare (salience 1))
(current-time ?time)
?lmachine<-(machine (number ?lmachn) (status busy))
?order<-(order (number ?ordern) (location machine ?lmachn) (event-time ?time) (process-plan ?first-operation $?restop))


; the machine can process the order directly when it become idle
?machine<-(machine (number ?machn&:(neq ?machn ?lmachn))(status ?st&:(neq ?st idle))(idle-until ?utime) (busy-time ?btime))
;(not (order (number ?exorder&:(< ?exorder ?ordern)) (location machine ?machn) (event-time ?time)))


;if the machine's queue is empty, its current opertaion is the same as the first-operation of the order
(or 
  (and 
	(machine (number ?machn) (currentop ?first-operation))
	(queue ?machn))

;if the machine's queue is not empty, the last order's opertaion in the queue is the same as the first-operation of the order
 (and 
	(queue ?machn $?orders ?order1)
	(order (number ?order1) (location queue ?machn)(event-time ?etime) (process-plan ?first-operation $?rests))
	(not (order (number ?order1) (location queue ?machn) (event-time ?oetime&:(> ?oetime ?etime))))))

; the time when other machines become idle is late than that of the machine we choose disregard of the possible switiching time
(not
	(machine (number ?othern1)(idle-until ?itime1&:(< ?itime1 ?utime))))

; there is no machine that has a samller number than the machine we choose, and has the same idle-until time, and can process the order directly when it is the order's turn

(not    (and
	(machine (number ?nothern3&:(< ?nothern3 ?machn)) (currentop ?first-operation) (idle-until ?nitime3&:(= ?nitime3 ?utime)))
        (queue ?nothern3)))

(not    (and
	(machine (number ?nothern4&:(< ?nothern4 ?machn)) (idle-until ?nitime4&:(= ?nitime4 ?utime)))
	(queue ?nothern4 $?ods4 ?lastod)
	(order (number ?lastod) (location queue ?nothern4) (event-time ?lasttime) (process-plan ?first-operation $?lastops))
	(not (order(number ?lastod)(location queue ?nothern4)(event-time ?alasttime&:(> ?alasttime ?lasttime))))))


;the queue is not empty or not
?queue<-(queue ?machn $?ods)
(define ?first-operation ?optime)
=>
(modify ?lmachine(status idle))
(modify ?order (location queue ?machn)(event-time ?utime))
(modify ?machine(idle-until =(+ ?utime ?optime)))
(retract ?queue)
(assert (queue ?machn $?ods ?ordern)))





(defrule machine-to-original-queue-process-directly
; the order is put in queue again when its current operation has been finished. this should be done before processing the new arrival order which arrives at the same time. 
(declare (salience 1))
(current-time ?time)

?order<-(order (number ?ordern) (location machine ?machn) (event-time ?time) (process-plan ?first-operation $?restop))

; the machine can process the order directly when it become idle
?machine<-(machine (number ?machn)(status ?st&:(neq ?st idle))(idle-until ?utime) (busy-time ?btime))
;(not (order (number ?exorder&:(< ?exorder ?ordern)) (location machine ?amachn) (event-time ?time)))


;if the machine's queue is empty, its current opertaion is the same as the first-operation of the order
(or 
  (and 
	(machine (number ?machn) (currentop ?first-operation))
	(queue ?machn))

;if the machine's queue is not empty, the last order's opertaion in the queue is the same as the first-operation of the order
 (and 
	(queue ?machn $?orders ?order1)
	(order (number ?order1) (location queue ?machn)(event-time ?etime) (process-plan ?first-operation $?rests))
	(not (order (number ?order1) (location queue ?machn) (event-time ?oetime&:(> ?oetime ?etime))))))

; the time when other machines become idle is late than that of the machine we choose disregard of the possible switiching time
(not
	(machine (number ?othern1)(idle-until ?itime1&:(< ?itime1 ?utime))))

; there is no machine that has a samller number than the machine we choose, and has the same idle-until time, and can process the order directly when it is the order's turn

(not    (and
	(machine (number ?nothern3&:(< ?nothern3 ?machn)) (currentop ?first-operation) (idle-until ?nitime3&:(= ?nitime3 ?utime)))
        (queue ?nothern3)))

(not    (and
	(machine (number ?nothern4&:(< ?nothern4 ?machn)) (idle-until ?nitime4&:(= ?nitime4 ?utime)))
	(queue ?nothern4 $?ods4 ?lastod)
	(order (number ?lastod) (location queue ?nothern4) (event-time ?lasttime) (process-plan ?first-operation $?lastops))
	(not (order(number ?lastod)(location queue ?nothern4)(event-time ?alasttime&:(> ?alasttime ?lasttime))))))


;the queue is empty or not
?queue<-(queue ?machn $?ods)
(define ?first-operation ?optime)
=>
(modify ?order (location queue ?machn)(event-time ?utime))
(modify ?machine (status idle) (idle-until = (+ ?utime ?optime)))
(retract ?queue)
(assert (queue ?machn $?ods ?ordern)))




(defrule machine-to-assembling-without-other-units
(current-time ?time)
?order<-(order (number ?ordern) (originalunits ?un) (currentunits ?cun&:(< ?cun ?un)) (location machine ?machn) (event-time ?time)(process-plan))
?machine<-(machine (number ?machn) (status busy))
(not (order (number ?ordern) (location assemble)))
(not 
(and (order (number ?otherorder) (location machine ?othermachn) (event-time ?time))
(machine (number ?othermachn&:(< ?othermachn ?machn)) (status busy))))
=>
(modify ?order (location assemble) (event-time 9999))
(modify ?machine (status idle)))


(defrule machine-to-assembling-with-other-units
(current-time ?time)
?order<-(order (number ?ordern) (originalunits ?un) (currentunits ?cun&:(< ?cun ?un)) (location machine ?machn) (event-time ?time)(process-plan))
?machine<-(machine (number ?machn) (status busy))
?order1<-(order (number ?ordern) (currentunits ?cun1&:(< (+ ?cun ?cun1) ?un)) (location assemble))
(not 
(and (order (number ?otherorder) (location machine ?othermachn) (event-time ?time))
(machine (number ?othermachn&:(< ?othermachn ?machn)) (status busy))))
=>
(retract ?order)
(modify ?order1 (currentunits =(+ ?cun ?cun1)))
(modify ?machine (status idle)))


(defrule machine-to-depart-without-assemble
(current-time ?time)
; the order has no more operation to complete
?order<-(order (number ?ordern) (originalunits ?un) (currentunits ?un) (location machine ?machn) (event-time ?time) (actual-ship-time nil) (process-plan))
?machine<-(machine (number ?machn)(status busy))
(not 
(and (order (number ?otherorder) (location machine ?othermachn) (event-time ?time))
(machine (number ?othermachn&:(< ?othermachn ?machn)) (status busy))))
=>
; set event time to a flag value of 9999  when departing
(modify ?order (location depart) (event-time 9999) (actual-ship-time ?time))
(modify ?machine (status idle)))



(defrule machine-to-depart-with-assemble
(current-time ?time)
?order<-(order (number ?ordern) (originalunits ?un) (currentunits ?cun&:(< ?cun ?un)) (location machine ?machn) (event-time ?time)(actual-ship-time nil)(process-plan))
?machine<-(machine (number ?machn) (status busy))
?order1<-(order (number ?ordern) (currentunits ?cun1&:(= (+ ?cun ?cun1) ?un)) (location assemble))
(not 
(and (order (number ?otherorder) (location machine ?othermachn) (event-time ?time))
(machine (number ?othermachn&:(< ?othermachn ?machn)) (status busy))))
=>
(retract ?order)
(modify ?order1 (location depart)(currentunits ?un)(actual-ship-time ?time))
(modify ?machine (status idle)))


(defrule machine-utilization-report
(declare (salience 1))
(current-time ?time&:(< ?time 9999))
;all the order has been departed
(not (order (event-time ?ordert&:(< ?ordert 9999))))
=>
(printout t crlf crlf " MACHINE UTILIZATION REPORT :" crlf crlf)
(format t "%-9s| %-9s| %-9s| %-9s" Machine# Busy-Time Idle-Time Busy-Time-Percentage) 
(printout t crlf)
)



(defrule busy-idle-time
(current-time ?time)
(not (order (event-time ?ordert&:(< ?ordert 9999))))
?machine<-(machine (number ?machn) (busy-time ?btime) (idle-time ?itime&:(= ?itime 0)))
(not (machine (number ?anothern&:(< ?anothern ?machn)) (idle-time 0)))
=>
(modify ?machine (idle-time =(- ?time ?btime)))
(format t "%-9d| %-9d| %-9d| %-9f" ?machn ?btime (- ?time ?btime) (/ ?btime ?time))
(printout t crlf))

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
?order<- (order (number ?ordern&:(< ?ordern 9999)) (location depart) (actual-ship-time ?atime) (desired-ship-time ?dtime))
(not (order (number ?anothern&:(< ?anothern ?ordern)) (location depart)))
=>
(modify ?order (number 9999))
(format t "%-9d| %-16d| %-16d" ?ordern ?atime ?dtime)
(printout t crlf))















