



-------------------------------- MODULE test --------------------------------

EXTENDS Integers



VARIABLE y,x,pc



Init == y \in 1..5 /\ x=0 /\ pc = "L1"



Next1 == pc = "L1" /\ x' = y /\ y' = y /\ pc' = "L2"



Next2 == pc = "L2" /\ x' = x + 1 /\ y' = y /\ pc'= "L3"



Next3 == pc = "L3" /\ x' = x /\ y' = x /\ pc' = "Done"



Next == Next1 \/ Next2 \/ Next3



=============================================================================

\* Modification History

\* Last modified Sat May 25 15:45:31 CST 2019 by 10222446

\* Created Sat May 25 09:38:06 CST 2019 by 10222446





\* =等号不是赋值，就是数学里面的等于

\* ==是定义，定义Next1

\* /=不等于

\* ==宏定义，using, 替代

\* <<>>tuple,数组\

\* Finish: 这个是语句标签，goto用的

\* := 赋值语句

\*        final := final + Head(dqueue); 取头的值

\*        dqueue := Tail(dqueue); 去掉头部

\* |-> 定义域到值域的映射

\* Agatin: 标签，用于goto， label

\* fair process永远不会失败的process

\* \union求并集

