use "structureFLX.sml";

open Flx;

(* Sample terms *)
val t1 = VAR "abc";
val t2 = Z;
val t3 = F;
val t4 = ITE (t3,t1,t2);

val t5 = fromInt 4;
val t6 = fromInt ~3;

(* Test cases for fromInt and toInt *)
(*val resultint1 = (case (toInt t5) of 
                        4 => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle _ => (print "Incorrect\n"; false);

val resultint2 = (case (toInt t6) of 
                        ~3 => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle _ => (print "Incorrect\n"; false);

val resultInt3 = (case (toInt t4) of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_int => (print "correct\n"; true)
                        handle _ => (print "Incorrect\n"; false);

val resultInt4 =  (case (toInt (S (S (Z)))) of 
                        2 => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle _ => (print "Incorrect\n"; false);*)


(* Test cases for fromString *)
val resultstring1 = (case (fromString "a") of 
                        (VAR "a") => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val resultstring2 = (case (fromString "abcd efgh") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val resultstring3 = (case (fromString "(ITE <F,abc,Z>)") of 
                        ITE (F, VAR("abc"), Z) => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val resultstring4 = (case (fromString "(S (S Z))") of 
                        S (S (Z)) => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);


(* Test cases for toString *)
(* Make sure to properly parenthesize the constructor applications and use 
angular brackets for ITE in your output string *)
(* Do not print VAR for variable names in the output string *)
(*val resultstring5 = (case (toString t1) of 
                        "abc" => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false));

val resultstring6 = (case (toString t2) of 
                        "Z" => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false));

val resultstring7 = (case (toString t4) of 
                        "(ITE <F,abc,Z>)" => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false));*)

(* Test cases for normalize *)
(*val t9 = P (S Z);
val resultnorm1 = (case (normalize t9) of 
                Z => (print "Correct\n"; true)
                | _ => (print "incorrect\n"; false));*)


(* mJ testcases *)
(* Not Wellformed *)
val temp = (case (fromString "(abcdefgh") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "abcdefgh>") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "abcd,efgh") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "()") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "(S  a)") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "(ITE <a,a,a,>)") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "( ITE <a,a,a>)") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "(ITE <a,a ,a>)") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "(ITE <a,a,,a>)") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "(ITE <a,a,a>>)") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

val temp = (case (fromString "(ITE <a,a,(a)>)") of 
                        _ => (print "Incorrect\n"; false))
                        handle Not_wellformed  => (print "Correct\n"; true);

(* Valid fromString 
val temp = (case (fromString "(ITE <(ITE <Z,Z,Z>),Z,Z>)") of 
                        ITE (ITE (Z,Z,Z),Z,Z) => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val temp = (case (fromString "(ITE <(ITE <(S (S (P Z))),Z,(GTZ a)>),(IZ (S a)),as>)") of 
                        ITE ( (ITE ( (S (S (P Z))) , Z , (GTZ (VAR "a")) )) , (IZ (S (VAR "a"))) , (VAR "as")) => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);
*)
(* Normalize *)
(*val temp = IZ (ITE ((S (S (S Z))),(S (S (S Z))),(P (P Z))))
val temp1 = (case (normalize temp) of 
                        F => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val temp = ITE ( (IZ (VAR "a")), (GTZ (VAR "a")), (IZ (VAR "a")) )
val temp1 = (case (normalize temp) of 
                        F => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val temp = ITE ( (GTZ (VAR "a")), (IZ (VAR "a")), (GTZ (VAR "a")) )
val temp1 = (case (normalize temp) of 
                        F => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val temp = ITE ( (GTZ (VAR "a")), (GTZ (VAR "a")), (GTZ (VAR "a")) )
val temp1 = (case (normalize temp) of 
                        (GTZ (VAR "a")) => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);

val temp = IZ (S (ITE ( (VAR "a"), (P Z), (S (P (P Z))) )))
val temp1 = (case (normalize temp) of 
                        T => (print "correct\n"; true)
                        | _ => (print "Incorrect\n"; false))
                        handle Not_wellformed => (print "Incorrect\n"; false);*)

