use "signatureLAMBDAFLX.sml";

structure LambdaFlx : LAMBDAFLX = 
struct
  datatype lterm = term (* term from FLX *)
                   | VAR of string      (* variables *)
                   | Z                  (* zero *)
                   | T                  (* true *)
                   | F                  (* false *)
                   | P of lterm         (* Predecessor *)
                   | S of lterm         (* Successor *)
                   | ITE of lterm * lterm * lterm       (* If then else *)
                   | IZ of lterm        (* is zero *)
                   | GTZ of lterm       (* is greater than zero *)
                   | LAMBDA of lterm * lterm    (* lambda x [lterm] *)
                   | APP of lterm * lterm       (* application of lambda terms, i.e. (L M) *)
                                        
  exception Not_wellformed;
  exception Not_nf;
  exception Not_int;
  exception Not_welltyped;

  local
		fun to_char_list [] = []
			| to_char_list (h::t) = h::(to_char_list t);

		fun combine [] = []
				| combine ((#"Z")::tail) = ""::"Z"::(combine tail)
				| combine ((#"T")::tail) = ""::"T"::(combine tail)
				| combine ((#"F")::tail) = ""::"F"::(combine tail)
				| combine ((#"P")::tail) = ""::"P"::(combine tail)
				| combine ((#"S")::tail) = ""::"S"::(combine tail)
				| combine ((#"I")::(#"T")::(#"E")::tail)= "ITE"::(combine tail)
				| combine ((#"I")::(#"Z")::tail) = "IZ"::(combine tail)
				| combine ((#"G")::(#"T")::(#"Z")::tail) = "GTZ"::(combine tail)
				| combine ((#"L")::(#"A")::(#"M")::(#"B")::(#"D")::(#"A")::tail) = "LAMBDA"::(combine tail)
				| combine (h::tail) = 
					let val x = combine tail
					in if (h=(#"(") orelse h=(#")") orelse h=(#"[") orelse h=(#"]") orelse h=(#"<") orelse h=(#">") orelse h=(#","))
						then ""::Char.toString(h)::x
						else if (Char.isSpace h) then ""::x
						else if tail=[] then [Char.toString h] else (Char.toString(h)^List.hd(x))::List.tl(x)
					end;

		fun generateVar [] = []
				  	| generateVar (""::t) = generateVar t
				  	| generateVar (h::t) = (VAR h)::(generateVar t);

		fun str2term [] = []
				| str2term ((VAR "Z")::tail) = Z::(str2term tail)
				| str2term ((VAR "T")::tail) = T::(str2term tail)
				| str2term ((VAR "F")::tail) = F::(str2term tail)
				| str2term ((VAR " ")::tail) = str2term tail
				| str2term ((VAR "(")::(VAR "S")::(t:lterm)::(VAR ")")::tail) = S(List.hd(str2term[t]))::str2term(tail)
				| str2term ((VAR "(")::(VAR "P")::(t:lterm)::(VAR ")")::tail) = P(List.hd(str2term[t]))::str2term(tail)
				| str2term ((VAR "(")::(VAR "IZ")::(t:lterm)::(VAR ")")::tail) = IZ(List.hd(str2term[t]))::str2term(tail)
				| str2term ((VAR "(")::(VAR "GTZ")::(t:lterm)::(VAR ")")::tail) = GTZ(List.hd(str2term[t]))::str2term(tail)
				| str2term ((VAR "(")::(VAR "ITE")::(VAR "<")::(x:lterm)::(VAR ",")::(y:lterm)::(VAR ",")::(z:lterm)::(VAR ">")::(VAR ")")::tail) = 
					let
						val t1 = List.hd(str2term[x])
						val t2 = List.hd(str2term[y])
						val t3 = List.hd(str2term[z])
					in ITE((t1),(t2),(t3))::str2term(tail)
					end
				| str2term ((VAR "LAMBDA")::(VAR x)::(VAR "[")::(t:lterm)::(VAR "]")::tail) =(LAMBDA ((VAR x), List.hd(str2term[t])))::str2term(tail)
				| str2term ((VAR "(")::(t1:lterm)::(t2:lterm)::(VAR ")")::tail) = (APP (List.hd(str2term[t1]), List.hd(str2term[t2])))::str2term(tail)
				| str2term (h::tail) = h::(str2term tail);

		fun is_term [h] = h
						| is_term L = raise Not_wellformed;

		fun is_well_formed [] [] = true
			| is_well_formed L [] = false
			| is_well_formed [] L = false
			| is_well_formed (a::b) (c::d) = 
			if a=c then (is_well_formed b d) else false;

		fun parse [] = []
			| parse [h] = [h]
			| parse (h::tail) = 
				let val p = str2term (h::tail)
				in if (is_well_formed (h::tail) p) then raise Not_wellformed else (parse p)
				end;

		fun rename0 x (VAR t) count = if t=x then (VAR (t^(Int.toString count))) else (VAR t)
			| rename0 x (P t) count  = (P (rename0 x t count))
			| rename0 x (S t) count = (S (rename0 x t count))
			| rename0 x (IZ t) count = (IZ (rename0 x t count))
			| rename0 x (GTZ t) count = (GTZ (rename0 x t count))
			| rename0 x (ITE (t1,t2,t3)) count = (ITE ((rename0 x t1 count),(rename0 x t2 count),(rename0 x t3 count)))
			| rename0 x (APP (t1,t2)) count = (APP ((rename0 x t1 count),(rename0 x t2 count)))
			| rename0 x (LAMBDA (VAR t1,t2)) count = 
				if x=t1 then LAMBDA ((VAR (x^(Int.toString (count+1)))), (rename0 t1 t2 (count+1)))
				else 
					let val term1 = rename0 x t2 count
							val term2 = rename0 t1 term1 (count+1) 
					in term2 end
			(*| rename0 x (LAMBDA (_,_)) count = raise Not_wellformed*)
			| rename0 x t count = t;

		fun rename Z c = Z
			| rename T c = T
			| rename F c = F 
			| rename (VAR x) c = (VAR x)
			| rename (P x) c = (P (rename x c))
			| rename (S x) c = (S (rename x c))
			| rename (IZ x) c = (IZ (rename x c))
			| rename (GTZ x) c = (GTZ (rename x c))
			| rename (ITE (t1,t2,t3)) c = (ITE ((rename t1 c),(rename t2 c),(rename t3 c)))
			| rename (APP (t1,t2)) c = (APP ((rename t1 c),(rename t2 c)))
			| rename (LAMBDA (VAR x, y)) c = LAMBDA ((VAR (x^(Int.toString (c+1)))), (rename0 x y (c+1)))
			(*| rename (LAMBDA (_,_)) c = raise Not_wellformed*)
			| rename x c = x;

	in

		fun fromString x = 
			let val parsed = parse (generateVar (combine (to_char_list (String.explode x))))
					val t = is_term parsed
					val new_t = rename t 0
			in new_t end;
	end;

	datatype ltype = INT                (* int *)
                   | BOOL               (* bool *)
                   | TV of string
                   | STAR of ltype * ltype
                   | ARROW of ltype * ltype 


	local

	    (* takes a string variable and returns its type, if type is not present, 
	    	assigns it a new type and returns the list*)
	    fun findType x [] = ((TV (x^"0")), [(x, (TV (x^"0")))])
	    	| findType x ((x1,y)::t) = 
	    		if x=x1 then (y, ((x,y)::t)) else 
	    			let val (type1, list1) = findType x t in (type1, list1@((x1,y)::t))  end

	    fun assignType x [] t = [(x, t)]
	    	| assignType x ((x1,y)::tl) t =
	    		if x=x1 then (x,t)::tl else (x1,y)::(assignType x tl t)

	   	fun checkTypeVar (TV x) = true
	   		| checkTypeVar x = false

	   	fun checkTypeArrow (ARROW(b,x)) =  (true,b,x)
	   		| checkTypeArrow a = (false, a, a)
  in 
   	fun getType Z L = (INT, L)
    	| getType T L = (BOOL, L)
    	| getType F L = (BOOL, L)
    	| getType (VAR t) L = 
    		let val (type_t, list_t) = findType t L
    		in (type_t, list_t) end
    	| getType (P (VAR t)) L = 
	    	let val (currType, newL) = findType t L
	    	in if currType=INT then (INT, newL)
	    		else if (checkTypeVar currType) then 
	    			let val newnewL = assignType t newL INT
	    			in (INT, newnewL) end 
	    		else raise Not_welltyped 
	    	end
    	
    	| getType (P t) L = 
	    	let val (currType, newL) = getType t L
	    	in if currType=INT then (INT, newL) else raise Not_welltyped end
    	
    	| getType (S (VAR t)) L = 
	    	let val (currType, newL) = findType t L
	    	in if currType=INT then (INT, newL)
	    		else if (checkTypeVar currType) then 
	    			let val newnewL = assignType t newL INT
	    			 in (INT, newnewL) end 
	    		else raise Not_welltyped
	    	end

    	| getType (S t) L = 
	    	let val (currType, newL) = getType t L
	    	in if currType=INT then (INT, newL) else raise Not_welltyped end

    	| getType (IZ (VAR t)) L =
	    	let val (currType, newL) = findType t L
	    	in if currType=INT then (BOOL, newL)
	    		else if (checkTypeVar currType) then 
	    			let val newnewL = assignType t newL INT in (INT, newnewL) end 
	    		else raise Not_welltyped
	    	end

    	| getType (IZ t) L = 
	    	let val (currType, newL) = getType t L
	    	in if currType=INT then (BOOL, newL) else raise Not_welltyped end

    	| getType (GTZ (VAR t)) L =
	    	let val (currType, newL) = findType t L
	    	in if currType=INT then (BOOL, newL)
	    		else if (checkTypeVar currType) then 
	    			let val newnewL = assignType t newL INT in (INT, newnewL) end 
	    		else raise Not_welltyped
	    	end
	    	
    	| getType (GTZ t) L = 
	    	let val (currType, newL) = getType t L
	    	in if currType=INT then (BOOL, newL) else raise Not_welltyped end
    	
    	| getType (ITE (VAR t1,t2,t3)) L = 
    		let
    			val (type1, L1) = findType t1 L
    			val (type2, L2) = getType t2 L1
    			val (type3, L3) = getType t3 L2
    		in if (checkTypeVar type1) then 
    				let val newL = assignType t1 L3 BOOL
    				in if type2=type3 then (type2, newL) else raise Not_welltyped end
    			else if type1=BOOL andalso type2=type3 then (type2, L3)
    			else raise Not_welltyped
    		end

    	| getType (ITE (t1,t2,t3)) L = 
    		let
    			val (type1, L1) = getType t1 L
    			val (type2, L2) = getType t2 L1
    			val (type3, L3) = getType t3 L2
    		in if type1=BOOL andalso type2=type3 then (type2, L3)
    			else raise Not_welltyped
    		end
    	
    	| getType (LAMBDA (VAR x,t)) L = 
	    	let
	    		val (typex, newL) = findType x L
	    		val (typet, newnewL) = getType t newL
	    	in  (ARROW (typex, typet),newnewL) end

    	| getType (LAMBDA (t1,t2)) L = raise Not_wellformed

    	| getType (APP ((VAR x), (VAR y))) L = 
	    	let val (typex, Lx) = findType x L
	    		val (typey, Ly) = findType y Lx
	    		val (is_valid, x1, x2) = checkTypeArrow typex
	    	in 
	    		if typex=typey then raise Not_welltyped
	    		else if (checkTypeVar typex) andalso (checkTypeVar typey) then 
		    		let val newL = assignType x Ly (ARROW (typey, typex))
		    		in (typex, newL) end	
		    	else if is_valid andalso x1=typey then (x2, Ly)
		    	else if is_valid andalso (checkTypeVar typey) then 
		    		let val newnewL = assignType y Ly (x1)
		    		in (x2, newnewL) end
		    	else raise Not_welltyped
	    	end

    	| getType (APP ((VAR x), y)) L = 
	    	let val (typex, Lx) = findType x L
	    		val (typey, Ly) = getType y Lx
	    		val (is_valid, x1, x2) = checkTypeArrow typex
	    	in 
	    		if typex=typey then raise Not_welltyped
	    		else if (checkTypeVar typex) then 
		    		let val newL = assignType x Ly (ARROW (typey, typex))
		    		in (typex, newL) end	
		    	else if is_valid andalso x1=typey then (x2, Ly)
		    	else raise Not_welltyped
	    	end

    	| getType (APP (A, (VAR y))) L = 
    		let val (typea, La) = getType A L
    			val (typey, Ly) = findType y La
    			val (is_valid, a1, a2) = checkTypeArrow typea
    		in if typea=typey then raise Not_welltyped
    			else if is_valid andalso a1=typey then (a2, Ly)
    			else if is_valid andalso (checkTypeVar typey) then 
	    				let val newL = assignType y Ly a1
	    				in (a2, newL) end
	    		else raise Not_welltyped
    		end

    	| getType (APP (A,B)) L = 
	    	let
	    	 	val (typea, La) = getType A L
	    	 	val (typeb, Lb) = getType B La
	    	 	val (is_valid, b, x) = checkTypeArrow typea
	    	 in if typea=typeb then raise Not_welltyped
	    	 else if b=typeb then (x, Lb) else raise Not_welltyped end
    	| getType t L = raise Not_wellformed;

    fun isWellTyped0 Z = true
	  	| isWellTyped0 T = true
	  	| isWellTyped0 F = true
	  	| isWellTyped0 (VAR x) = true
	  	| isWellTyped0 (P t) = 
		  	let val (T1, L1) = getType t []
		  	in if T1=INT then true else raise Not_welltyped end
	  	| isWellTyped0 (S t) = 
		  	let val (T1, L1) = getType t []
		  	in if T1=INT then true else raise Not_welltyped end
			| isWellTyped0 (IZ t) = 
				let val (T1, L1) = getType t []
			  	in if T1=INT then true else raise Not_welltyped end
			| isWellTyped0 (GTZ t) = 
				let val (T1, L1) = getType t []
			  	in if T1=INT then true else raise Not_welltyped end
			| isWellTyped0 (ITE (t1,t2,t3)) = 
				let val (T1, L1) = getType (ITE (t1,t2,t3)) []
				in true end
			| isWellTyped0 (LAMBDA (VAR x, t)) = isWellTyped0 t
			| isWellTyped0 (APP (t1, t2)) = 
				let val (T1, L1) = getType (APP (t1, t2)) []
				in true	end
			| isWellTyped0 t = raise Not_wellformed;
  end;


  local

		fun sub (VAR x) (VAR y) M = if x=y then M else (VAR y)
			| sub (VAR x) (P y) M  = P (sub (VAR x) y M)
			| sub (VAR x) (S y) M = S (sub (VAR x) y M)
			| sub (VAR x) (IZ y) M = IZ (sub (VAR x) y M)
			| sub (VAR x) (GTZ y) M = GTZ (sub (VAR x) y M)
			| sub (VAR x) (ITE (t1, t2,t3)) M = ITE ((sub (VAR x) t1 M), (sub (VAR x) t2 M), (sub (VAR x) t3 M))
			| sub (VAR x) (LAMBDA (VAR y, z)) M = (LAMBDA (VAR y, (sub (VAR x) z M)))
			| sub (VAR x) (APP (y,z)) M = (APP ((sub (VAR x) y M), (sub (VAR x) z M)))
			| sub (VAR x) t M = t
	
		fun betanf0 Z = Z
			| betanf0 T = T
			| betanf0 F = F
			| betanf0 (VAR x) = (VAR x)
			| betanf0 (S (P x)) = 
				let val (t, l) = getType x []
				in if t=INT then betanf0 x else raise Not_welltyped end
			| betanf0 (P (S x)) =
				let val (t, l) = getType x []
				in if t=INT then betanf0 x else raise Not_welltyped end
			| betanf0 (P x) = P (betanf0 x)
			| betanf0 (S x) = S (betanf0 x)
			| betanf0 (IZ Z) = T
			| betanf0 (GTZ Z) = F
			| betanf0 (IZ x) = 
				let 
					val (type_x, _) = getType x []
					val t = betanf0 x
					fun normalize_itz (S n) = F
						| normalize_itz (P n) = F
						| normalize_itz x = IZ x
				in if type_x=INT then (normalize_itz t) else raise Not_welltyped end
			| betanf0 (GTZ x) = 
				let 
					val (type_x, _) = getType x []
					val t = betanf0 x;
					fun normalize_gtz (S n) = T
						| normalize_gtz (P n) = F
						| normalize_gtz x = GTZ x
				in if type_x=INT then (normalize_gtz t) else raise Not_welltyped end
			| betanf0 (ITE (T,x,y)) = betanf0 x
			| betanf0 (ITE (F,x,y)) = betanf0 y
			| betanf0 (ITE (t1,t2,t3)) = 
				let val (type_t1,_) = getType t1 []
				in if type_t1<>BOOL then raise Not_welltyped
					else if t2=t3 then betanf0 t2
					else 
						let 
							val x1 = betanf0 t1
							val x2 = betanf0 t2
							val x3 = betanf0 t3
						in (ITE (x1,x2,x3))
						end
				end
			| betanf0 (LAMBDA ((VAR x), y)) =  
				let val y_ = betanf0 y
				in LAMBDA ((VAR x), y_) end
			| betanf0 (APP ((LAMBDA ((VAR x),(VAR y))), M)) = if x=y then (betanf0 M) else (betanf0 (VAR y))
			| betanf0 (APP ((LAMBDA ((VAR x),y)), M)) = 
				let val M_ = betanf0 M
					val y_ = betanf0 y
					val s = (sub (VAR x) y_ M_) 
				in (betanf0 (betanf0 s)) end
			| betanf0 (APP (L, M)) =   APP ((betanf0 L), (betanf0 M))
			| betanf0 (LAMBDA (t0,t1)) = raise Not_wellformed
			| betanf0 x = raise Not_wellformed;

		in
			fun betanf t = 
				let val bnf_t = betanf0 t
					val is_lterm = (isWellTyped0 bnf_t)
				in
					if is_lterm then bnf_t else raise Not_wellformed
				end;
	end;

		fun isWellTyped t =
			let val bnf_t = (betanf t)
			in isWellTyped0 bnf_t end;	

  
  fun toString Z = "Z"
    | toString T = "T"
    | toString F = "F"
    | toString (P t) = ("(P " ^ (toString t)) ^ ")"
    | toString (S t) = ("(S " ^ (toString t)) ^ ")"
    | toString (ITE (t1,t2,t3)) = "(ITE <" ^ (toString t1) ^ "," ^ (toString t2) ^ "," ^ (toString t3)  ^ ">)"
    | toString (IZ t) = ("(IZ " ^ (toString t)) ^ ")"
    | toString (GTZ t) = ("(GTZ " ^ (toString t)) ^ ")"
    | toString (VAR t) = t
    | toString (LAMBDA (t0,t1)) = "LAMBDA " ^ (toString t0) ^ "[" ^ (toString t1) ^ "]"
    | toString (APP (t0,t1)) = "(" ^ (toString t0) ^ " " ^ (toString t1) ^ ")";


  local
    fun fromIntPos 0 = Z
      | fromIntPos n = S (fromIntPos (n-1))
    fun fromIntNeg 0 = Z
      | fromIntNeg n = P (fromIntNeg (n+1))
  in
    fun fromInt 0 = Z
      | fromInt n = 
      if n > 0 then fromIntPos n else fromIntNeg n
  end;


  local
    fun toIntS Z = 0
      | toIntS T = raise Not_int
      | toIntS F = raise Not_int
      | toIntS (VAR x) = raise Not_int
      | toIntS (GTZ x)= raise Not_int
      | toIntS (IZ x) = raise Not_int
      | toIntS (ITE (t1,t2,t3)) = raise Not_int
      | toIntS (LAMBDA (t1,t2)) = raise Not_int
      | toIntS (APP (t1,t2)) = raise Not_int
      | toIntS (P t) = raise Not_nf
      | toIntS (S t) = (toIntS t) + 1
    fun toIntP Z = 0
      | toIntP T = raise Not_int
      | toIntP F = raise Not_int
      | toIntP (VAR x) = raise Not_int
      | toIntP (GTZ x)= raise Not_int
      | toIntP (IZ x) = raise Not_int
      | toIntP (ITE (t1,t2,t3)) = raise Not_int
      | toIntP (LAMBDA (t1,t2)) = raise Not_int
      | toIntP (APP (t1,t2)) = raise Not_int
      | toIntP (S t) = raise Not_nf
      | toIntP (P t) = (toIntP t) - 1
  in
    fun toInt Z = 0
      | toInt (VAR x) = raise Not_int
      | toInt T = raise Not_int
      | toInt F = raise Not_int
      | toInt (GTZ x )= raise Not_int
      | toInt (IZ x) = raise Not_int
      | toInt (ITE (t1,t2,t3)) = raise Not_int
      | toInt (LAMBDA (t1,t2)) = raise Not_int
      | toInt (APP (t1,t2)) = raise Not_int
      | toInt (S t) = toIntS (S t)
      | toInt (P t) = toIntP (P t)
  end;


end;

(*open LambdaFlx;*)
(*fun sub (VAR x) (VAR y) M = if x=y then M else (VAR y)
	| sub (VAR x) (P y) M  = P (sub (VAR x) y M)
	| sub (VAR x) (S y) M = S (sub (VAR x) y M)
	| sub (VAR x) (IZ y) M = IZ (sub (VAR x) y M)
	| sub (VAR x) (GTZ y) M = GTZ (sub (VAR x) y M)
	| sub (VAR x) (ITE (t1, t2,t3)) M = ITE ((sub (VAR x) t1 M), (sub (VAR x) t2 M), (sub (VAR x) t3 M))
	| sub (VAR x) (LAMBDA (VAR y, z)) M = (LAMBDA (VAR y, (sub (VAR x) z M)))
	| sub (VAR x) (APP (y,z)) M = (APP ((sub (VAR x) y M), (sub (VAR x) z M)))
	| sub (VAR x) t M = t;*)
(*Control.Print.printDepth := 1024;
val x = VAR "x";
val y = VAR "y";
val z = VAR "z";
val t = LAMBDA (x, LAMBDA (y, LAMBDA (z, (APP (x, (APP (y,z)))))));
val t1 = APP (y,z);
val t2 = APP (x, APP (y,z));
val zero = LAMBDA (y, LAMBDA (x,x));
val suc = LAMBDA (z, (LAMBDA ((VAR "yy"), (LAMBDA ((VAR "xx"), (APP ((APP (z,(VAR "yy"))), (APP ((VAR "yy"),(VAR "xx"))))))))))
val t3 = APP (suc, zero);
val t6 = (LAMBDA ((VAR "yy"), (LAMBDA ((VAR "xx"), (APP ((APP (z,(VAR "yy"))), (APP ((VAR "yy"),(VAR "xx")))))))));
val t00 = APP (LAMBDA (VAR "x",VAR "x"),APP (VAR "yy",VAR "xx"));
*)(*val y_ = betanf ((LAMBDA ((VAR "yy"), (LAMBDA ((VAR "xx"), (APP ((APP (z,(VAR "yy"))), (APP ((VAR "yy"),(VAR "xx"))))))))));
val M_ = betanf zero;
val s = sub z y_ M_;
*)
(*(LAMBDA ((VAR "xx"), (APP ((APP (LAMBDA (VAR "y",LAMBDA (VAR "x",VAR "x")),VAR "yy")), (APP (VAR "yy",VAR "xx"))))))*)
(*LAMBDA(VAR "n",(APP ((APP (VAR "n", (LAMBDA (VAR "x", F)))), T)))*)
 

