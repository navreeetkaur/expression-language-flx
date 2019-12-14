use "signatureTL.sml";

structure tl: TL = 
struct
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
	end;
end;


open tl;
Control.Print.printDepth := 1024;
val x = VAR "x";
val y = VAR "y";
val z = VAR "z";
val t = LAMBDA (x, LAMBDA (y, LAMBDA (z, (APP (x, (APP (y,z)))))));
val t1 = APP (y,z);
val t2 = APP (x, APP(y,z));
