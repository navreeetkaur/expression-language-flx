use "signatureFLX.sml";
(*open String;
open Char;
open List;
*)
structure Flx : FLX = 
struct
	datatype term = VAR of string (* variable *)
                  | Z           (* zero *)
                  | T           (* true *)
                  | F           (* false *)
                  | P of term   (* Predecessor *)
                  | S of term   (* Successor *)
                  | ITE of term * term * term   (* If then else *)
                  | IZ of term  (* is zero *)
                  | GTZ of term (* is greater than zero *)
    
  exception Not_wellformed;
  exception Not_nf;
  exception Not_int;

  local 
		fun combine [] = []
			| combine ((#"Z")::tail) = ""::"Z"::(combine tail)
			| combine ((#"T")::tail) = ""::"T"::(combine tail)
			| combine ((#"F")::tail) = ""::"F"::(combine tail)
			| combine ((#"P")::tail) = ""::"P"::(combine tail)
			| combine ((#"S")::tail) = ""::"S"::(combine tail)
			| combine ((#"I")::(#"T")::(#"E")::tail)= "ITE"::(combine tail)
			| combine ((#"I")::(#"Z")::tail) = "IZ"::(combine tail)
			| combine ((#"G")::(#"T")::(#"Z")::tail) = "GTZ"::(combine tail)
			| combine (h::tail) = 
				let val x = combine tail
				in if (h=(#"(") orelse h=(#")") orelse h=(#"<") orelse h=(#">") orelse h=(#","))
					then ""::Char.toString(h)::x
					else if (Char.isSpace h) then ""::x
					else if tail=[] then [Char.toString h] else (Char.toString(h)^List.hd(x))::List.tl(x)
				end

		fun str2term [] = []
			| str2term ((VAR "Z")::tail) = Z::(str2term tail)
			| str2term ((VAR "T")::tail) = T::(str2term tail)
			| str2term ((VAR "F")::tail) = F::(str2term tail)
			| str2term ((VAR " ")::tail) = str2term tail
			| str2term ((VAR "(")::(VAR "S")::(t:term)::(VAR ")")::tail) = S(List.hd(str2term[t]))::str2term(tail)
			| str2term ((VAR "(")::(VAR "P")::(t:term)::(VAR ")")::tail) = P(List.hd(str2term[t]))::str2term(tail)
			| str2term ((VAR "(")::(VAR "IZ")::(t:term)::(VAR ")")::tail) = IZ(List.hd(str2term[t]))::str2term(tail)
			| str2term ((VAR "(")::(VAR "GTZ")::(t:term)::(VAR ")")::tail) = GTZ(List.hd(str2term[t]))::str2term(tail)
			| str2term ((VAR "(")::(VAR "ITE")::(VAR "<")::(x:term)::(VAR ",")::(y:term)::(VAR ",")::(z:term)::(VAR ">")::(VAR ")")::tail) = 
				let
					val t1 = List.hd(str2term[x])
					val t2 = List.hd(str2term[y])
					val t3 = List.hd(str2term[z])
				in ITE((t1),(t2),(t3))::str2term(tail)
				end
			| str2term (h::tail) = h::(str2term tail)
	in
		fun fromString x = 
			let 
				fun generateVar [] = []
			  	| generateVar (""::t) = generateVar t
			  	| generateVar (h::t) = (VAR h)::(generateVar t)
				fun to_char_list [] = []
					| to_char_list (h::t) = h::(to_char_list t)
				fun is_term [h] = h
					| is_term L = raise Not_wellformed
				fun is_well_formed [] [] = true
					| is_well_formed L [] = false
					| is_well_formed [] L = false
					| is_well_formed (a::b) (c::d) = 
					if a=c then (is_well_formed b d) else false
				fun parse [] = []
					| parse [h] = [h]
					| parse (h::tail) = 
						let val p = str2term (h::tail)
						in if (is_well_formed (h::tail) p) then raise Not_wellformed else (parse p)
						end
			in 
				let 
					val parsed = parse (generateVar (combine (to_char_list (String.explode x))))
					val t = is_term parsed
				in 
					t
				end
			end
	end;


  fun toString Z = "Z"
  	| toString T = "T"
  	| toString F = "F"
  	| toString (P t) = ("(P " ^ (toString t)) ^ ")"
  	| toString (S t) = ("(S " ^ (toString t)) ^ ")"
  	| toString (ITE (t1,t2,t3)) = "(ITE <" ^ (toString t1) ^ "," ^ (toString t2) ^ "," ^ (toString t3)  ^ ">)"
  	| toString (IZ t) = ("(IZ " ^ (toString t)) ^ ")"
  	| toString (GTZ t) = ("(GTZ " ^ (toString t)) ^ ")"
		| toString (VAR t) = t;


	local
	  fun fromIntPos 0 = Z
	  	| fromIntPos n = S (fromIntPos (n-1))
	  fun fromIntNeg 0 = Z
	  	| fromIntNeg n = P (fromIntNeg (n+1))
	in
    fun fromInt 0 = Z
    	| fromInt n = 
    	if n > 0 
    	then fromIntPos n 
    	else fromIntNeg n
	end;


	local
		fun toIntS Z = 0
			| toIntS (VAR x) = raise Not_int
		  | toIntS T = raise Not_int
		  | toIntS F = raise Not_int
		  | toIntS (GTZ x )= raise Not_int
		  | toIntS (IZ x) = raise Not_int
		  | toIntS (ITE (t1,t2,t3)) = raise Not_int
		  | toIntS (P t) = raise Not_nf
			| toIntS (S t) = (toIntS t) + 1
		fun toIntP Z = 0
			| toIntP (VAR x) = raise Not_int
		  | toIntP T = raise Not_int
		  | toIntP F = raise Not_int
		  | toIntP (GTZ x )= raise Not_int
		  | toIntP (IZ x) = raise Not_int
		  | toIntP (ITE (t1,t2,t3)) = raise Not_int
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
    	| toInt (S t) = (toInt t) + 1
    	| toInt (P t) = (toInt t) - 1
	end;


	fun normalize Z = Z
		| normalize T = T
		| normalize F = F
		| normalize (S (P x)) = normalize x
		| normalize (P (S x)) = normalize x
		| normalize (IZ Z) = T
		| normalize (GTZ Z) = F
		| normalize (IZ x) = 
			let 
				val t = normalize x
				fun normalize_itz (S n) = F
					| normalize_itz (P n) = F
					| normalize_itz x = IZ x
			in normalize_itz t 
			end
		| normalize (GTZ x) = 
			let 
				val t = normalize x;
				fun normalize_gtz (S n) = T
					| normalize_gtz (P n) = F
					| normalize_gtz x = GTZ x
			in (normalize_gtz t) end
		| normalize (ITE (T,x,y)) = normalize x
		| normalize (ITE (F,x,y)) = normalize y
		| normalize (ITE (t1,t2,t3)) = 
			if t2=t3 then normalize t2
			else 
				let 
					val x1 = normalize t1
					val x2 = normalize t2
					val x3 = normalize t3
				in (ITE (x1,x2,x3))
				end
		| normalize x = x;

end;
(*open Flx;*)
