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
