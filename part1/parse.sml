local
      fun clean [] = []
        | clean(h::t) = h::clean(t)

      fun join_vars [] = []
        | join_vars((#"I")::(#"T")::(#"E")::tl) = "ITE"::join_vars(tl)
        | join_vars((#"I")::(#"Z")::tl) = "IZ"::join_vars(tl)
        | join_vars((#"G")::(#"T")::(#"Z")::tl) = "GTZ"::join_vars(tl)
        | join_vars (h::t) = 
          let
            val clean_t = join_vars(t)
          in
            if(Char.isUpper(h) orelse h = #"," orelse h = #"(" orelse h = #")" orelse h = #"<" orelse h = #">") then
              ""::Char.toString(h)::clean_t
            else if(h = #" ") then
              ""::clean_t
            else
              if(t=[]) then
                [Char.toString(h)]
              else
                Char.toString(h) ^ List.hd(clean_t) :: List.tl(clean_t)
          end
      
      fun make_vars [] = []
        | make_vars(""::t) = make_vars(t)
        | make_vars(h::t) = VAR(h) :: make_vars(t)
      
      fun reduce_terms [] = []
        | reduce_terms(VAR("Z")::tl) = Z::reduce_terms(tl)
        | reduce_terms (VAR("T")::tl) = T::reduce_terms(tl)
        | reduce_terms (VAR("F")::tl) = F::reduce_terms(tl)
        | reduce_terms (VAR(" ")::tl) = reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("P")::(x:term)::VAR(")")::tl) = P(List.hd(reduce_terms[x]))::reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("S")::(x:term)::VAR(")")::tl) = S(List.hd(reduce_terms[x]))::reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("IZ")::(x:term)::VAR(")")::tl) = IZ(List.hd(reduce_terms[x]))::reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("GTZ")::(x:term)::VAR(")")::tl) = GTZ(List.hd(reduce_terms[x]))::reduce_terms(tl)
        | reduce_terms (VAR("(")::VAR("ITE")::VAR("<")::(a:term)::VAR(",")::(b:term)::VAR(",")::(c:term)::VAR(">")::VAR(")")::tl) = ITE((List.hd(reduce_terms[a])),(List.hd(reduce_terms[b])),(List.hd(reduce_terms[c])))::reduce_terms(tl)
        | reduce_terms(h::tl) = h::reduce_terms(tl)
      
      fun compare([],[]) = true
        | compare(L,[]) = false
        | compare([],L) = false
        | compare(L1 as (h1::t1), L2 as (h2::t2)) =
          if(h1=h2) then
            compare(t1,t2)
          else
            false
      
      fun make_terms [] = []
        | make_terms [h] = [h]
        | make_terms(L as h::t) =
        let
          val L1 = reduce_terms(h::t)
        in
          if(compare(L1,L)) then
            raise Not_wellformed
          else
            make_terms(L1)
        end
    in
      fun fromString(Str) =
        let
          val S_clean = clean(String.explode(Str))
          val S_join = join_vars(S_clean)
          val S_made = make_vars(S_join)
          val S_term = make_terms(S_made)
        in
          if(List.length(S_term) > 1) then
            raise Not_wellformed
          else
            List.hd(S_term)
        end
    end