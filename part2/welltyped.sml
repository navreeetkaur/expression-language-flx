  local
   (* fun isInt Z = true
      | isInt T = false
      | isInt F = false
      | isInt (P t) = isInt t
      | isInt (S t) = isInt t
      | isInt (ITE (t1,t2,t3)) = (isInt t2) andalso (isInt t3) andalso (isBool t1) 
      | isInt (GTZ t) = false
      | isInt (IZ t) = false
      | isInt (LAMBDA ((VAR t),t2)) = false
      | isInt (LAMBDA (t1, t2)) = raise Not_wellformed
      | isInt (APP (t1,t2)) = false
      | isInt (VAR t) = false
      | isInt t = raise Not_wellformed
    fun isBool Z = false
      | isBool T = true
      | isBool F = true
      | isBool (P t) = false
      | isBool (S t) = false
      | isBool (ITE (t1,t2,t3)) = (isBool t1) andalso (isBool t2) andalso (isBool t3) 
      | isBool (GTZ t) = true
      | isBool (IZ t) = true
      | isBool (LAMBDA ((VAR t),t2)) = false
      | isBool (LAMBDA (t1, t2)) = raise Not_wellformed
      | isBool (APP (t1,t2)) = false
      | isBool (VAR t) = false
      | isBool t = raise Not_wellformed*)

    fun check [] [] = true
      | check L [] = false
      | check [] L = false
      | check (hd1::tl1) (hd2::tl2) = 
      if (hd1<>hd2) then false else (check tl1 tl2);


    (* INT:1  BOOL:2 *)
    fun getType Z = [1]
      | getType T = [2]
      | getType F = [2]
      | getType (VAR t) = [3]
      | getType (P t) = if (hd (getType t))=1 then [1] else [0]
      | getType (S t) = if (hd (getType t))=1 then [1] else [0]
      | getType (IZ t) = if (hd (getType t))=1 then [2] else [0]
      | getType (GTZ t) = if (hd (getType t))=1 then [2] else [0]
      | getType (ITE (t1,t2,t3)) = 
        let val v = getType t2
        in
          if (((hd (getType t1))=2) andalso (check (getType t3) v)) then v else [0]
        end
        (*// check this *)
      | getType (LAMBDA (t0, t1)) = 
        let
          val v0 = (getType t0)
          val v1 = (getType t1)
        in if (((hd v0)<>0) orelse ((hd v1)<>0)) then v0@v1 else [0] 
        end
      (*// | getType (APP ((LAMBDA ((VAR t0), t1)), (VAR u))) = getType t1*)
      | getType (APP (t1, t2)) = 
        let
          val T1 = getType t1
          val T2 = getType t2
        in
          if (hd T1)<>(hd T2) then [0] else (List.last T1)::[]
          (*// if ((null (tl T2)) andalso (hd T1)=(hd T2)) then (tl T1) else [0]*)
        end
      | getType t = raise Not_wellformed;

  in 
    fun isWellTyped Z = true
      | isWellTyped T = true
      | isWellTyped F = true
      | isWellTyped (IZ t) = if (hd (getType t))=1 then true else false
      | isWellTyped (GTZ t) = if (hd (getType t))=1 then true else false
      | isWellTyped (P t) = if (hd (getType t))=1 then true else false
      | isWellTyped (S t) = if (hd (getType t))=1 then true else false
      | isWellTyped (ITE (t1,t2,t3)) = if (hd (getType (ITE (t1,t2,t3))))<>0 then true else false
      | isWellTyped (VAR t) = true
      | isWellTyped (LAMBDA (VAR t,t2)) = if (hd (getType (LAMBDA (VAR t,t2))))<>0 then true else false
      | isWellTyped (LAMBDA (t1, t2)) = raise Not_wellformed
      | isWellTyped (APP (t1, t2)) = if (hd (getType (APP (t1, t2))))<>0 then true else false
      | isWellTyped t = raise Not_wellformed
  end;



  (*fun insert (x, []) = [x]
        | insert (x, L as y::M) = if (x=y) then L else y::(insert (x, M))

      fun belongsto (x, []) = false
      | belongsto (x, y::L) = if (x=y) then true else belongsto(x, L)

    fun delete (x, []) = []
      | delete (x, y::L) = if (x=y) then L 
                           else y::(delete (x, L))
    fun union ([], M) = M
      | union (x::L, M) = union (L, insert (x, M))

    fun isvar (VAR s) = true
      | isvar _ = false

    fun FV (VAR x) = [(VAR x)]
      | FV (LAMBDA((VAR x), L)) = delete ((VAR x), FV(L))
      | FV (APP (L, M)) = union (FV(L), FV(M))

    fun BV ((VAR _)) = []
      | BV (LAMBDA((VAR x), L)) = (VAR x)::BV(L)
      | BV (APP (L, M)) = BV(L) @ BV(M)

    fun wellformed ((VAR x)) = true
      | wellformed (LAMBDA(VAR(x), L)) = wellformed (L)
      | wellformed (LAMBDA(_, _)) = false
      | wellformed (APP (L, M)) = wellformed (L) andalso wellformed (M)

      fun sub (N, (VAR x)) (VAR y) = if x=y then N else (VAR y)
        | sub (N, (VAR x)) (APP (L, M)) = APP((sub (N, (VAR x)) L), (sub (N, (VAR x)) M))
        | sub (N, VAR(x)) (LAMBDA ((VAR y), L)) =
          if (x=y) then LAMBDA ((VAR x), L)
          else
            let val FVL = FV(L)
                  val FVN = FV(N)
              in  if belongsto ((VAR x), FVN)
                  then
                      let val strsN = map toString FVN
                          val strsL = map toString FVL
                          val strsLN = strsL @strsN
                          fun newvar (z, strs) =
                              if belongsto (z, strs) then newvar (z^"1", strs) else z
                          val zed = newvar(x^"1", strsLN)
                      in  LAMBDA ((VAR zed), (sub (N, (VAR x)) (sub ((VAR zed), (VAR y)) L)))
                      end
              else LAMBDA (VAR(y), (sub (N, VAR(x)) L))
    end*)


    
    fun insert (x, []) = [x]
        | insert (x, L as y::M) = if (x=y) then L else y::(insert (x, M))

    fun belongsto (x, []) = false
    | belongsto (x, y::L) = if (x=y) then true else belongsto(x, L)

    fun delete (x, []) = []
    | delete (x, y::L) = if (x=y) then L 
                       else y::(delete (x, L))
    fun union ([], M) = M
    | union (x::L, M) = union (L, insert (x, M))

    fun isvar (VAR s) = true
    | isvar _ = false

    fun FV (VAR x) = [(VAR x)]
    | FV (LAMBDA((VAR x), L)) = delete ((VAR x), FV(L))
    | FV (APP (L, M)) = union (FV(L), FV(M))

    fun BV ((VAR _)) = []
    | BV (LAMBDA((VAR x), L)) = (VAR x)::BV(L)
    | BV (APP (L, M)) = BV(L) @ BV(M)

    fun wellformed ((VAR x)) = true
    | wellformed (LAMBDA(VAR(x), L)) = wellformed (L)
    | wellformed (LAMBDA(_, _)) = false
    | wellformed (APP (L, M)) = wellformed (L) andalso wellformed (M)

    fun sub (N, (VAR x)) (VAR y) = if x=y then N else (VAR y)
    | sub (N, (VAR x)) (APP (L, M)) = APP((sub (N, (VAR x)) L), (sub (N, (VAR x)) M))
    | sub (N, VAR(x)) (LAMBDA ((VAR y), L)) =
      if (x=y) then LAMBDA ((VAR x), L)
      else
        let val FVL = FV(L)
              val FVN = FV(N)
        in  if belongsto ((VAR x), FVN)
              then
                  let val strsN = map toString FVN
                      val strsL = map toString FVL
                      val strsLN = strsL @strsN
                      fun newvar (z, strs) =
                          if belongsto (z, strs) then newvar (z^"1", strs) else z
                      val zed = newvar(x^"1", strsLN)
                  in  LAMBDA ((VAR zed), (sub (N, (VAR x)) (sub ((VAR zed), (VAR y)) L)))
                  end
          else LAMBDA (VAR(y), (sub (N, VAR(x)) L))
        end