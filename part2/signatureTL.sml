use "structureLAMBDAFLX.sml";
open LambdaFlx;

signature TL =
sig
    datatype ltype = INT                (* int *)
                   | BOOL               (* bool *)
                   | TV of string
                   | STAR of ltype * ltype
                   | ARROW of ltype * ltype 
    
(*    val findType: string*((string*ltype) list) -> ltype * (string*ltype) list
    val assignType: string*((string*ltype) list)*ltype -> (string*ltype) list *)           
    val getType: lterm -> ((string*ltype) list) -> ltype * (string*ltype) list
end
