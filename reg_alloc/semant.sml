signature SEMANT = sig
  type venv
  type tenv
  type expty

  val transProg: Absyn.exp -> {expx:Translate.frag list, ty:Types.ty, exp2:Translate.exp}
end

structure Semant : SEMANT = struct
  structure A = Absyn
  structure P = PrintAbsyn
  structure S = Symbol
  structure E = Env
  structure T = Types
  structure Tr = Translate
  structure Te = Temp

  type venv = E.enventry S.table
  type tenv = T.ty S.table

  type expty = {exp: Tr.exp, ty: T.ty}
  val error = ErrorMsg.error

  fun expty_to_str({exp=exp, ty=ty}) = T.typ_to_str(ty)

  (* To help BreakExp *)
  val top_label = Temp.newlabel()

  fun check_int ({exp=exp, ty=T.INT}, pos) = exp
    | check_int ({exp=exp, ty=_}, pos) = (error pos "INT required"; exp)

  fun check_unit ({exp=exp, ty=T.UNIT}, pos) = exp
    | check_unit ({exp=exp, ty=_}, pos) = (error pos "UNIT required"; exp)


  fun check_array ({exp=exp, ty=T.ARRAY(_, _)}, pos) = exp
    | check_array ({exp=exp, ty=_}, pos) = (error pos "Array required"; exp)

  fun check_eqtyp ({exp=exp, ty=T.INT}, pos) = exp
    | check_eqtyp ({exp=exp, ty=T.RECORD(_, _)}, pos) = exp
    | check_eqtyp ({exp=exp, ty=T.ARRAY(_, _)}, pos) = exp
    | check_eqtyp ({exp=exp, ty=T.NIL}, pos) = exp
    | check_eqtyp ({exp=exp, ty=T.STRING}, pos) = exp
    | check_eqtyp ({exp=exp, ty=ty}, pos) =
        ((error pos ("Can check equality for integers, strings, records and array types: "
                    ^(T.typ_to_str ty)));
        exp)

  fun actual_ty(T.NAME (sym, ty)) =
        (case !ty
           of SOME ty' => actual_ty ty'
            | NONE => T.UNIT)
    | actual_ty(ty) = ty

  fun h_same_type (T.RECORD(fields1, uniq1), ty2) =
        (case ty2
          of T.RECORD(fields2, uniq2) => (uniq1 = uniq2)
           | T.NIL => true
           | _ => false)
    | h_same_type (T.ARRAY(typ1, uniq1), ty2) =
        (case ty2
          of T.ARRAY(typ2, uniq2) => (uniq1 = uniq2)
           | _ => false)
    | h_same_type (ty1, ty2) = (ty1=ty2)

  fun same_type(ty1, ty2) = h_same_type(actual_ty ty1, actual_ty ty2)

    (* Search the type environment for a spcific type.
    * Returns T.ty *)
  fun type_lookup tenv sym pos =
      (case S.look (tenv, sym)
         of SOME typ => (typ)
          | NONE => ((error pos ("Type is not defined: " ^ S.name sym));
                    T.UNIT))

  fun check_fields(h::l) =
      ((List.exists (fn {name, escape, typ, pos} =>
          if (#name h)=name then
            (error pos ("duplicate field: " ^ S.name name); true)
          else
            false)
        l); check_fields(l))
    | check_fields(_) = ()

  fun check_typdec(h::l) =
      ((List.exists (fn {name, pos, ty} =>
          if (#name h)=name then
            (error pos ("Duplicate type dec: " ^ S.name name); true)
          else
            false)
        l); check_typdec(l))
    | check_typdec(_) = ()

  (* Translates Absyn.ty -> Types.ty *)
  fun transTy (tenv, aty) =
    let
      fun trans_fields(fields)= (map
            (fn{name, escape, typ, pos} => (case SOME(type_lookup tenv typ pos)
               of SOME ty => (name, ty)
                | NONE => (name, T.UNIT)))
            fields)
    in case aty
      of A.NameTy (id, pos) => type_lookup tenv id pos
       | A.RecordTy fields => (check_fields(fields);
                              T.RECORD ((trans_fields fields), ref()))
       | A.ArrayTy (id, pos) => T.ARRAY((type_lookup tenv id pos), ref())
    end

  and transDec (venv, tenv, lev, label, A.VarDec vardec, eList) =
        let
          val {name, escape=escape, typ=typ, init, pos=pos1} = vardec
          val {exp, ty} = transExp (venv, tenv, lev, label) init
          val _ = case typ
                      of SOME (s, pos) =>
                        (case S.look (tenv, s)
                           of NONE => (error pos ("Type not defined: " ^ S.name s))
                            | SOME ty2 =>
                                (if same_type (ty2, ty) then ()
                                 else (error pos1 ("Type mismatch. Declared "^
                                 (T.typ_to_str ty)^" with type "^(T.typ_to_str ty2)))))

                       | NONE => ()
          val var_entry as E.VarEntry{access=a,...} = E.VarEntry{access=Tr.allocLocal(lev)(true), ty=ty}
          val assignExp = Tr.InitVarExp(a,exp)
        in
          (S.enter(venv, name, var_entry), tenv, (eList @ [assignExp]))
        end

     | transDec(venv, tenv, lev, label, A.FunctionDec fundecs, eList) =
        let
          fun makeheader (fundec: A.fundec, env) =
            let
              val r_ty =
                (case (#result fundec)
                   of NONE => T.UNIT
                    | SOME(rt, pos) => type_lookup tenv rt pos)

              val params' =
                (map (fn ({name, escape, typ, pos}) =>
                    {name=name, ty = type_lookup tenv typ pos})
                  (#params fundec))

              val formals =
                (map (fn ({name, escape, typ, pos}) => (!escape))
                  (#params fundec))

              val newlabel = Te.newlabel()

              val fun_entry = E.FunEntry({
                    level=Tr.newLevel({parent=lev, name=newlabel,
                      formals=(map (fn param => true) params')}),
                    label=newlabel,
                    formals=(map #ty params'),
                    result=r_ty})
            in
              S.enter(env, (#name fundec), fun_entry)
            end

          fun enterparam (param:A.field, (venv,level')) =
            let
              val ty = type_lookup tenv (#typ param) (#pos param)
              val var_entry = E.VarEntry({access=Tr.allocLocal(level')(true), ty=ty})
            in
              (S.enter(venv, (#name param), var_entry),level')
            end

          val venv' = (foldr makeheader venv fundecs)

          fun check (fundec : A.fundec) =
            let
              val funname = #name(fundec)
              val funlevel = (case S.look (venv', funname)
                 of SOME (E.FunEntry {level=lev', label, formals, result}) => lev'
                 | _ => (error (#pos(fundec)) ("Function Header is not defined: " ^ S.name funname); lev))
              val (venv'',_) = (foldl enterparam (venv',funlevel) (#params fundec))
              val {exp, ty} = transExp(venv'', tenv, funlevel, label) (#body fundec)
            in
              Tr.procEntryExit({level=funlevel,body=exp})
            end

          val _ = (map check fundecs)
        in
          (venv', tenv, eList)
        end

    | transDec(venv, tenv, lev, label, A.TypeDec typeDecs, eList) =
        let
          val names = map #name typeDecs
          val poss = map #pos typeDecs

          val _ = check_typdec(typeDecs)
          val typs = map #ty typeDecs
          fun addt (n, env) = S.enter(env, n, T.NAME(n, ref NONE))
          val tenv' = foldr addt tenv names

          val nts = map (fn t => transTy (tenv', t)) typs

          fun updt ((n, nt), pos) =
              case S.look(tenv', n)
                of SOME (T.NAME(_, r)) =>
                     (case !r
                        of NONE => (r := SOME nt)
                         | SOME t => if (t = nt) then ()
                                     else (error pos "var dec type mismatch"))
                | _ => (error pos "var dec type mismatch")

          val _ = app updt (ListPair.zip(ListPair.zip(names, nts), poss))
        in
          (venv, tenv', eList)
        end

  and transDecs(venv, tenv, lev, label, decs) =
    (foldl (fn (dec, (v, t, eList)) => transDec(v, t, lev, label, dec, eList))
      (venv, tenv, []) decs)

  and transExp(venv, tenv, lev, label) =
    let
          (* Nil *)
      fun trexp (A.NilExp) = {exp=Tr.NilExp(), ty=T.NIL}

          (* Integer *)
        | trexp (A.IntExp i) = {exp=Tr.IntExp(i), ty=T.INT}

          (* String *)
        | trexp (A.StringExp (str, pos)) = {exp=Tr.StringExp(str), ty=T.STRING}

          (* Array *)
        | trexp (A.ArrayExp {typ, size, init, pos}) =
            let
              val arr_type = actual_ty (type_lookup tenv typ pos)
              val et_size = trexp size
              val et_init = trexp init

              (* Make sure init = typ *)
              fun check_init_typ (T.ARRAY(typ', uniq)) =
                    if same_type(typ', #ty et_init) then ()
                    else
                      (error pos ("Array type-id ("^(T.typ_to_str typ')^
                      ") and init type ("^(expty_to_str et_init)^
                      ") are not the same."))
                | check_init_typ (typ') = (error pos ((S.name typ)
                      ^ " is not a valid array type. Got " ^ (T.typ_to_str typ')
                      ^" instead"))
            in
              (check_int(et_size, pos);
              check_init_typ(arr_type);
              {exp=(Tr.ArrayExp(#exp et_size, #exp et_init)), ty=arr_type})
            end

          (* Record *)
        | trexp (A.RecordExp {fields, typ, pos}) =
              let val fields' = map (fn (_, e, _) => #exp(trexp e)) fields
              in {exp=(Tr.RecordExp(fields')), ty=(type_lookup tenv typ pos)}
              end

          (* Variable *)
        | trexp (A.VarExp var) = trvar var

          (* Call *)
        | trexp (A.CallExp {func, args, pos}) =
            let
              fun check_arg(formal, arg) =
                let
                  val et_arg = trexp arg
                in
                  if same_type(formal, (#ty et_arg)) then
                    (#exp et_arg)
                  else
                    ((error pos ("Argument mismatch for function " ^ (S.name func)^
                    ". Formal expects " ^ (T.typ_to_str formal) ^ " but arg is " ^
                    (expty_to_str et_arg))); (#exp et_arg))
                end

              fun check_args(formals, args) =
                if(length(formals) <> length(args)) then
                  ((error pos
                    ("Wrong number of arguments provided for function "
                    ^(S.name func)));[])
                else
                  (map check_arg (ListPair.zip(formals, args)))
            in
              (case S.look (venv, func)
                 of SOME (E.FunEntry {level=lev', label=label', formals, result}) =>
                            {exp=(Tr.CallExp(func, label', lev', lev,
                              (check_args(formals, args)))),
                            ty=result}
                  | _ => ((error pos ("Function " ^(S.name func)^
                                      " does not exist." ));
                          {exp=Tr.NilExp(), ty=T.UNIT}))
            end

          (* Operation *)
        | trexp (A.OpExp op_exp) = trOpExp op_exp

          (* Assign *)
        | trexp (A.AssignExp {var, exp, pos}) =
          let
            val et_left = trvar var
            val et_right = trexp exp
          in
            (if same_type(#ty et_left, #ty et_right) then ()
            else
              ((error pos ("Assignment expression type ("
              ^ (expty_to_str et_right) ^ ") does not match variable type ("
              ^ (expty_to_str et_left) ^ ")"))));
            {exp=Tr.AssignExp((#exp et_left), (#exp et_right)), ty=T.UNIT}
          end

          (* If *)
        | trexp (A.IfExp {test, then', else', pos}) =
            let
              val et_test = trexp test
              val et_then = trexp then'
            in
              case else'
                (* If-then statements return T.UNIT *)
                of NONE =>
                    (check_int(et_test, pos);
                    check_unit(et_then, pos);
                    {exp=(Tr.IfExp(#exp(et_test), #exp(et_then), NONE)), ty=T.UNIT})
                 | SOME else_exp =>
                     let val et_else = trexp else_exp
                     in
                       (check_int(et_test, pos);
                       {exp=(Tr.IfExp((#exp et_test), (#exp et_then),
                                      SOME(#exp et_else))),
                       ty=(#ty et_else)})
                     end
            end

          (* While *)
        | trexp (A.WhileExp {test, body, pos}) =
            let val et_test = trexp test
                val test_label = Temp.newlabel()
                val done_label = Temp.newlabel()
                val et_body = transExp(venv, tenv, lev, done_label) body
            in
              (check_int (et_test, pos);
              check_unit(et_body, pos);
              {exp=(Tr.WhileExp(test_label, done_label, #exp et_test, #exp et_body)), ty=T.UNIT})
            end

          (* For *)
        | trexp (A.ForExp {var=varsym, escape, lo, hi, body, pos}) =
          let
            val et_lo = trexp lo
            val et_hi = trexp hi
            val test_label = Temp.newlabel()
            val done_label = Temp.newlabel()
            val venv' = S.enter(venv, varsym, E.VarEntry{access=Tr.allocLocal(lev)(true),
                                                        ty=T.INT})
            val et_body = transExp(venv', tenv, lev, done_label) body
          in
            (check_int(et_lo, pos);
            check_int(et_hi, pos);
            check_unit(et_body, pos);
            {exp=(Tr.ForExp(test_label, done_label, #exp et_lo, #exp et_hi, #exp et_body)),
            ty=T.UNIT})
          end

        (* Break *)
        | trexp (A.BreakExp pos) =
            ((if label = top_label then
              (error pos "Cannot break without a while or for loop")
            else());
            {exp=(Tr.BreakExp(label)), ty=T.UNIT})

        (* Let *)
        | trexp (A.LetExp{decs, body, pos}) =
            let
              val letLevel = Tr.newLevel({parent=lev,name=Te.newlabel(),formals=[]})
              val (venv', tenv', expList) = transDecs(venv, tenv, letLevel, label, decs)
              val et_body = transExp(venv', tenv', letLevel, label) body
            in
              {exp=Tr.LetExp(expList, #exp(et_body)), ty=(#ty et_body)}
            end

        (* Sequence *)
        | trexp (A.SeqExp exps) =
            let
              (* exps comes in form (exp * pos) list *)
              val results = map trexp (map #1 exps)
            in
              if(List.null(results)) then
                {exp=Tr.NilExp(), ty=T.UNIT}
              else
                {exp=Tr.SeqExp((map #exp results)),
                ty=(#ty (List.last results))}
            end

          (* Addition *)
      and trOpExp ({left, oper=A.PlusOp, right, pos}) = trMathOpExp(left, A.PlusOp, right, pos)
          (* Minus *)
        | trOpExp ({left, oper=A.MinusOp, right, pos}) = trMathOpExp(left, A.MinusOp, right, pos)
          (* Times *)
        | trOpExp ({left, oper=A.TimesOp, right, pos}) = trMathOpExp(left, A.TimesOp, right, pos)
          (* Divide *)
        | trOpExp ({left, oper=A.DivideOp, right, pos}) = trMathOpExp(left, A.DivideOp, right, pos)
          (* Equal *)
        | trOpExp ({left, oper=A.EqOp, right, pos}) = trEqOpExp(left, A.EqOp, right, pos)
          (* Not equal *)
        | trOpExp ({left, oper=A.NeqOp, right, pos}) = trEqOpExp(left, A.NeqOp, right, pos)
          (* Less than *)
        | trOpExp ({left, oper=A.LtOp, right, pos}) = trMathOpExp(left, A.LtOp, right, pos)
          (* Less than or equal to *)
        | trOpExp ({left, oper=A.LeOp, right, pos}) = trMathOpExp(left, A.LeOp, right, pos)
          (* Greater than *)
        | trOpExp ({left, oper=A.GtOp, right, pos}) = trMathOpExp(left, A.GtOp, right, pos)
          (* Greater than or equal to *)
        | trOpExp ({left, oper=A.GeOp, right, pos}) = trMathOpExp(left, A.GeOp, right, pos)

      and trMathOpExp (left, oper, right, pos) =
            let val left' = trexp left
                val right' = trexp right
            in
              (check_int(left', pos);
               check_int(right', pos);
               {exp=(Tr.OpExp(oper, #exp left', #exp right')), ty=T.INT})
            end

      and trEqOpExp (left, oper, right, pos) =
            let val left' = trexp left
                val right' = trexp right
            in
              (check_eqtyp(left', pos);
              check_eqtyp(right', pos);
              (if same_type(#ty left', #ty right') then ()
               else
                 (error pos ("Cannot compare " ^(expty_to_str left')
                  ^" with "^(expty_to_str right'))));
              {exp=(Tr.OpExp(oper, #exp left', #exp right')), ty=T.INT})
            end

          (* Simple Var *)
      and trvar (A.SimpleVar(id, pos)) =
            (case S.look(venv, id)
               of SOME(E.VarEntry{access, ty}) => {exp=(Tr.SimpleVar(access, lev)),
                                                  ty=actual_ty ty}
                | _ => (error pos ("Undefined simple var " ^ S.name id);
                        {exp=Tr.NilExp(), ty=T.UNIT}))

          (* FieldVar *)
        | trvar (A.FieldVar(var, sym, pos)) =
            let
              val {exp=var_exp, ty=var_ty} = trvar var
            in
              case var_ty
                of T.RECORD(fields, uniq) =>
                    let
                      fun get_index(sym, [], i) = NONE
                        | get_index(sym, (fsym, ty)::l, i) =
                            (if (sym = fsym) then SOME((i, ty))
                             else get_index(sym, l, i+1))
                    in
                      (case get_index(sym, fields, 0)
                         of SOME((i, ty)) => {exp=Tr.FieldVar(var_exp, i),
                                              ty=actual_ty ty}
                          | NONE => ((error pos ("Field " ^ (S.name sym) ^
                                                " not found"));
                                    ({exp=Tr.NilExp(), ty=T.UNIT})))
                    end
                | _ => ((error pos ("Undefined record var "
                        ^ (S.name sym) ^ " of type " ^ (T.typ_to_str var_ty)));
                        {exp=Tr.NilExp(), ty=T.UNIT})
            end

          (* SubscriptVar *)
        | trvar (A.SubscriptVar(var, exp, pos)) =
            let
              val et_arr = trvar var
              val et_ind = trexp exp
              fun get_typ({exp=_, ty=T.ARRAY(typ, uniq)}) = actual_ty typ
                | get_typ({exp=_, ty=ty}) = ty
            in
              (check_int(et_ind, pos);
              check_array(et_arr, pos);
              {exp=Tr.SubscriptVar(#exp et_arr, #exp et_ind),
                ty=get_typ et_arr})
            end
    in
      trexp
    end

  fun transProg(absyn) =
  let
	  val firstlevel = Translate.newLevel {
	      name= Temp.namedlabel "tig_main",
        parent=Tr.outermost,
        formals=[]}

	   val {exp, ty} = transExp (E.base_venv, E.base_tenv, Tr.outermost,
       top_label) absyn
   in
	   (Tr.procEntryExit {level=firstlevel, body=exp};
     {expx=Tr.getResult(),ty=ty,exp2=exp})
   end
end
