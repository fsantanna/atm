package atm

import kotlin.math.max

class Coder () {
    // Pair<mems,protos>: need to separate b/c protos must be inner->outer, while mems outer->inner
    val pres: MutableList<Pair<String,String>> = mutableListOf()
    val defers: MutableMap<Expr.Do, Triple<MutableList<Int>,String,String>> = mutableMapOf()
    val code: String = G.outer!!.code()

    fun List<Expr>.code (): String {
        return this.map { it.code() }.joinToString("")
    }

    fun Expr.toerr (): String {
        val src = this.to_str(false).replace("_\\d+".toRegex(), "").quote(45)
        return "\"${this.tk.pos.file} : (lin ${this.tk.pos.lin}, col ${this.tk.pos.col}) : $src\""
    }

    fun Expr.check_aborted (cmd: String): String {
        val exe = this.up_exe()
        val defer = this.up_first_without({ it is Expr.Defer }, { it is Expr.Proto })
        return (CEU>=3 && exe!==null && defer===null).cond { """
            if (ceux->exe->status == CEU_EXE_STATUS_TERMINATED) {
                $cmd;
            }
        """ }
    }
    fun Expr.check_error_aborted (cmd: String, msg: String): String {
        return """
            CEU_ERROR_CHK_ERR($cmd, $msg);
            ${this.check_aborted(cmd)}
        """
    }

    fun Expr.code(): String {
        if (this.is_dst()) {
            assert(this is Expr.Acc || this is Expr.Index || this is Expr.Pub)
        }
        return when (this) {
            is Expr.Proto -> """
                function ()
                    return ${this.blk.es.code()}
                end
            """
            is Expr.Do -> {
                val body = this.es.code()   // before defers[this] check
                val up = this.fup()
                val blkc = this.idx("block_$n")
                """
                do -- BLOCK | ${this.dump()}
                    ${(CEU >= 4).cond { """
                         ${(!this.is_mem()).cond { "CEU_Block" }} $blkc = NULL;
                    """}}
                    
                    ${defers[this].cond { """
                        --{ // BLOCK | defers | init | ${this.dump()}
                            ${it.second}
                        --}
                    """ }}
                    
                    do -- BLOCK | ${this.dump()}
                        $body
                        ${(up is Expr.Loop).cond { """
                            CEU_LOOP_STOP_${up!!.n}:
                        """ }}
                    end

                    ${defers[this].cond { """
                        { -- BLOCK | defers | term | ${this.dump()}
                            ${it.third}
                        }
                    """ }}
                    
                    ${(CEU >= 4).cond { """
                        if ($blkc != NULL) {
                            CEU_LNKS($blkc)->up.blk = NULL; // also on ceu_task_unlink (if unlinked before leave)
                        }
                        {
                            CEU_Block cur = ceu_task_get($blkc);
                            while (cur != NULL) {
                                ceu_abort_dyn(cur);
                                CEU_Dyn* nxt = ceu_task_get(CEU_LNKS(cur)->sd.nxt);
                                ceu_gc_dec_dyn(cur); // TODO: could affect nxt?
                                cur = nxt;
                            }
                        }                            
                    """ }}

            --[[
            #ifdef CEU_LEX
                    ceux->depth--;
            #endif
            ]]--
                end
                """
            }
            is Expr.Enclose -> {
                """
                do { -- ENCLOSE | ${this.dump()}
                    ${this.es.code()}
                } while (0);
                if (CEU_ERROR != CEU_ERROR_NONE) {
                    continue;
                }
                ${this.check_aborted("continue")}
                if (CEU_ESCAPE == CEU_ESCAPE_NONE) {
                    // no escape
                } else if (CEU_ESCAPE == CEU_TAG_${this.tag.str.idc()}) {
                    CEU_ESCAPE = CEU_ESCAPE_NONE;   // caught escape: go ahead
                } else {
                    continue;                       // uncaught escape: propagate up
                }                                                            
                """
            }
            is Expr.Escape -> """ -- ESCAPE | ${this.dump()}
            {
                ${this.e.cond { """
                    ${it.code()}
                """ }}
                CEU_ESCAPE = CEU_TAG_${this.tag.str.idc()};
                continue;
            }
            """
            is Expr.Group -> "-- GROUP | ${this.dump()}\n" + this.es.code()
            is Expr.Dcl -> this.idtag.first.str.let { id ->
                (!GLOBALS.contains(id)).cond { "local ${id.idc()} ${this.src.cond { " = " + it.code() }}\n" }
             }
            is Expr.Set -> this.dst.code() + " = " + this.src.code() + "\n"
            is Expr.If -> """
                { -- IF | ${this.dump()}
                    ${this.cnd.code()}
                    {
                        int v = ceu_as_bool(ceu_acc);
                        if (v) {
                            ${this.t.code()}
                        } else {
                            ${this.f.code()}
                        }
                    }
                }
                """
            is Expr.Loop -> """
                -- LOOP | ${this.dump()}
                CEU_LOOP_START_${this.n}:
                    ${this.blk.code()}
                    goto CEU_LOOP_START_${this.n};
            """
            is Expr.Data -> "-- DATA | ${this.dump()}\n"
            is Expr.Drop -> """
                -- DROP | ${this.dump()}
                ${this.e.code()}
                ${(LEX && !this.e.is_lval()).cond { """
                    CEU_ERROR_CHK_PTR (
                        continue,
                        ceu_drop(ceu_acc, ceux->depth),
                        ${this.fupx().toerr()}
                    );
                """ }}
            """

            is Expr.Catch -> {
                """
                { -- CATCH ${this.dump()}
                    do { // catch
                        ${this.blk.code()}
                    } while (0); // catch
                    ${(CEU>=3 && this.up_any { it is Expr.Proto && it.tk.str!="func'" }).cond { """
                        if (ceux->act == CEU_ACTION_ABORT) {
                            continue;   // do not execute next statement, instead free up block
                        }
                    """ }}
                    if (CEU_ERROR == CEU_ERROR_NONE) {
                        // no error
                    } else {
                        ${this.tag.cond2({"""
                            if (CEU_ERROR==CEU_TAG_nil || _ceu_sup_(CEU_TAG_${it.str.idc()}, CEU_ERROR)) {
                                CEU_ERROR = CEU_ERROR_NONE; // caught error: go ahead
                                ceu_error_clear();
                            } else {
                                continue;                   // uncaught error: propagate up
                            }                            
                        """},{"""
                            CEU_ERROR = CEU_ERROR_NONE; // caught error: go ahead
                            ceu_error_clear();
                        """})}
                    }
                }
                """
            }
            is Expr.Defer -> {
                val bup = this.up_first { it is Expr.Do } as Expr.Do
                val (ns,ini,end) = defers.getOrDefault(bup, Triple(mutableListOf(),"",""))
                val id = this.idx("defer_$n")
                val inix = """
                    ${this.dcl("int")} $id = 0;   // not yet reached
                """
                val endx = """
                    if ($id) {     // if true: reached, finalize
                        int ceu_error_$n = CEU_ERROR;
                        CEU_ERROR = CEU_ERROR_NONE;
                        do {
                            ${this.blk.code()}
                        } while (0);    // catch throw
                        assert(CEU_ERROR==CEU_ERROR_NONE && "TODO: error in defer");
                        CEU_ERROR = ceu_error_$n;
                    }
                """
                ns.add(n)
                defers[bup] = Triple(ns, ini+inix, endx+end)
                """
                $id = 1;   // now reached
                CEU_ACC(((CEU_Value) { CEU_VALUE_NIL }));
                """
            }

            is Expr.Resume -> {
                val coro = this.idx("coro_$n")
                """
                { -- RESUME | ${this.dump()}
                    ${(!this.is_mem()).cond { """
                        CEU_Value $coro;
                        CEU_Value ceu_args_$n[${this.args.size}];
                    """ }}

                    ${this.co.code()}
                    $coro = CEU_ACC_KEEP();
                    if ($coro.type!=CEU_VALUE_EXE_CORO || ($coro.Dyn->Exe.status!=CEU_EXE_STATUS_YIELDED)) {                
                        ceu_gc_dec_val($coro);
                        CEU_ERROR_CHK_PTR (
                            continue,
                            "expected yielded coro",
                            ${this.toerr()}
                        );
                    }

                    ${this.args.mapIndexed { i,e ->
                        e.code() + """
                            #ifdef CEU_LEX
                                CEU_ERROR_CHK_PTR (
                                    { ceu_gc_dec_val($coro); continue; },
                                    ceu_lex_chk_own(ceu_acc, $coro.Dyn->Any.lex),
                                    ${this.toerr()}
                                );
                            #endif
                            ${this.idx("args_$n")}[$i] = CEU_ACC_KEEP();
                        """
                    }.joinToString("")}
                    
                    CEUX ceux_$n = {
                        $coro.Dyn->Exe.clo,
                        {.exe = (CEU_Exe*) $coro.Dyn},
                        CEU_ACTION_RESUME,
                        CEU4(ceux COMMA)
                        CEU_LEX_X($coro.Dyn->Exe.depth COMMA)
                        ${this.args.size},
                        ${this.idx("args_$n")}
                    };
                    $coro.Dyn->Exe.clo->proto(&ceux_$n);
                    ceu_gc_dec_val($coro);
                    ${this.check_error_aborted("continue", this.toerr())}
                } -- CALL | ${this.dump()}
            """
            }
            is Expr.Yield -> {
                """
                { -- YIELD ${this.dump()}
                    ${this.e.code()}
                    ceux->exe->status = CEU_EXE_STATUS_YIELDED;
                    ceux->exe->pc = $n;
                #ifdef CEU_LEX
                    ceux->exe->depth = ceux->depth;
                    CEU_ERROR_CHK_PTR (
                        continue,
                        ceu_lex_chk_own(ceu_acc, (CEU_Lex) { CEU_LEX_MUTAB, 1 }),
                        ${this.toerr()}
                    );
                #endif
                    return;
                case $n: -- YIELD ${this.dump()}
                    if (ceux->act == CEU_ACTION_ABORT) {
                        //CEU_ACC((CEU_Value) { CEU_VALUE_NIL }); // to be ignored in further move/checks
                        continue;
                    }
                #if CEU >= 4
                    if (ceux->act == CEU_ACTION_ERROR) {
                        continue;
                    }
                #endif
                #ifdef CEU_LEX
                    ceux->depth = ceux->exe->depth;
                #endif
                    ceu_gc_dec_val(ceu_acc);
                    ceu_acc = (ceux->n > 0) ? ceux->args[0] : (CEU_Value) { CEU_VALUE_NIL };
                }
            """
            }

            is Expr.Spawn -> {
                val blk = this.up_first { it is Expr.Do } as Expr.Do
                val blkc = blk.idx("block_${blk.n}")
                val tsks = this.idx("tsks_$n")
                val depth = if (this.tsks == null) "ceux->depth" else "$tsks.Dyn->Any.lex.depth"
                """
                { -- SPAWN | ${this.dump()}
                    ${(!this.is_mem()).cond { """
                        CEU_Value ceu_tsks_$n;
                        CEU_Value ceu_args_$n[${this.args.size}];
                    """ }}

                    ${(CEU>=5 && this.tsks!==null).cond {
                        this.tsks!!.code() + """
                            $tsks = ceu_acc;                            
                            if (ceu_acc.type != CEU_VALUE_TASKS) {
                                CEU_ERROR_CHK_PTR (
                                    continue,
                                    "invalid pool",
                                    ${this.toerr()}
                                );
                            }
                        """
                    }}
                    
                    ${this.args.mapIndexed { i,e ->
                        e.code() + """
                            #ifdef CEU_LEX
                                CEU_ERROR_CHK_PTR (
                                    continue,
                                    ceu_lex_chk_own(ceu_acc, (CEU_Lex) { CEU_LEX_MUTAB, $depth }),
                                    ${this.toerr()}
                                );
                            #endif
                            ${this.idx("args_$n")}[$i] = CEU_ACC_KEEP();
                        """
                    }.joinToString("")}

                    ${this.tsk.code()}
                    CEU_Dyn* ceu_a_$n = ${when {
                        (CEU<5 || this.tsks===null) -> "(CEU_Dyn*)ceu_task_up(ceux)"
                        else -> "$tsks.Dyn"
                    }};
                    CEU_Block* ceu_b_$n = ${this.tsks.cond2({"NULL"}, {"&$blkc"})};
                    CEU_Value ceu_exe_$n = ceu_create_exe_task(ceu_acc, ceu_a_$n, ceu_b_$n CEU_LEX_X(COMMA $depth));
                    CEU_ACC(ceu_exe_$n);
                    CEU_ERROR_CHK_ERR(continue, ${this.toerr()});
                    
                #ifdef CEU_LEX
                    CEU_ERROR_CHK_PTR (
                        continue,
                        ceu_lex_chk_own(ceu_acc,
                            ${if (CEU>=5 && this.tsks!==null) {
                                "ceu_a_$n->Any.lex"
                            } else {
                                "(CEU_Lex) { CEU_LEX_IMMUT, ceux->depth }"  
                            }}
                        ),
                        ${this.toerr()}
                    );
                #endif
        
                    ${(CEU>=5 && this.tsks!==null).cond { """
                        if (ceu_acc.type != CEU_VALUE_NIL)
                    """ }}
                    {
                        ceu_acc = (CEU_Value) { CEU_VALUE_NIL };
                        CEUX ceux_$n = {
                            ceu_exe_$n.Dyn->Exe.clo,
                            {.exe = (CEU_Exe*) ceu_exe_$n.Dyn},
                            CEU_ACTION_RESUME,
                            ceux,
                            CEU_LEX_X(ceu_exe_$n.Dyn->Exe.depth COMMA)
                            ${this.args.size},
                            ${this.idx("args_$n")}
                        };
                        ceu_exe_$n.Dyn->Exe.clo->proto(&ceux_$n);
                        CEU_ERROR_CHK_ERR({ceu_gc_dec_val(ceu_exe_$n);continue;}, ${this.toerr()});
                        if (CEU_ESCAPE != CEU_ESCAPE_NONE) {
                            ceu_gc_dec_val(ceu_exe_$n);
                            continue;
                        }                                                            
                        ceu_gc_dec_val(ceu_acc);
                        ${this.check_aborted("{ceu_gc_dec_val(ceu_exe_$n);continue;}")}
                        ceu_acc = ceu_exe_$n;
                    }
                } -- SPAWN | ${this.dump()}
                """
            }
            is Expr.Delay -> """
                -- DELAY | ${this.dump()}
                ceux->exe_task->time = CEU_TIME;
            """
            is Expr.Pub -> {
                val set = this.idx( "val_$n")
                val exe = if (this.tsk !== null) "" else {
                    this.up_first_task_outer().let { outer ->
                        val n = this.up_all_until() {
                            it is Expr.Proto && it.tk.str=="task'" && !it.fake
                        }
                            .filter { it is Expr.Proto } // but count all protos in between
                            .count() - 1
                        "(ceux->exe_task${"->clo->up_nst".repeat(n)})"
                    }
                }
                """
                { -- PUB | ${this.dump()}
                    ${this.is_dst().cond{ """
                        ${this.dcl("CEU_Value")} $set = CEU_ACC_KEEP();
                    """ }}
                    CEU_Value ceu_tsk_${G.N}; {
                        ${this.tsk.cond2({"""
                            ${it.code()}
                            ceu_tsk_${G.N} = ceu_acc;
                            if (!ceu_istask_val(ceu_tsk_${G.N})) {
                                CEU_ERROR_CHK_PTR (
                                    continue,
                                    "expected task",
                                    ${this.toerr()}
                                );
                            }
                        """},{"""
                            ceu_tsk_${G.N} = ceu_dyn_to_val((CEU_Dyn*)$exe);
                        """})}
                    }
                    """ + when {
                        this.is_dst() -> """
                            #ifdef CEU_LEX
                            CEU_ERROR_CHK_PTR (
                                continue,
                                ceu_lex_chk_own($set, (CEU_Lex) { CEU_LEX_MUTAB, ceu_tsk_${G.N}.Dyn->Any.lex.depth }),
                                ${this.toerr()}
                            );
                            #endif
                            ceu_gc_dec_val(ceu_tsk_${G.N}.Dyn->Exe_Task.pub);
                            ceu_tsk_${G.N}.Dyn->Exe_Task.pub = $set;
                        """
                        this.is_drop() -> error("TODO: drop pub")
                        else -> """
                            CEU_ACC(ceu_tsk_${G.N}.Dyn->Exe_Task.pub);                        
                        """
                    } + """
                }
                """
            }
            is Expr.Toggle -> {
                val id = this.idx( "tsk_$n")
                """
                {  -- TOGGLE | ${this.dump()}
                    ${this.tsk.code()}
                    ${this.dcl("CEU_Value")} $id = CEU_ACC_KEEP();
                    ${this.on.code()}
                    {   -- TOGGLE | ${this.dump()}
                        int on = ceu_as_bool(ceu_acc);
                        int ceu_err_$n = 0;
                        if (!ceu_istask_val($id)) {
                            CEU_ERROR_CHK_PTR (
                                continue,
                                "expected yielded task",
                                ${this.toerr()}
                            );
                        }
                        if (!ceu_err_$n && on && $id.Dyn->Exe_Task.status!=CEU_EXE_STATUS_TOGGLED) {                
                            CEU_ERROR_CHK_PTR (
                                {ceu_err_$n = 1;},
                                "expected toggled task",
                                ${this.toerr()}
                            );
                        }
                        if (!ceu_err_$n && !on && $id.Dyn->Exe_Task.status!=CEU_EXE_STATUS_YIELDED) {                
                            CEU_ERROR_CHK_PTR (
                                {ceu_err_$n = 1;},
                                "expected yielded task",
                                ${this.toerr()}
                            );
                        }
                        ceu_gc_dec_val($id);
                        if (ceu_err_$n) {
                            continue;
                        }
                        $id.Dyn->Exe_Task.status = (on ? CEU_EXE_STATUS_YIELDED : CEU_EXE_STATUS_TOGGLED);
                    }
                }
            """
            }
            is Expr.Tasks -> {
                val blk = this.up_first { it is Expr.Do } as Expr.Do
                val blkc = blk.idx("block_${blk.n}")
                """
                {  -- TASKS | ${this.dump()}
                    ${this.max.code()}
                    CEU_Value ceu_tsks_$n = ceu_create_tasks(ceux, &$blkc, ceu_acc CEU_LEX_X(COMMA ceux->depth));
                    CEU_ACC(ceu_tsks_$n);
                    CEU_ERROR_CHK_ERR(continue, ${this.toerr()});
                }
                """
            }

            is Expr.Nat -> {
                val body = G.nats[this.n]!!.let { (set, str) ->
                    var x = str
                    for (dcl in set) {
                        val idx = (dcl.fnex() as Expr.Dcl).idx(this)
                        //println(setOf(x, v))
                        x = x.replaceFirst("XXX", idx)
                    }
                    x
                }
                when (this.tk_.tag) {
                    null   -> """
                        CEU_ACC(((CEU_Value) { CEU_VALUE_NIL }));
                        $body 
                        ${this.check_error_aborted("continue", this.toerr())}
                    """
                    ":pre" -> {
                        pres.add(Pair("",body))
                        "CEU_ACC(((CEU_Value) { CEU_VALUE_NIL }));"
                    }
                    ":ceu" -> "CEU_ACC($body);"
                    else -> {
                        val (TAG,Tag) = this.tk_.tag.drop(1).let {
                            Pair(it.uppercase(), it.first().uppercase()+it.drop(1))
                        }
                        "CEU_ACC(((CEU_Value){ CEU_VALUE_$TAG, {.$Tag=($body)} }));"
                    }
                }
            }
            is Expr.Acc -> this.tk.str.idc()
            is Expr.Nil  -> "nil"
            is Expr.Tag  -> '"' + this.tk.str + '"'
            is Expr.Bool -> this.tk.str
            is Expr.Char -> "CEU_ACC(((CEU_Value) { CEU_VALUE_CHAR, {.Char=${this.tk.str}} }));"
            is Expr.Num  -> this.tk.str

            is Expr.Tuple -> "{ __type=\"tuple\", ${this.args.map { it.code() }.joinToString(",")} }\n"
            is Expr.Vector -> {
                val id_vec = this.idx("vec_$n")
                """
                { -- VECTOR | ${this.dump()}
                    ${this.dcl()} $id_vec = ceu_create_vector(CEU_LEX_X(ceux->depth));
                    ${this.args.mapIndexed { i, it ->
                        it.code() + """
                            assert(NULL == ceu_col_set($id_vec, (CEU_Value) { CEU_VALUE_NUMBER, {.Number=$i} }, ceu_acc));
                        """
                    }.joinToString("")}
                    CEU_ACC($id_vec);
                }
            """
            }
            is Expr.Dict -> {
                val id_dic = this.idx("dic_$n")
                val id_key = this.idx("key_$n")
                """
                { -- DICT | ${this.dump()}
                    ${this.dcl()} $id_dic = ceu_create_dict(CEU_LEX_X(ceux->depth));
                    ${this.args.map { """
                        {
                            ${it.first.code()}
                            ${this.dcl()} $id_key = CEU_ACC_KEEP();
                            ${it.second.code()}
                            CEU_Value ceu_val_$n = CEU_ACC_KEEP();
                            CEU_ERROR_CHK_PTR (
                                continue,
                                ceu_col_set(${id_dic}, $id_key, ceu_val_$n),
                                ${this.toerr()}
                            );
                            ceu_gc_dec_val($id_key);
                            ceu_gc_dec_val(ceu_val_$n);
                        }
                    """ }.joinToString("")}
                    CEU_ACC($id_dic);
                }
            """
            }
            is Expr.Index -> {
                val idx = this.data().let { if (it === null) -1 else it.first!! }
                val id_col = this.idx("col_$n")
                val id_val = this.idx("val_$n")
                """
                { -- INDEX | ${this.dump()}
                    -- VAL
                    ${this.is_dst().cond { """
                        ${this.dcl()} $id_val = CEU_ACC_KEEP();
                    """ }}
                    
                    -- COL
                    ${this.col.code()}
                    ${this.dcl()} $id_col = CEU_ACC_KEEP();

                    // IDX
                    ${if (idx == -1) {
                        this.idx.code()
                    } else {
                        """
                        CEU_ACC(((CEU_Value) { CEU_VALUE_NUMBER, {.Number=$idx} }));
                        """
                    }}
                    CEU_Value ceu_idx_$n = CEU_ACC_KEEP();
                """ +
                when {
                    this.is_dst() -> """
                        { -- INDEX | DST | ${this.dump()}
                            char* ceu_err_$n = ceu_col_set($id_col, ceu_idx_$n, $id_val);
                            ceu_gc_dec_val($id_col);
                            ceu_gc_dec_val(ceu_idx_$n);
                            ceu_acc = $id_val;
                            CEU_ERROR_CHK_PTR (
                                continue,
                                ceu_err_$n,
                                ${this.toerr()}
                            );
                        }
                        """
                    this.is_drop() -> {
                        val depth = this.base()!!.depth_diff()
                        """
                        { -- INDEX | DROP | ${this.dump()}
                            CEU_ACC((CEU_Value) { CEU_VALUE_NIL });     // ceu_acc may be equal to $idx (hh_05_coro)
                            CEU_Value ceu_$n = ceu_col_get($id_col, ceu_idx_$n);
                            ceu_gc_inc_val(ceu_$n);
                            char* ceu_err_$n = ceu_col_set($id_col, ceu_idx_$n, (CEU_Value) { CEU_VALUE_NIL });
                            ceu_gc_dec_val($id_col);
                            CEU_ERROR_CHK_PTR (
                                continue,
                                ceu_drop(ceu_$n, ceux->depth-$depth),
                                ${this.fupx().toerr()}
                            );
                            CEU_ACC(ceu_$n);
                            ceu_gc_dec_val(ceu_$n);
                        }
                    """
                    }
                    else -> """
                        CEU_ACC(ceu_col_get($id_col, ceu_idx_$n));
                        ceu_gc_dec_val($id_col);
                        ceu_gc_dec_val(ceu_idx_$n);
                        CEU_ERROR_CHK_ERR(continue, ${this.toerr()});
                    """
                } + """
                }
                """
            }
            is Expr.Call -> this.clo.code() + "(" + this.args.map { it.code() }.joinToString(", ") + ")\n"
        }
    }
}
