package atm

fun NExpr.fnex (): Expr {
    return G.ns[this]!!
}

fun Expr.fup (): Expr? {
    return G.ups[this.n]?.fnex()
}

fun Expr.fupx (): Expr {
    return this.fup()!!
}

fun cache_ns () {
    G.outer!!.dn_visit {
        G.ns[it.n] = it
    }
}

fun cache_ups () {
    G.outer!!.dn_visit { me ->
        when (me) {
            is Expr.Proto -> {
                G.ups[me.blk.n] = me.n
                me.pars.forEach { G.ups[it.n] = me.n }
            }

            is Expr.Do -> me.es.forEach { G.ups[it.n] = me.n }
            is Expr.Group -> me.es.forEach { G.ups[it.n] = me.n }
            is Expr.Enclose -> me.es.forEach { G.ups[it.n] = me.n }
            is Expr.Escape -> if (me.e !== null) G.ups[me.e.n] = me.n
            is Expr.Dcl -> if (me.src !== null) G.ups[me.src.n] = me.n
            is Expr.Set -> {
                G.ups[me.dst.n] = me.n
                G.ups[me.src.n] = me.n
            }

            is Expr.If -> {
                G.ups[me.cnd.n] = me.n
                G.ups[me.t.n] = me.n
                G.ups[me.f.n] = me.n
            }

            is Expr.Loop -> G.ups[me.blk.n] = me.n
            is Expr.Data -> {}
            is Expr.Drop -> G.ups[me.e.n] = me.n

            is Expr.Catch -> G.ups[me.blk.n] = me.n
            is Expr.Defer -> G.ups[me.blk.n] = me.n

            is Expr.Yield -> G.ups[me.e.n] = me.n
            is Expr.Resume -> {
                G.ups[me.co.n] = me.n
                me.args.forEach { G.ups[it.n] = me.n }
            }

            is Expr.Spawn -> {
                if (me.tsks !== null) G.ups[me.tsks.n] = me.n
                G.ups[me.tsk.n] = me.n
                me.args.forEach { G.ups[it.n] = me.n }
            }

            is Expr.Delay -> {}
            is Expr.Pub -> if (me.tsk !== null) G.ups[me.tsk.n] = me.n
            is Expr.Toggle -> {
                G.ups[me.tsk.n] = me.n
                G.ups[me.on.n] = me.n
            }

            is Expr.Tasks -> G.ups[me.max.n] = me.n

            is Expr.Nat -> {}
            is Expr.Acc -> {}
            is Expr.Nil -> {}
            is Expr.Tag -> {}
            is Expr.Bool -> {}
            is Expr.Char -> {}
            is Expr.Num -> {}
            is Expr.Tuple -> me.args.forEach { G.ups[it.n] = me.n }
            is Expr.Vector -> me.args.forEach { G.ups[it.n] = me.n }
            is Expr.Dict -> {
                me.args.forEach {
                    G.ups[it.first.n] = me.n
                    G.ups[it.second.n] = me.n
                }
            }

            is Expr.Index -> {
                G.ups[me.col.n] = me.n
                G.ups[me.idx.n] = me.n
            }

            is Expr.Call -> {
                G.ups[me.clo.n] = me.n
                me.args.forEach { G.ups[it.n] = me.n }
            }
            is Expr.Uno -> G.ups[me.e.n] = me.n
            is Expr.Bin -> {
                G.ups[me.e1.n] = me.n
                G.ups[me.e2.n] = me.n
            }
        }
    }
}

fun cache_tags () {
    TAGS.forEach {
        G.tags[it] = Tk.Tag(it,G.outer!!.tk.pos.copy())
    }
    G.outer!!.dn_visit {
        when (it) {
            is Expr.Enclose-> G.tags[it.tag.str] = it.tag
            is Expr.Escape -> G.tags[it.tag.str] = it.tag
            is Expr.Data   -> G.tags[it.tk_.str] = it.tk_
            is Expr.Catch  -> if (it.tag !== null) { G.tags[it.tag.str] = it.tag }
            is Expr.Tag    -> G.tags[it.tk_.str] = it.tk_
            else           -> {}
        }
    }
}

fun cache_nonlocs () {
    fun Expr.Proto.to_nonlocs (): List<Expr.Dcl> {
        return this
            .dn_collect { if (it is Expr.Acc) listOf(it) else emptyList() }
            .map { acc -> acc.id_to_dcl(acc.tk.str)!!.let {
                Pair(it, it.to_blk())
            }}
            .filter { (_,blk) -> blk.fup()!=null }
            .filter { (_,blk) -> this.fupx().up_first { it==blk } != null }
            .map { (dcl,_) -> dcl }
            .sortedBy { it.n }
    }
    G.outer!!.dn_visit {
        if (it is Expr.Proto) {
            G.nonlocs[it.n] = it.to_nonlocs().map { it.n }
        }
    }

}