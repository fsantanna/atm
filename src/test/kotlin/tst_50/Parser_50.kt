package tst_50

import atm.*
import org.junit.Test

class Parser_50 {
    @Test
    fun aa_01_func_nested() {
        val l = lexer(
            """
            func' :nested () { nil }
        """
        )
        val parser = Parser(l)
        val e = parser.expr()
        assert(e.to_str() == "(func' :nested () {\nnil;\n})") { e.to_str() }
        //assert(trap { parser.expr() } == "anon : (lin 2, col 18) : expected \"(\" : have \":nested\"")
    }
    @Test
    fun aa_02_coro_nested() {
        val l = tst_04.lexer(
            """
            coro' :nested () { nil }
        """
        )
        val parser = Parser(l)
        val e = parser.expr()
        assert(e.to_str() == "(coro' :nested () {\nnil;\n})") { e.to_str() }
        //assert(trap { parser.expr() } == "anon : (lin 2, col 18) : expected \"(\" : have \":nested\"")
    }
    @Test
    fun aa_03_task_err() {
        val l = lexer("""
            task' :xxx () {}
        """.trimIndent())
        val parser = Parser(l)
        //assert(trap { parser.expr() } == "anon : (lin 1, col 1) : invalid task : unexpected \":xxx\"")
        assert(trap { parser.expr() } == "anon : (lin 1, col 7) : expected \"(\" : have \":xxx\"")
    }
    @Test
    fun aa_04_task() {
        val l = lexer("task' (a,b) :nested { 10 }")
        val parser = Parser(l)
        val e = parser.expr()
        assert(e.to_str() == "(task' (a,b) :nested {\n10;\n})") { e.to_str() }
    }

}
