package com.empowerops.sojourn

import com.empowerops.babel.BabelCompiler
import com.microsoft.z3.Context
import org.assertj.core.api.Assertions.assertThat
import org.testng.annotations.Test;

public class Z3TranscodingFixture {

    val compiler = BabelCompiler()

    @Test fun `when transcoding simple arithmatic should properly resolve`() = runTest(
            sourceExpr = "3 * 4 + 5 / 6 - 1 < 0",
            result = "(< (- (+ (* 3 4) (div 5 6)) 1) 0)"
    )

    private fun runTest(sourceExpr: String, result: String): Unit {

        val walker = BabelZ3TranscodingWalker(Context(), emptyMap())
        compiler.compile(sourceExpr, walker)

        assertThat(walker.transcodedExpr.toString()).isEqualTo(result)
    }
}
