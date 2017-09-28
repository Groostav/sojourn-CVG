package com.empowerops.sojourn

import kotlinx.collections.immutable.immutableMapOf
import org.assertj.core.api.Assertions.*
import org.testng.annotations.Test


public class EuclideanNormSanityFixture {

    @Test
    fun `when asking for deviation of simple three points should properly calculate`(){

        val p1 = immutableMapOf("x1" to 0.0)
        val p2 = immutableMapOf("x1" to 1.0)
        val p3 = immutableMapOf("x1" to -1.0)

        val (center, dispersion) = findDispersion(listOf(p1, p2, p3))
        
        assertThat(center).isEqualTo(mapOf("x1" to 0.0))
        assertThat(dispersion).isEqualTo(2.0/3.0)
    }

    @Test fun `when asking for dispersion of simple square should properly generate`(){

        val p1 = immutableMapOf("x1" to -1.0, "x2" to -1.0)
        val p2 = immutableMapOf("x1" to -1.0, "x2" to +1.0)
        val p3 = immutableMapOf("x1" to +1.0, "x2" to -1.0)
        val p4 = immutableMapOf("x1" to +1.0, "x2" to +1.0)

        val (center, dispersion) = findDispersion(listOf(p1, p2, p3, p4))

        assertThat(center).isEqualTo(mapOf("x1" to 0.0, "x2" to 0.0))
        assertThat(dispersion).isEqualTo(Math.sqrt(2.0))
    }
}