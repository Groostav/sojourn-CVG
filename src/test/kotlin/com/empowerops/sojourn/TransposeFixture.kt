package com.empowerops.sojourn

import org.assertj.core.api.Assertions.assertThat
import org.testng.annotations.Test

class TransposeFixture {

    @Test
    fun `when transposing empty matrix should get empty matrix`(){
        assertThat(emptyList<List<Int>>().asTransposedRegular()).isEqualTo(emptyList<List<Int>>())
        assertThat(listOf<List<Int>>(emptyList()).asTransposedRegular()).isEqualTo(emptyList<List<Int>>())
    }
    @Test
    fun `when transposing simple matrix should properly transpose`(){
        val list = listOf(
            listOf("V1AB", "V2AB", "V3AB"),
            listOf("V1C", "V2C", "V3C")
        )

        val result = list.asTransposedRegular()

        assertThat(result.first()).isEqualTo(listOf("V1AB", "V1C"))
        assertThat(result.size).describedAs("the transposed matrix size").isEqualTo(3)
        assertThat(result.first().size).describedAs("the size of the first row in the transposed matrix").isEqualTo(2)
        assertThat(result).isEqualTo(listOf(
            listOf("V1AB", "V1C"),
            listOf("V2AB", "V2C"),
            listOf("V3AB", "V3C")
        ))
    }
}