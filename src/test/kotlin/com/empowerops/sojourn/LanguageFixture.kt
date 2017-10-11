package com.empowerops.sojourn

import org.assertj.core.api.Assertions.assertThat
import org.testng.annotations.Test

class LanguageFixture {


    @Test fun `when parsing simple decimal string should properly parse`() = runRatioTest("0.1111", 1111 to 10_000)
    @Test fun `when parsing integer string should properly parse`() = runRatioTest("1111", 1111 to 1)
    @Test fun `when parsing funny trailing-dot integer string should properly parse`() = runRatioTest("1111.", 1111 to 1)
    @Test fun `when parsing funny leading-dot integer string should properly parse`() = runRatioTest(".1111", 1111 to 10_000)
    @Test fun `when parsing rational number string should properly parse`() = runRatioTest("12.34", 1234 to 100)

    private fun runRatioTest(str: String, expectedResult: Pair<Int, Int>) {

        fun String.toIntStrict(): Int = toInt().let { when(it) {
            //TODO, this should probably be smarted to allow for the literal max/min value number
            Integer.MAX_VALUE -> throw NumberFormatException("overflow representing $this as integer")
            Integer.MIN_VALUE -> throw NumberFormatException("underflow representing $this as integer")
            else -> it
        }}

        //act
        val numerator = str.replace(".", "").toIntStrict()
        val denominator = when {
            '.' !in str -> 1
            else -> Math.pow(10.0, 0.0+str.length - str.indexOf('.') - 1).toInt()
        }

        val res = numerator to denominator

        //assert
        assertThat(res).isEqualTo(expectedResult)
    }

    @Test fun `when casting a large double to integer should throw number format`(){
        assertThat(1E20.toInt()).isEqualTo(Integer.MAX_VALUE)

        @Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
        assertThat((1E20 as java.lang.Number).intValue()).isEqualTo(Integer.MAX_VALUE)
    }


}