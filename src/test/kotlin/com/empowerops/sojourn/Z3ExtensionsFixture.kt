package com.empowerops.sojourn

import com.microsoft.z3.Context
import org.testng.annotations.Test


class Z3ExtensionsFixture {

    @Test fun `thigns`(): Unit {
        Context().configure {

            val mod = Function("mod", realSort, realSort, returnType = realSort)

            TODO()
        }
    }
}
