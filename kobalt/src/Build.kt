import com.beust.kobalt.*
import com.beust.kobalt.plugin.packaging.*
import com.beust.kobalt.plugin.application.*
import com.beust.kobalt.plugin.kotlin.*

object Versions {
    val kotlin = "1.1.50"
    val babel = "0.9"
}

val bs = buildScript {
    repos("http://dl.bintray.com/kotlin/kotlinx")
}

val p = project {
    name = "sojourn-CVG"
    group = "com.empowerops.sojourn"
    artifactId = name
    version = "0.1"


    dependencies {

        compile(file("deps/z3-4.5.0-win-x86/com.microsoft.z3.jar"))
        compile("com.empowerops:babel:${Versions.babel}")
        compile("com.empowerops:babel:jar:sources:${Versions.babel}")

        compile(
                "org.jetbrains.kotlin:kotlin-reflect:${Versions.kotlin}",
                "org.jetbrains.kotlin:kotlin-runtime:${Versions.kotlin}",
                "org.jetbrains.kotlin:kotlin-stdlib:${Versions.kotlin}"
        )

        compile("org.jetbrains.kotlinx:kotlinx-coroutines-core:0.20")
        compile("org.jetbrains.kotlinx:kotlinx-collections-immutable:0.1")
        compile("org.antlr:antlr4-runtime:4.7")
        compile("javax.inject:javax.inject:1")
        compile("com.google.code.findbugs:jsr305:3.0.2")
    }

    dependenciesTest {
        compile("org.testng:testng:6.11")
        compile("org.assertj:assertj-core:3.8.0")
        compile("org.jetbrains.kotlin:kotlin-stdlib:jar:sources:${Versions.kotlin}")
        compile("org.jetbrains.kotlinx:kotlinx-coroutines-core:jar:sources:0.20")
    }

    assemble {
        mavenJars {  }
    }

    test {

        jvmArgs("-Djava.library.path=deps/z3-4.5.0-win-x86")

        include("**/*Fixture.class")
        include("**/*Benchmarks.class")
    }

    application {
        mainClass = "com.example.MainKt"
    }
}
