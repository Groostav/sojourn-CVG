import com.beust.kobalt.*
import com.beust.kobalt.plugin.packaging.*
import com.beust.kobalt.plugin.application.*
import com.beust.kobalt.plugin.kotlin.*

val p = project {
    name = "sojourn-CVG"
    group = "com.empowerops.sojourn"
    artifactId = name
    version = "0.1"

    dependencies {
        compile("org.antlr:antlr4-runtime:4.7")
        compile("javax.inject:javax.inject:1")
        compile("com.google.code.findbugs:jsr305:3.0.2")
    }

    dependenciesTest {
        compile("org.testng:testng:6.11")
    }

    assemble {
        jar {
        }
    }

    application {
        mainClass = "com.example.MainKt"
    }
}
