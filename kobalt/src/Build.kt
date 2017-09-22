import com.beust.kobalt.*
import com.beust.kobalt.plugin.packaging.*
import com.beust.kobalt.plugin.application.*
import com.beust.kobalt.plugin.kotlin.*

object Versions {
    val kotlin = "1.0.3"
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

        compile(
                "org.jetbrains.kotlin:kotlin-reflect:${Versions.kotlin}",
                "org.jetbrains.kotlin:kotlin-runtime:${Versions.kotlin}",
                "org.jetbrains.kotlin:kotlin-stdlib:${Versions.kotlin}"
        )

        compile(file("babel-0.3.jar"))
        compile("org.jetbrains.kotlinx:kotlinx-collections-immutable:0.1")
        compile("org.antlr:antlr4-runtime:4.7")
        compile("javax.inject:javax.inject:1")
        compile("com.google.code.findbugs:jsr305:3.0.2")
    }

    dependenciesTest {
        compile("org.testng:testng:6.11")
        compile("org.assertj:assertj-core:3.8.0")
    }

    assemble {
        mavenJars {  }
    }

    application {
        mainClass = "com.example.MainKt"
    }
}
