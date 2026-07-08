plugins {
    kotlin("jvm") version "2.2.0"
}

// val projectArend = gradle.includedBuild("Arend")
group = "org.arend.lang"
version = "1.11.0.3"

repositories {
    mavenCentral()
}

dependencies {
    implementation("org.json:json:20231013")
    implementation(kotlin("reflect"))
    implementation(kotlin("stdlib-jdk8"))
    implementation("org.arend:base")
    implementation("org.arend:cli")
    implementation("org.apache.commons:commons-lang3:3.12.0")
    implementation("commons-cli:commons-cli:1.5.0")
}
