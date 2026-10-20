scalaVersion := "3.9.0"

homepage      := Some(uri("https://github.com/Katrix/arrow-syntax"))
organization  := "net.katsstuff"
licenses      := Seq("MIT" -> uri("http://opensource.org/licenses/MIT"))
developers    := List(Developer("Katrix", "Kathryn Frid", "katrix97@hotmail.com", uri("http://katsstuff.net/")))
versionScheme := Some("early-semver")
version       := "0.1.0-SNAPSHOT"

lazy val publishSettings = Seq(
  Test / publishArtifact := false,
  scmInfo := Some(
    ScmInfo(
      uri("https://github.com/Katrix/arrow-syntax"),
      "scm:git:github.com/Katrix/arrow-syntax",
      Some("scm:git:github.com/Katrix/arrow-syntax")
    )
  ),
  autoAPIMappings := true,
  publishTo := {
    val centralSnapshots = "https://central.sonatype.com/repository/maven-snapshots/"
    if version.value.endsWith("-SNAPSHOT") then Some("central-snapshots" at centralSnapshots)
    else localStaging.value
  }
)

lazy val root = rootProject
  .settings(
    publishSettings,
    name := "arrow-syntax",
    scalacOptions ++= Seq( "-Xcheck-macros", "-feature", "-deprecation", "-unchecked"),
    libraryDependencies ++= Seq(
      "org.typelevel" %% "cats-core"   % "2.13.0",
      "org.typelevel" %% "weaver-cats" % "0.13.0" % Test
    )
  )
