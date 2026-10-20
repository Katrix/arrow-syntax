scalaVersion := "3.9.0"

lazy val root = rootProject
  .settings(
    name := "arrow-syntax",
    scalacOptions += "-Xcheck-macros",
    libraryDependencies ++= Seq(
      "org.typelevel" %% "cats-core"   % "2.13.0",
      "org.typelevel" %% "weaver-cats" % "0.13.0" % Test
    )
  )
