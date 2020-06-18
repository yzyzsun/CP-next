{ name = "zord"
, dependencies =
  [ "assert"
  , "console"
  , "debug"
  , "effect"
  , "parsing"
  , "psci-support"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
