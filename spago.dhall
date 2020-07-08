{ name = "zord"
, dependencies =
  [ "console"
  , "debug"
  , "parsing"
  , "psci-support"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
