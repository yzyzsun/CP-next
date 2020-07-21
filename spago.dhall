{ name = "zord"
, dependencies =
  [ "ansi"
  , "console"
  , "debug"
  , "node-fs"
  , "node-readline"
  , "parsing"
  , "psci-support"
  , "transformers"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
