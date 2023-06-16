# Package

version = "20230616"
author        = "Emery Hemingway"
description   = "Dhall language evaluator"
license       = "Unlicense"
srcDir        = "src"
installExt    = @["nim"]
bin           = @["dhall/private/cbor_to_dhall", "dhall/private/xml_to_dhall"]


# Dependencies

requires "nim >= 1.2.0", "bigints", "cbor >= 0.7.0", "npeg", "nimSHA2"
