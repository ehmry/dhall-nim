# Package

version       = "0.1.0"
author        = "Emery Hemingway"
description   = "Dhall language evaluator"
license       = "ISC"
srcDir        = "src"
installExt    = @["nim"]
bin           = @["xml_to_dhall"]


# Dependencies

requires "nim >= 1.2.0", "bigints", "cbor >= 0.7.0", "npeg", "nimSHA2"
