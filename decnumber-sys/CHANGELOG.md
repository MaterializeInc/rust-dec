# Changelog

All notable changes to this crate will be documented in this file.

The format is based on [Keep a Changelog], and this crate adheres to [Semantic
Versioning].

## 0.1.5 - 2020-03-10

* Expose the lookup table for converting binary numbers 0-999 to their
  3-character representations, `BIN2CHAR`.

## 0.1.4 - 2020-02-25

* Expose lookup tables for converting DPD to binary: `DPD2BIN`, `DPD2BINK`,
  `DPD2BINM`, `DECCOMBMSD`.

## 0.1.3 - 2020-02-03

* Import a patch that corrects `decDoubleIsSigned` and `decQuadIsSigned`, which
  were previously inverted from their documented behavior.

  This patch comes from the [libdecnumber errata][errata].

## 0.1.2 - 2020-02-01

* Correct documentation links in README, again.

## 0.1.1 - 2020-02-01

* Correct documentation links in README.

## 0.1.0 - 2020-01-31

Initial release.

[Keep a Changelog]: https://keepachangelog.com/en/1.0.0/
[Semantic Versioning]: https://semver.org/spec/v2.0.0.html
[errata]: http://speleotrove.com/decimal/decnumerr.html
