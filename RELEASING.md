# Release checklist

* Update changelog(s).

* Update versions in `Cargo.toml`(s).

* Update versions in README.

* Commit changes and merge to master.

* Ensure tests have passed.

* If releasing dec:

  ```
  git tag -am "dec $VERSION" dec-$VERSION
  ```

* If releasing dec-sys:

  ```
  git tag -am "decnumber-sys $VERSION" decnumber-sys-$VERSION
  ```

* Push tags:

  ```
  git push --tags
  ```

* Create a new release on crates.io:

  ```
  (cd dec && cargo publish)
  (cd decnumber-sys && cargo publish)
  ```

# Release permissions

In order to successfully complete the `cargo publish` steps you must be a
member of the "Crate owners" Github team and use an appropriate token through
`cargo login`.
