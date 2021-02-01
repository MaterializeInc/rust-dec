# Release checklist

* Update changelogs.

* Update versions in `Cargo.toml`s.

* Update versions in README.

* Commit changes and merge to master.

* Ensure tests have passed.

* ```
  git tag -am 'dec $VERSION' dec-$VERSION
  ```

* ```
  git tag -am 'decnumber-sys $VERSION' decnumber-sys-$VERSION
  ```

* ```
  git push --tags
  ```

* Create a new release on GitHub.

* ```
  (cd dec && cargo publish)
  (cd decnumber-sys && cargo publish)
  ```
