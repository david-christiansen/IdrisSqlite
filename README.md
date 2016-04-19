SQLite bindings for Idris
========

These SQLite bindings are forked from IdrisWeb.

To install:

idris --install sqlite.ipkg

to test installation:

idris --build sqlite_test.ipkg
./sqlite_test

expected output is:

Done
[[DBText "test", DBText "CREATE TABLE test (name INT, age INT)"]]


