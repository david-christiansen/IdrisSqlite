SQLite bindings for Idris
========

These SQLite bindings are forked from IdrisWeb.

To install:

Make sure your idris command was built with libffi support (if not rebuild it so - you will need to create a custom.mk file - copy custom.mk-alldeps and edit it)

idris --install sqlite.ipkg

to test installation:

idris --build sqlite_test.ipkg
./sqlite_test

expected output is:

Done
[[DBText "test", DBText "CREATE TABLE test (name INT, age INT)"]]


