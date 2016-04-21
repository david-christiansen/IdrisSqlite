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

To install the type provider:

cd type-provider

idris --install sqlite_provider.ipkg

to run the type-provider demo:

cd ../type_provider-demo

idris --build demo.ipkg

./test

The expected output is:


The speakers are:
name|bio|
"David Christiansen"|"PhD student at ITU"|
"Another Speaker"|null|
"Lots of Speaking"|null|

The talks are:
title|abstract|
"Type Providers and Error Reflection in Idris"|"Let's talk to the outside world!"|
"Monadic Missile Launching"|"Side effects FTW!"|
"An Actuarial DSL"|"Dependently typed life insurance"|

Conference program
name|title|abstract|
"David Christiansen"|"Type Providers and Error Reflection in Idris"|"Let's talk to the outside world!"|
"Another Speaker"|"Monadic Missile Launching"|"Side effects FTW!"|
"Lots of Speaking"|"An Actuarial DSL"|"Dependently typed life insurance"|

ok


To run the error test demo:

cd ../error_test
idris --build error_test.ipkg

The expected output is:

Type checking ./ErrorTest.idr
ErrorTest.idr:30:12-32:1:
When checking right hand side of speakers with expected type
        Query db ["name" ::: TEXT, "bio" ::: TEXT]

When checking argument ok to constructor Queries.Query.Select:
        Bad schema: 
                "name" ::: TEXT 
                "bio" ::: TEXT 
                Expected subschema of 
                        "id" ::: INTEGER 
                        "name" ::: TEXT 
                        "bio" ::: NULLABLE TEXT
ErrorTest.idr:39:33:
When checking right hand side of program with expected type
        Query db
              ["name" ::: TEXT, "title" ::: TEXT, "abstract" ::: TEXT]

When checking argument ok to constructor Queries.Expr.Col:
        The column "speaker_id" was not found with type INTEGER in the
        schema 
                "id" ::: INTEGER 
                "name" ::: TEXT 
                "bio" ::: NULLABLE TEXT 
                "title" ::: TEXT 
                "abstract" ::: TEXT 
                "speaker" ::: INTEGER
