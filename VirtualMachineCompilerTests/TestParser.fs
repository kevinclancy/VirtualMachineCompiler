module TestParser

open Syntax
open NUnit.Framework
open Utils

[<TestFixture>]
type Fixture () =

    [<SetUp>]
    member this.setup () =
        ()

    [<Test>]
    member this.parseSum() =
        match parseExpr "3 + 2" with
        | Plus(IntLiteral(3, _), IntLiteral(2, _), _) ->
            ()
        | _ ->
            failwith "expected to parse addition operator"

    [<Test>]
    member this.parseNestedSum() =
        match parseExpr "(4 + 2) + 1" with
        | Plus(Plus(IntLiteral(4, _), IntLiteral(2, _), _), IntLiteral(1, _), _) ->
            ()
        | _ ->
            failwith "expected to parse addition operator"

