module TestAddressResolution

open Syntax
open NUnit.Framework
open TargetCode
open Utils
open AddressResolution

[<TestFixture>]
type Fixture () =

    [<SetUp>]
    member this.setup () =
        ()

    [<Test>]
    member this.basicTest1() =
        let input = [
            LoadC 2
            Pop

            SymbolicAddress 0
            LoadC 1
            Dup
            Pop
            Pop
            Jump 0
        ]

        Assert.AreEqual(resolve input, [| LoadC 2 ; Pop ; LoadC 1 ; Dup ; Pop ; Pop ; Jump 2 |])

    [<Test>]
    member this.basicTest2() =
        let input = [
            Jump 0
            LoadC 2
            Pop
            SymbolicAddress 0
        ]

        Assert.AreEqual(resolve input, [| Jump 3 ; LoadC 2 ; Pop |])