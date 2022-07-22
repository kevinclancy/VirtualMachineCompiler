module Typecheck

open Syntax
open CheckComputation

let checkProg (prog : Prog) : Check<Unit> =
    Result ()