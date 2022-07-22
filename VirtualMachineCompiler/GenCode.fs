module GenCode

open TargetCode
open Syntax
open Environment
open GenComputation


/// compute an upper bound on the number of words that the VM could push onto the stack while executing this
/// expression, excluding calls to other functions
let rec stackOffsetBound (e : Expr) : int =
    match e with
    | Plus(e1, e2, _) ->
        let e1Bound = stackOffsetBound e1
        // while computing e2, the value of e1 is already on the stack
        let e2Bound = (stackOffsetBound e2) + 1
        max (stackOffsetBound e1) (stackOffsetBound e2)
    

let rec binOp (ctxt : Context) (e1 : Expr) (e2 : Expr) (instr : Instruction) : Gen<Ty * List<Instruction>> =
    gen {
        let! ty1, code1 = genExprR ctxt e1
        let! ty2, code2 = genExprR ctxt e2
        do! 
            match ty1 with
            | Int 
            | Ptr(_) ->
                pass
            | _ ->
                error "expected integer or pointer type" e1.Range
        do!
            match ty2 with
            | Int ->
                pass
            | _ ->
                error "expected integer type" e2.Range
        return ty1, List.concat [code1 ; code2 ; [instr]]
    }    

and genExprL (ctxt : Context) (e : Expr) : Gen<Ty * List<Instruction>> =
    match e with
    | Plus(_, _, _)
    | Minus(_, _, _)
    | Times(_, _, _)
    | Eq(_, _, _)
    | Leq(_, _, _)
    | Geq(_, _, _)
    | Lt(_, _, _) ->
        error "binary operations cannot occur as l-expressions" e.Range
    | Assign(_, _, _) ->
        error "assignments cannot occur as l-expressions" e.Range
    | FunCall(_, _, _) ->
        error "function calls cannot occur as l-expressions" e.Range
    | Var(name, rng) ->
        gen {
            let loadInstruction =
                match ctxt.varCtxt[name].address with
                | Local(addr) ->
                    LoadRC addr
                | Global(addr) ->
                    LoadC addr

            return (ctxt.varCtxt[name].ty, [loadInstruction])
        }

and genExprR (ctxt : Context) (e : Expr) : Gen<Ty * List<Instruction>> =
    match e with
    | Plus(e1, e2, _) ->
        binOp ctxt e1 e2 Instruction.Add
    | Minus(e1, e2, _) ->
        binOp ctxt e1 e2 Instruction.Sub
    | Times(e1, e2, _) ->
        binOp ctxt e1 e2 Instruction.Mul
    | Eq(e1, e2, _) ->
        binOp ctxt e1 e2 Instruction.Eq
    | Leq(e1, e2, _) ->
        binOp ctxt e1 e2  Instruction.Leq
    | Geq(e1, e2, _) ->
        binOp ctxt e1 e2 Instruction.Geq
    | Lt(e1, e2, _) ->
        binOp ctxt e1 e2 Instruction.Lt
    | Assign(e1, e2, rng) ->
        gen {
            let! ty1, code1 = genExprL ctxt e1
            let! ty2, code2 = genExprR ctxt e2

            do! 
                match Ty.IsEqual ty1 ty2 with
                | true ->
                    pass
                | false ->
                    error "Types on the left and right-hand side of assignment are unequal" rng
            
            return ty1, List.concat [code1 ; code2 ; [Store 1]]
        }
    | Var(name, _) ->
        gen {
            let loadInstruction =
                match ctxt.varCtxt[name].address with
                | Local(addr) ->
                    LoadRC addr
                | Global(addr) ->
                    LoadC addr

            return (ctxt.varCtxt[name].ty, [loadInstruction ; Load ctxt.varCtxt[name].ty.Size])
        }
    | IntLiteral(c, _) ->
        gen {
            return (Int, [LoadC c])
        }
    | FunCall(name, args, rng) ->
        gen {
            let! funDecl = 
                match ctxt.funCtxt.TryFind(name) with
                | Some(funDecl) ->
                    gen {
                        return funDecl
                    }
                | None ->
                    error ("No function named " + name + " has been declared") rng
            
            let! results = letAll (List.map (genExprR ctxt) args)
            let argTys, argInstructionLists = List.unzip results

            let actualFormalTyComparison = List.zip argTys (List.map (fun (x : VarDecl) -> x.ty) funDecl.decl.pars)

            do!
                match List.tryFindIndex (fun (S,T) -> not (Ty.IsEqual S T)) actualFormalTyComparison with
                | Some(i) ->
                    let (S,T) = actualFormalTyComparison[i]
                    error ("actual type " + S.ToString() + " is not equal to " + T.ToString()) args[i].Range
                | None ->
                    gen {
                        return ()
                    }

            let sizeArgs = List.sum (List.map (fun (T : Ty) -> T.Size) argTys)
            let sizeRet = funDecl.decl.retTy.Size
            let code = List.concat [
                [Alloc <| max (sizeRet - sizeArgs) 0]
                List.concat argInstructionLists
                [Mark] 
                [LoadC funDecl.addr]
                [Call]
                [Slide(max (sizeArgs - sizeRet) 0, sizeRet)]
            ]

            return (funDecl.decl.retTy, code)
        }

and check (highestIndex : int) (addrJumpTable : int) : Gen<List<Instruction>> =
    gen {
        let! addrHandleBoundsViolation = getFreshSymbolicAddr
        return [
            // handle bounds violation if top of stack is less than 0
            Dup  
            LoadC 0
            Instruction.Geq 
            JumpZ addrHandleBoundsViolation

            // handle bounds violation if top of stack is greater than highestIndex
            Dup 
            LoadC highestIndex 
            Instruction.Leq 
            JumpZ addrHandleBoundsViolation

            JumpI addrJumpTable

            SymbolicAddress addrHandleBoundsViolation
            Pop
            LoadC highestIndex
            JumpI addrJumpTable
        ]
    }

and genStat (ctxt : Context) (s : Stat) : Gen<List<Instruction>> =
    match s with
    | ExprStat(e, _) ->
        gen {
            let! _, code = genExprR ctxt e
            return Pop :: code
        }
    | IfThen(cond, thenClause, _) ->
        gen {
            let! condTy, condCode = genExprR ctxt cond 
            do!
                match condTy with
                | Int ->
                    pass
                | _ ->
                    error "Condition expected to have type int" cond.Range
            let! thenCode = genStat ctxt thenClause
            let! addr = getFreshSymbolicAddr 
            return List.concat [condCode ; [JumpZ addr] ; thenCode ; [SymbolicAddress addr]]
        }
    | IfThenElse(cond, thenClause, elseClause, _) ->
        gen {
            let! condTy, condCode = genExprR ctxt cond
            do!
                match condTy with
                | Int ->
                    pass
                | _ ->
                    error "Condition expected to have type int" cond.Range
            let! thenCode = genStat ctxt thenClause
            let! elseCode = genStat ctxt elseClause
            let! addrElseBegin = getFreshSymbolicAddr
            let! addrAfterElse = getFreshSymbolicAddr
            return List.concat [
                condCode
                [JumpZ addrElseBegin]
                thenCode
                [Jump addrAfterElse]
                [SymbolicAddress addrElseBegin]
                elseCode
                [SymbolicAddress addrAfterElse]
            ]
        }
    | While(cond, body, _) ->
        gen {
            let! condTy, condCode = genExprR ctxt cond
            do!
                match condTy with
                | Int ->
                    pass
                | _ ->
                    error "Condition expected to have type int" cond.Range
            let! bodyCode = genStat ctxt body
            let! addrBeforeCond = getFreshSymbolicAddr
            let! addrAfterLoop = getFreshSymbolicAddr
            return List.concat [
                [SymbolicAddress addrBeforeCond]
                condCode
                [JumpZ addrAfterLoop]
                bodyCode
                [Jump addrBeforeCond]
                [SymbolicAddress addrAfterLoop]
            ]
        }
    | For(init, cond, incr, body, _) ->
        gen {
            let! initCode = genStat ctxt init
            let! condTy, condCode = genExprR ctxt cond
            do!
                match condTy with
                | Int ->
                    pass
                | _ ->
                    error "Condition expected to have type int" cond.Range
            let! incrCode = genStat ctxt incr
            let! bodyCode = genStat ctxt body
            let! addrEvaluateCond = getFreshSymbolicAddr
            let! addrAfterLoop = getFreshSymbolicAddr
            return List.concat [
                initCode
                [SymbolicAddress addrEvaluateCond]
                condCode
                [JumpZ addrAfterLoop]
                bodyCode
                incrCode
                [Jump addrEvaluateCond]
                [SymbolicAddress addrAfterLoop]
            ]
        }
    | Switch(scrutinee, cases, deflt, _) ->
        gen {
            let! addrJumpTable = getFreshSymbolicAddr
            let! addrAfterSwitch = getFreshSymbolicAddr
            let! checkBoundsInstructions = check (cases.Length - 1) addrJumpTable
            // TODO: check that the case values are 0 through k-1
            let! scrutineeTy, scrutineeCode = genExprR ctxt scrutinee
            do!
                match scrutineeTy with
                | Int ->
                    pass
                | _ ->
                    error "Case scrutinee expected to have type int" scrutinee.Range

            let makeCase (c : SwitchCase) : Gen<int * List<Instruction>> =
                gen {
                    let! bodyInstructions = genStat ctxt c.statement
                    let! addrCase = getFreshSymbolicAddr
                    return addrCase , List.concat [
                        [SymbolicAddress addrCase]
                        bodyInstructions
                        [Jump addrAfterSwitch]
                    ]
                }

            let! cases = letAll (List.map makeCase cases)
            let caseAddresses, caseBodies = List.unzip cases
            return List.concat [
                scrutineeCode
                checkBoundsInstructions
                List.concat caseBodies
                [SymbolicAddress addrJumpTable]
                List.map (fun addr -> Jump addr) caseAddresses
                [SymbolicAddress addrAfterSwitch]
            ]
        }
    | Sequence(stat1, stat2, _) ->
        gen {
            let! code1 = genStat ctxt stat1
            let! code2 = genStat ctxt stat2
            return List.concat [code1 ; code2 ]
        }
    | Return(returnExpr, rng) ->
        gen {
            let! exprTy,exprInstructions = genExprR ctxt returnExpr

            do!
                match Ty.IsEqual ctxt.retTy exprTy with
                | true ->
                    gen {
                        return ()
                    }
                | false ->
                    error ("type of return " + exprTy.ToString() + " does not match declared return type " + ctxt.retTy.ToString()) rng

            return List.concat [
                exprInstructions
                [StoreR(ctxt.retAddr, exprTy.Size)]
                [Instruction.Return(3 + (max (ctxt.argumentSpace - exprTy.Size) 0))]
            ]
        }
    | ReturnVoid(rng) ->
        gen {
            return [Instruction.Return (ctxt.argumentSpace + 3)]
        }

/// Returns (addr, instructions)
/// where addr is a symbolic address for the function and 
/// instructions is a list of instructions that executes an incarnation of the function
//let genFunc (func : FunDecl) : Gen<int * List<Instruction>> =
//    gen {
//        let addr = getFreshSymbolicAddr

//        return List.concat [
//            [Enter ]
//        ]
//    }

//let genProg (prog : Prog) : Gen<List<Instruction>> =
//    gen {
//        let sizeGlobals = List.sumBy (fun (x : VarDecl) -> x.ty.Size) prog.globals
//        let sizeForbiddenCells = 1
//        let sizeOrganizationalCells = 3 

//        let callMain = [
//            Enter(sizeForbiddenCells + sizeOfGlobals + sizeOrganizationalCells)
//            Alloc(sizeOfGlobals + sizeForbiddenCells)
//            Mark
//            LoadC(0) // todo: should load address of main
//            Call
//            Slide(sizeGlobals, 1)
//            Halt
//        ]


//    }
    