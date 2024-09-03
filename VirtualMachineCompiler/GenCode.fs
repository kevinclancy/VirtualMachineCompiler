﻿module GenCode

open TargetCode
open Syntax
open Environment
open GenComputation

/// Generate code to perform `e1 'binop' e2` where 'binop' is a binary operation implemented by `instr`
///
/// ## Parameters
///
/// * ctxt - the context of the operation
/// * e1 - the left operand
/// * e2 - the right operand
/// * instr - an instruction that pops `v1` and `v2` from the stack and pushes `v1 'binop' v2`,
///           where `v2` is the value on the top of the stack and `v1` is the value directly below
///
/// ## Returns
///
/// * 1 - the additional stack size (beyond its starting size) needed to execute the code
/// * 2 - the type of the result of the binary operation
/// * 3 - the list of generated instructions, which pop the arguments and push the result of the binary operation
let rec binOp (ctxt : Context) (e1 : Expr) (e2 : Expr) (instr : Instruction) : Gen<int * Ty * List<Instruction>> =
    gen {
        let! depth1, ty1, code1 = genExprR ctxt e1
        let! depth2, ty2, code2 = genExprR ctxt e2
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
        return max (depth1) (depth2 + 1), ty1, List.concat [code1 ; code2 ; [instr]]
    }

/// Generate the lvalue of the expression `e`
///
/// ## Parameters
///
/// * ctxt - the context that e occurs in
/// * e - the expression to compute the l-value of
///
/// ## Returns
///
/// * 1 - The additional stack size (beyond its starting size) needed to execute the generated instructions
/// * 2 - The type of the expression `e`
/// * 3 - The generated list of instructions, which push the l-value of `e` onto the stack.
and genExprL (ctxt : Context) (e : Expr) : Gen<int * Ty * List<Instruction>> =
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
    | IntLiteral(_) ->
        error "integer literals cannot occur as l-expressions" e.Range
    | Var(name, rng) ->
        gen {
            let loadInstruction =
                match ctxt.varCtxt[name].address with
                | Local(addr) ->
                    LoadRC addr
                | Global(addr) ->
                    LoadC addr

            return (1, ctxt.varCtxt[name].ty, [loadInstruction])
        }

/// Generate a sequence of instructions that pushes the r-value of
/// the expression 'e' onto the stack
///
/// ## Parameters
///
/// * ctxt - The context that the expression `e` appears in
/// * e - The expression to compute the r-value of
///
/// ## Returns
///
/// * 1 - The additional stack size (beyond its starting size) needed to execute the generated instructions
/// * 2 - The type of `e`
/// * 3 - A list of instructions that push the r-value of `e` onto the stack
and genExprR (ctxt : Context) (e : Expr) : Gen<int * Ty * List<Instruction>> =
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
    | Gt(e1, e2, _) ->
        binOp ctxt e1 e2 Instruction.Gt
    | Lt(e1, e2, _) ->
        binOp ctxt e1 e2 Instruction.Lt
    | Assign(e1, e2, rng) ->
        gen {
            let! depth1, ty1, code1 = genExprL ctxt e1
            let! depth2, ty2, code2 = genExprR ctxt e2

            do!
                match Ty.IsEqual ty1 ty2 with
                | true ->
                    pass
                | false ->
                    error "Types on the left and right-hand side of assignment are unequal" rng

            return (max depth2 (depth1 + ty2.Size), ty1, List.concat [code2 ; code1 ; [Store ty2.Size]])
        }
    | Var(name, rng) ->
        gen {
            let! loadInstruction =
                match Map.tryFind name (ctxt.varCtxt) with
                | Some({ address = Local(addr) ; ty = _ }) ->
                    gen {
                        return LoadRC addr
                    }
                | Some({ address = Global(addr) ; ty = _ }) ->
                    gen {
                        return LoadC addr
                    }
                | None ->
                    error ("Undeclared variable '" + name + "'") rng


            return (ctxt.varCtxt[name].ty.Size, ctxt.varCtxt[name].ty, [loadInstruction ; Load ctxt.varCtxt[name].ty.Size])
        }
    | IntLiteral(c, _) ->
        gen {
            return (1, Int, [LoadC c])
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

            let! argResults = letAll (List.map (genExprR ctxt) args)
            let _, argTys, argInstructionLists = List.unzip3 argResults

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
            let retAllocDepth = max (sizeRet - sizeArgs) 0
            let markDepth = 2
            let funAddrDepth = 1
            let code = List.concat [
                [Alloc retAllocDepth]
                List.concat argInstructionLists
                [Mark]
                [LoadCAddr funDecl.addr]
                [Call]
                [Slide(max (sizeArgs - sizeRet) 0, sizeRet)]
            ]

            let foldArg ((maxDepth, currDepth) : int * int)
                        ((argDepth, argTy, _) : int * Ty * List<Instruction>) : int * int =
                (max maxDepth (currDepth + argDepth), currDepth + argTy.Size)

            let argsDepth = fst (List.fold foldArg (0,0) argResults)

            return (argsDepth + retAllocDepth + markDepth + funAddrDepth, funDecl.decl.retTy, code)
        }

/// Let `n` be the value on top of the stack. `check k addrJumpTable` generates an instruction sequence
/// that
///
/// * jumps to `addrJumpTable + n` if 0 <= `n` < `k`
/// * and jumps to `addrJumpTable + k` otherwise
///
/// ## Returns
///
/// * 1 - The additional stack size (beyond its starting size) needed to execute the generated instructions
/// * 2 - The generated instruction sequence
and check (k : int) (addrJumpTable : int) : Gen<int * List<Instruction>> =
    gen {
        let! addrHandleBoundsViolation = getFreshSymbolicAddr
        return 2, [
            // handle bounds violation if top of stack is less than 0
            Dup
            LoadC 0
            Instruction.Geq
            JumpZ addrHandleBoundsViolation

            // handle bounds violation if top of stack is greater than k
            Dup
            LoadC k
            Instruction.Leq
            JumpZ addrHandleBoundsViolation

            JumpI addrJumpTable

            SymbolicAddress addrHandleBoundsViolation
            Pop
            LoadC k
            JumpI addrJumpTable
        ]
    }

/// Generates a sequence of instructions to execute statement `s` while leaving the stack unchanged
///
/// ## Parameters
///
/// * ctxt - The context that `s` occurs in
/// * s - The statement to generate code for
///
/// ## Returns
///
/// * 1 - The additional stack size (beyond its starting size) needed to execute the generated instructions
/// * 2 - The generated instruction sequence
and genStat (ctxt : Context) (s : Stat) : Gen<int * List<Instruction>> =
    match s with
    | ExprStat(e, _) ->
        gen {
            let! depth, _, code = genExprR ctxt e
            return depth, List.concat [code ; [Pop]]
        }
    | IfThen(cond, thenClause, _) ->
        gen {
            let! condDepth, condTy, condCode = genExprR ctxt cond
            do!
                match condTy with
                | Int ->
                    pass
                | _ ->
                    error "Condition expected to have type int" cond.Range
            let! thenDepth, thenCode = genStat ctxt thenClause
            let! addr = getFreshSymbolicAddr
            return (
                max condDepth thenDepth,
                List.concat [condCode ; [JumpZ addr] ; thenCode ; [SymbolicAddress addr]]
            )
        }
    | IfThenElse(cond, thenClause, elseClause, _) ->
        gen {
            let! condDepth, condTy, condCode = genExprR ctxt cond
            do!
                match condTy with
                | Int ->
                    pass
                | _ ->
                    error "Condition expected to have type int" cond.Range
            let! thenDepth, thenCode = genStat ctxt thenClause
            let! elseDepth, elseCode = genStat ctxt elseClause
            let! addrElseBegin = getFreshSymbolicAddr
            let! addrAfterElse = getFreshSymbolicAddr
            return (
                List.max [condDepth ; thenDepth ; elseDepth],
                List.concat [
                    condCode
                    [JumpZ addrElseBegin]
                    thenCode
                    [Jump addrAfterElse]
                    [SymbolicAddress addrElseBegin]
                    elseCode
                    [SymbolicAddress addrAfterElse]
                ]
            )
        }
    | While(cond, body, _) ->
        gen {
            let! condDepth, condTy, condCode = genExprR ctxt cond
            do!
                match condTy with
                | Int ->
                    pass
                | _ ->
                    error "Condition expected to have type int" cond.Range
            let! bodyDepth, bodyCode = genStat ctxt body
            let! addrBeforeCond = getFreshSymbolicAddr
            let! addrAfterLoop = getFreshSymbolicAddr
            return (
                max condDepth bodyDepth,
                List.concat [
                    [SymbolicAddress addrBeforeCond]
                    condCode
                    [JumpZ addrAfterLoop]
                    bodyCode
                    [Jump addrBeforeCond]
                    [SymbolicAddress addrAfterLoop]
                ]
            )
        }
    | For(init, cond, incr, body, _) ->
        gen {
            let! initDepth, initCode = genStat ctxt init
            let! condDepth, condTy, condCode = genExprR ctxt cond
            do!
                match condTy with
                | Int ->
                    pass
                | _ ->
                    error "Condition expected to have type int" cond.Range
            let! incrDepth, incrCode = genStat ctxt incr
            let! bodyDepth, bodyCode = genStat ctxt body
            let! addrEvaluateCond = getFreshSymbolicAddr
            let! addrAfterLoop = getFreshSymbolicAddr
            return (
                List.max [initDepth ; condDepth ; incrDepth ; bodyDepth],
                List.concat [
                    initCode
                    [SymbolicAddress addrEvaluateCond]
                    condCode
                    [JumpZ addrAfterLoop]
                    bodyCode
                    incrCode
                    [Jump addrEvaluateCond]
                    [SymbolicAddress addrAfterLoop]
                ]
            )
        }
    | Switch(scrutinee, cases, deflt, _) ->
        gen {
            let! addrJumpTable = getFreshSymbolicAddr
            let! addrAfterSwitch = getFreshSymbolicAddr
            let! checkBoundsDepth, checkBoundsInstructions = check (cases.Length - 1) addrJumpTable
            let! scrutineeDepth, scrutineeTy, scrutineeCode = genExprR ctxt scrutinee
            do!
                match scrutineeTy with
                | Int ->
                    pass
                | _ ->
                    error "Case scrutinee expected to have type int" scrutinee.Range

            let makeCase (c : SwitchCase) : Gen<int * int * List<Instruction>> =
                gen {
                    let! bodyDepth, bodyInstructions = genStat ctxt c.statement
                    let! addrCase = getFreshSymbolicAddr
                    return bodyDepth, addrCase , List.concat [
                        [SymbolicAddress addrCase]
                        bodyInstructions
                        [Jump addrAfterSwitch]
                    ]
                }

            let! cases = letAll (List.map makeCase cases)
            let caseDepths , caseAddresses, caseBodies = List.unzip3 cases
            return (
                List.max (scrutineeDepth :: checkBoundsDepth :: caseDepths),
                List.concat [
                    scrutineeCode
                    checkBoundsInstructions
                    List.concat caseBodies
                    [SymbolicAddress addrJumpTable]
                    List.map (fun addr -> Jump addr) caseAddresses
                    [SymbolicAddress addrAfterSwitch]
                ]
            )
        }
    | Sequence(stat1, stat2, _) ->
        gen {
            let! depth1, code1 = genStat ctxt stat1
            let! depth2, code2 = genStat ctxt stat2
            return (
                max depth1 depth2,
                List.concat [code1 ; code2 ]
            )
        }
    | Return(returnExpr, rng) ->
        gen {
            let! exprDepth, exprTy, exprInstructions = genExprR ctxt returnExpr

            do!
                match Ty.IsEqual ctxt.retTy exprTy with
                | true ->
                    gen {
                        return ()
                    }
                | false ->
                    error ("type of return " + exprTy.ToString() + " does not match declared return type " + ctxt.retTy.ToString()) rng

            let retValueAddr =
                if ctxt.argumentSpace > ctxt.retTy.Size then
                    -(ctxt.argumentSpace + 2)
                else
                    -(ctxt.retTy.Size + 2)
            return (
                exprDepth,
                List.concat [
                    exprInstructions
                    [StoreR(retValueAddr, exprTy.Size)]
                    [Instruction.Return(3 + (max (ctxt.argumentSpace - exprTy.Size) 0))]
                ]
            )
        }
    | ReturnVoid(rng) ->
        gen {
            return (
                0,
                [Instruction.Return (ctxt.argumentSpace + 3)]
            )
        }

/// Generates code for a function declaration
///
/// ## Parameters
///
/// * ctxt - The context the function declaration occurs in
/// * func - The function declaration
///
/// ## Returns
///
/// * 1 - The symbolic address for the function
/// * 2 - A list of instructions that exectues an incarnation of the function
let genFunc (ctxt : Context) (func : FunDecl) : Gen<int * List<Instruction>> =
    gen {
        let! funAddr = getFreshSymbolicAddr
        let localDeclSize = List.sumBy (fun (d : VarDecl) -> d.ty.Size) func.localDecls
        let argumentSize = List.sumBy (fun (d : VarDecl) -> d.ty.Size) func.pars
        let! bodyDepth, bodyInstructions = genStat (ctxtForFunc ctxt funAddr func) func.body
        return funAddr, List.concat [
            [SymbolicAddress funAddr]
            [Enter (localDeclSize + bodyDepth)]
            [Alloc localDeclSize]
            bodyInstructions
            [Instruction.Return <| max (argumentSize - func.retTy.Size) 0]
        ]
    }

/// Generate a list of instructions to execute `prog`
///
/// ## Paramters
///
/// * prog - The program to generate instructions for
///
/// ## Returns
///
/// * The generated list of instructions that executes `prog`
let genProg (prog : Prog) : Gen<List<Instruction>> =
    gen {
        let sizeGlobals = List.sumBy (fun (x : VarDecl) -> x.ty.Size) prog.globals
        let sizeMainReturn = 1
        let sizeOrganizationalCells = 3

        let ctxt = elabGlobals Context.empty 1 prog.globals

        let foldFuncDecl ((ctxt, genFuncs) : Context * List<int * List<Instruction>>) (d : FunDecl) =
            gen {
                let! addr, instructions = genFunc ctxt d
                let ctxt' = {
                    ctxt with
                        funCtxt = ctxt.funCtxt.Add(d.name, { addr = addr ; decl = d })
                        argumentSpace = List.sumBy (fun (v : VarDecl) -> v.ty.Size) d.pars
                        retTy = d.retTy
                }
                return (
                    ctxt',
                    (addr, instructions) :: genFuncs
                )
            }

        let! _, funcList = foldM (ctxt, []) foldFuncDecl prog.funDecls

        let funcAddresses, funcInstructions = List.unzip (List.rev funcList)

        return List.concat [
            [Enter(sizeMainReturn + sizeGlobals + sizeOrganizationalCells)]
            [Alloc(sizeMainReturn + sizeGlobals)]
            [Mark]
            [LoadCAddr(List.last funcAddresses)]
            [Call]
            [Slide(sizeGlobals, 1)]
            [Halt]
            List.concat funcInstructions
        ]
    }
