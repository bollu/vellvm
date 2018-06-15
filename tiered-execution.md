# Tiered execution for VE-LLVM
## Why?
1. Allows for compositional reasoning about instruction, terminator, basic block, and
function level execution.

2. Encodes useful theorems directly into the execution, rather than having to "recover" this
as additional lemmas.


## Structure
We divide the "program state" of `(global env, fnid, blkid, pc)` across our execution steps. For example, an instruction does not need to care about the current function or the current basic block. so, we do not pass this to the function which executes instructions

### Instruction Execution

First, we define possible results executing an instruction can have. Informally, there are only three things an instruction can do: 
1. read/write to memory, which is recorded by `Vis` nodes.
2. write to the local environment, which is represented by `IREnvEffect` (`IR` for `InstResult`).
3. call another function, which is represented by `IRCall`.
```coq
Inductive InstResult :=
(** Represent calling a function. IRCall <function-to-call> <args> <instruction ID to resume from> **)
| IRCall: fnid -> list id -> instid -> InstResult
(** Represent modifying the environment **)
| IREnvEffect: env  -> InstResult
```

```coq
(** function to execute instructions **)
Definition execInst: Trace InstResult  := ...(TODO)
```

### Terminator
A terminator can:
1. transfer control to another basic block.
2. return a value from the function.

```coq
Inductive TermResult :=
| TRBreak: bbid -> TermResult
| TRRet: DValue -> TermResult
```

```coq
Definition execTerm : TermResult := ... (TODO)
```

### Basic block Execution
A basic block can:
1. Return from the function
2. Transfer control to another basic block
3. Call another function

```coq
Inductive BBResult :=
| BBRBreak: bbid -> BBResult
| BBRRet: Dvalue -> BBresult
(** Call a function, given the function id, arguments,
and point in the basic block to resume from **)
| BBRCall: fnid -> args -> instid -> bbid -> BBresult
```

When a basic block executes, note that all traces that are generated are finite. If there is a function call, then we return a special state that marks our wish to call a function. So, we can define this using `Fixpoint`, destructing over the list of instructions in the BB.


```coq
Fixpoint execBB (bb: basicblock) : Trace BBResult :=
... (TODO)
```

### Function Execution

A function can:
1. Return a value
2. Transfer control to another function

```coq
Inductive FunctionResult :=
| FRReturn: DValue -> FunctionResult
| FRCall: fnid -> args -> instid -> bbid-> fnid -> FunctionResult.
```

## Toplevel Execution

The toplevel maintains the call stack information, and can either:
1. Handle a call and push a value on the call stack
2. Handle a ret and pop a value from the call stack
3. Handle the ret from main() and return the value
as the value of the program.

##Advantages

This clearly gives us separation of concerns, since the results that each object can produce is clearly deliniated. It also should allow us to prove theorems about how a basic block or instruction executes, without tying the semantics up with the **entire program** (currently, `step`, which executes instructions takes a `cfg` as a parameter, which is basically "rest of the program").


## Disadvantages

I have not implemented and played around with this system yet, so I've quite possibly missed some glaring holes.