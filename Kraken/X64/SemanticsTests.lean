module

import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

/-! Concrete-evaluation tests of semantics that the native asm tests can't observe. -/

private partial def accessChecks :
    Effects → Option (List (Nat × Nat) × List (Nat × Nat))
  | .done _ => some ([], [])
  | .require_read_access p ok => (accessChecks (ok ())).map fun (rs, ws) => ((p.lower.val, p.upper.val) :: rs, ws)
  | .require_write_access p ok => (accessChecks (ok ())).map fun (rs, ws) => (rs, (p.lower.val, p.upper.val) :: ws)
  | _ => none

/-- 64 bytes of data memory at `0x1000`. -/
private def s : MachineData := { dmem := (List.replicate 64 0).At 0x1000 }

#guard accessChecks (s.loadAvx 0x1000 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1010)], [])
#guard accessChecks (s.loadAvx 0x1000 .W256 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1020)], [])
#guard accessChecks (s.loadAvx 0x1000 .W512 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1000, 0x1040)], [])
#guard accessChecks (s.storeAvx (w := .W128) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1010)])
#guard accessChecks (s.storeAvx (w := .W256) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1020)])
#guard accessChecks (s.storeAvx (w := .W512) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0x1000, 0x1040)])

#guard ([Width.W8, .W16, .W32, .W64].all fun w =>
  accessChecks (s.load 0x1000 w fun _ s => .done ⟨s, 0⟩) ==
    some ([(0x1000, 0x1000 + w.bytes)], []) &&
  accessChecks (s.store (w := w) 0x1000 0 fun s => .done ⟨s, 0⟩) ==
    some ([], [(0x1000, 0x1000 + w.bytes)]))

#guard accessChecks (s.loadAvx 0x1001 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0x1001, 0x1011)], [])
#guard match s.loadAvx 0x1001 .W128 (fun _ s => .done ⟨s, 0⟩) (checkAlign := true) with
  | .gp_unaligned addr bytes => addr == 0x1001 && bytes == 16
  | _ => false
#guard match s.storeAvx (w := .W128) 0x1001 0 (fun s => .done ⟨s, 0⟩) (checkAlign := true) with
  | .gp_unaligned addr bytes => addr == 0x1001 && bytes == 16
  | _ => false

private def wrapping : MachineData :=
  { dmem := (List.replicate 64 0).At 0xfffffffffffffff8 }

#guard accessChecks (wrapping.load 0xffffffffffffffff .W8 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0xffffffffffffffff, UInt64.size)], [])
#guard accessChecks (wrapping.loadAvx 0xfffffffffffffff8 .W128 fun _ s => .done ⟨s, 0⟩) ==
  some ([(0xfffffffffffffff8, UInt64.size), (0, 8)], [])
#guard accessChecks (wrapping.storeAvx (w := .W128) 0xfffffffffffffff8 0 fun s => .done ⟨s, 0⟩) ==
  some ([], [(0xfffffffffffffff8, UInt64.size), (0, 8)])

/-! `cld`/`std` write only the direction flag. -/

private def runOp [Labels] (op : Operation .W64) (s : MachineData) : Option MachineData :=
  let : AddressSize := ⟨.W64⟩
  match op.interp ⟨0, 1⟩ s (fun s => .done ⟨s, 1⟩) (fun _ _ => .unimplemented "jump") with
  | .done st => some st.data
  | _ => none

/-- A state with every status flag set and some register and memory contents. -/
private def busy : MachineData :=
  { s with regs := { rax := 7 }, status := .mk true true true true true true }

example [Labels] : runOp .std busy = some { busy with df := true } := by rfl
example [Labels] : runOp .cld { busy with df := true } = some busy := by rfl
example [Labels] : runOp .cld busy = some busy := by rfl
example [Labels] : (runOp .std busy >>= runOp .std) = some { busy with df := true } := by rfl
example [Labels] : (runOp .std busy >>= runOp .cld) = some busy := by rfl

example [Labels] (op : Operation .W64)
    (hop : op = .bt (.low .rax .W64) (.imm (.int64 0)) ∨
      op = .bts (.low .rax .W64) (.imm (.int64 0))) :
    (let : AddressSize := ⟨.W64⟩
    op.interp ⟨0, 1⟩ busy (fun st => .done ⟨st, 1⟩)
        (fun _ _ => .unimplemented "jump")) =
      undefined (fun flags : StatusFlags =>
        .done ⟨{ busy with status := { flags with cf := true, zf := busy.status.zf } }, 1⟩) := by
  rcases hop with rfl | rfl <;>
    simp only [Operation.interp, BitOffset.interp, ConstExpr.interp] <;> rfl

example [Labels] : ([Operation.bt (.low .rax .W8) (.imm (.int64 0)),
    .bts .ah (.reg .ah)].all fun op =>
  let : AddressSize := ⟨.W64⟩
  match op.interp ⟨0, 1⟩ busy (fun st => .done ⟨st, 1⟩)
      (fun _ _ => .unimplemented "jump") with
  | .unimplemented _ => true
  | _ => false) = true := by rfl

section got

private abbrev gotLabels : Labels :=
  { label := fun _ => 0x7000
    gotSlot := fun name => if name == "f" then 0x1000 else 0x1018 }

private def gotAddress (name : Label := "f") : AddrExpr :=
  { base := some .rip, idx := none, disp := .sub (.gotSlot name) .after_current_instruction }

private def gotState : MachineData :=
  { s with
    dmem := Mem.storeInt (Mem.storeInt (Mem.storeInt s.dmem 0x1000 8 0x5000)
      0x1018 8 0x6000) 0x1020 8 0x9000
    regs := { rax := 0x8000, rsp := 0x1020 } }

private def evalInstr (op : Operation .W64) (st : MachineData := gotState)
    (labels : Labels := gotLabels) : Except String MachineState :=
  let e := Program.fakeLayout [.instr (.regular .W64 .W64 op)]
  e.eval ⟨st, e.addrOf 0⟩ (fun st => st.pc != e.addrOf 0) (some labels)

private def callResult (target : RelRegOrMem) (pc : Int64)
    (labels : Labels := gotLabels) : Bool :=
  let i := Instr.regular .W64 .W64 (.call target)
  (evalInstr (.call target) gotState labels).toOption.map (fun st =>
    st.pc == pc && st.data.regs.rsp == 0x1018 &&
    (Mem.loadInt st.data.dmem 0x1018 8).map (BitVec.ofInt 64) ==
      some ((Program.fakeLayout [.instr i]).addrOf 1).toBitVec) == some true

#guard (evalInstr (.mov (.reg .rax) (.mem (gotAddress)))).toOption.map (·.data.regs.rax) ==
  some 0x5000
#guard (evalInstr (.mov (.reg .rax) (.mem (gotAddress "g")))).toOption.map (·.data.regs.rax) ==
  some 0x6000
#guard (evalInstr (.lea .rax (gotAddress))).toOption.map (·.data.regs.rax) == some 0x1000
#guard (evalInstr (.lea .rax
  { base := some .rip, idx := none, disp := .sub (.label "f") .after_current_instruction }
  )).toOption.map (·.data.regs.rax) == some 0x7000
#guard (evalInstr (.jmp (.mem (gotAddress)))).toOption.map (fun st =>
  st.pc == 0x5000 && st.data == gotState) == some true
#guard (evalInstr (.jmp (.reg .rax))).toOption.map (fun st =>
  st.pc == 0x8000 && st.data == gotState) == some true
#guard (evalInstr (.jmp (.mem
  { base := some (.reg .rsp), idx := none }))).toOption.map (·.pc) == some 0x9000
#guard callResult (.mem (gotAddress)) 0x5000
#guard callResult (.mem (gotAddress "g")) 0x6000
#guard callResult (.reg .rax) 0x8000
#guard callResult (.reg .rsp) 0x1020
#guard callResult (.mem { base := some (.reg .rsp), idx := none }) 0x9000
#guard callResult (.mem { base := some (.reg .rsp), idx := none, disp := .int64 (-8) }) 0x6000
#guard callResult (.mem (gotAddress)) 0x6000
  { gotLabels with gotSlot := fun _ => 0x1018 }

#guard (evalInstr (.mov (.reg .rax) (.mem (gotAddress))) gotState
  { gotLabels with label := fun _ => 0x9000 }).toOption.map (·.data.regs.rax) == some 0x5000
#guard (evalInstr (.mov (.reg .rax) (.mem (gotAddress)))
  { gotState with dmem := Mem.storeInt gotState.dmem 0x1000 8 0x4444 }).toOption.map
    (·.data.regs.rax) == some 0x4444

#guard
  letI : Labels := gotLabels
  letI : AddressSize := ⟨.W64⟩
  accessChecks ((RegOrMem.mem (gotAddress) : RegOrMem .W64).interp
    gotState ⟨0x20, 0x26⟩ (fun v st => .done ⟨st.setReg .rax v, 0x26⟩)) ==
    some ([(0x1000, 0x1008)], [])

#guard match (letI : Labels := gotLabels; letI : AddressSize := ⟨.W64⟩
    (RegOrMem.mem (gotAddress) : RegOrMem .W64).interp
      { gotState with dmem := {} } ⟨0x20, 0x26⟩ (fun _ st => .done ⟨st, 0x26⟩)) with
  | .require_read_access _ ok =>
    match ok () with
    | .nonmem_load _ addr w _ => addr == 0x1000 && w == .W64
    | _ => false
  | _ => false

#guard
  let e := Program.fakeLayout [
    .instr (.regular .W64 .W64 (.mov (.reg .rax) (.mem (gotAddress)))),
    .instr (.regular .W64 .W64 (.jmp (.mem (gotAddress)))) ]
  (e.eval ⟨gotState, e.addrOf 0⟩ (fun st => st.pc == 0x5000) (some gotLabels)).toOption.map
    (fun st => st.data.regs.rax == 0x5000 && st.pc == 0x5000) == some true

#guard (evalInstr (.mov (.mem (gotAddress)) (.reg .rax))).toOption.map
  (fun st => Mem.loadInt st.data.dmem 0x1000 8) == some (some 0x8000)

private def rejectsMissingSlots (i : Instr) : Bool :=
  let e := Program.fakeLayout [.label "f@GOT", .label "g@GOT", .instr i]
  let st := { gotState with
    dmem := Mem.storeInt (Mem.storeInt gotState.dmem 0 8 0x3333) (-1) 8 0x4444 }
  match e.eval ⟨st, e.startAddr⟩ (fun st => st.pc != e.startAddr) with
  | .error msg => msg == "No GOT slot address mapping supplied"
  | .ok _ => false

#guard [Operation.mov (.reg .rax) (.mem (gotAddress)), .lea .rax (gotAddress),
    .mov (.mem (gotAddress)) (.reg .rax),
    .call (.mem (gotAddress)), .jmp (.mem (gotAddress)),
    .jmp (.mem (gotAddress "g"))].all fun op =>
  rejectsMissingSlots (.regular .W64 .W64 op)

#guard
  let e := Program.fakeLayout [.label "f", .label "f@GOT", .label "g@GOT"]
  let labels := e.labels gotLabels.gotSlot
  (labels.gotSlot "f", labels.gotSlot "g") == (0x1000, 0x1018)

private def missingSlotExpressions : List ConstExpr :=
  [.gotSlot "missing", .add (.gotSlot "missing") (.int64 8),
    .sub (.label "f") (.gotSlot "missing")]

#guard missingSlotExpressions.all fun c =>
  [Operation.mov (.reg .rax) (.imm c), .push (.imm c),
    .jmp (.rel c), .call (.rel c),
    .shl (.reg .rax) (.imm8 c), .shr (.reg .rax) (.imm8 c),
    .sar (.reg .rax) (.imm8 c), .shld (.reg .rax) .rcx (.imm8 c),
    .shrd (.reg .rax) .rcx (.imm8 c), .rol (.reg .rax) (.imm8 c),
    .ror (.reg .rax) (.imm8 c), .rcl (.reg .rax) (.imm8 c),
    .rcr (.reg .rax) (.imm8 c)].all fun op =>
      rejectsMissingSlots (.regular .W64 .W64 op)

#guard missingSlotExpressions.all fun c =>
  let dst : AvxDst .W128 := .avx (.xmm .mm0)
  let src : AvxRegOrMem .W128 := .avx (.xmm .mm1)
  [AvxOperation.pshufd dst src c, .palignr dst src c, .pblendw dst src c,
    .vprord dst src c, .vpsrld dst src c, .vpternlogd dst src src c].all fun op =>
      rejectsMissingSlots (.avx .W64 .W128 op)

#guard [1, 6, 15].all fun bytes =>
  let e : Executable :=
    { startAddr := 0x20
      program := [{ directive := .instr (.regular .W64 .W64
        (.mov (.reg .rax) (.mem (gotAddress)))), size := bytes }] }
  (e.eval ⟨gotState, 0x20⟩ (fun st => st.pc != 0x20) (some gotLabels)).toOption.map
    (·.data.regs.rax) == some 0x5000

#guard missingSlotExpressions.all fun c =>
  let a : AddrExpr := { base := some (.reg .rax), idx := none, disp := c }
  [Operation.mov (.reg .rax) (.mem a), .mov (.mem a) (.reg .rax),
    .lea .rax a, .jmp (.mem a), .call (.mem a)].all fun op =>
      rejectsMissingSlots (.regular .W64 .W64 op)

#guard missingSlotExpressions.all fun c =>
  let a : AddrExpr := { base := none, idx := none, disp := c }
  let dst : AvxDst .W128 := .avx (.xmm .mm0)
  [AvxOperation.movups dst (.mem a), .vmovups dst (.mem a),
    .movups (.mem a) dst, .vmovups (.mem a) dst,
    .vmovIn .W64 (.xmm .mm0) (.mem a),
    .vmovOut .W64 (.mem a) (.xmm .mm0)].all fun op =>
      rejectsMissingSlots (.avx .W64 .W128 op)

#guard
  let e : Executable :=
    { startAddr := 0x20
      program := [
        { directive := .instr (.regular .W64 .W64 (.jmp (.rel (.int64 0x1a)))), size := 6 },
        { directive := .instr (.regular .W64 .W64
            (.mov (.reg .rax) (.mem (gotAddress)))), size := 6 } ] }
  match e.eval ⟨gotState, 0x20⟩ (fun st => st.pc == 0x40) with
  | .error msg => msg == "No GOT slot address mapping supplied"
  | .ok _ => false

#guard
  let e := Program.fakeLayout [.instr (.regular .W64 .W64
    (.mov (.reg .rax) (.imm (.gotSlot "missing"))))]
  match e.eval ⟨gotState, e.startAddr⟩ (fun _ => true) with
  | .error msg => msg == "No GOT slot address mapping supplied"
  | .ok _ => false

#guard missingSlotExpressions.all fun c =>
  [0, 1, 2, 4, 8].all fun bytes =>
    let e := Program.fakeLayout [.word bytes c]
    match e.eval ⟨gotState, e.startAddr⟩ (fun _ => true) with
    | .error msg => msg == "No GOT slot address mapping supplied"
    | .ok _ => false

#guard
  let e := Program.fakeLayout [.word 8 (.int64 0)]
  (e.eval ⟨gotState, e.startAddr⟩ (fun _ => true)).isOk

end got
