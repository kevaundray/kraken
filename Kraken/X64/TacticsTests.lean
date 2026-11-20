module

import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Semantics
import Kraken.X64.WP.Basic

private def kprologueTestProgram : Program := []

-- The hygienic state alias must not capture an existing `ss`.
example [layout : Layout] [Labels] (P : Prop) (ss : Nat) (s : MachineData) (hP : P) :
    straightlineStep (layout kprologueTestProgram) ⟨s, layout.start⟩ (fun _ => P) := by
  kprologue kprologueTestProgram with s
  have _ : Nat := ss
  have _ : UInt64 := r15
  have _ : RegZmms := zmms
  have _ : StatusFlags := flags
  have _ : DataMem := mem
  exact hP

/--
error: kprologue: refusing to shadow existing locals: rax
-/
#guard_msgs in
example [layout : Layout] [Labels] (rax : UInt64) (s : MachineData) :
    straightlineStep (layout kprologueTestProgram) ⟨s, layout.start⟩ (fun _ => True) := by
  kprologue kprologueTestProgram with s

section got

private def gotTestAddress : AddrExpr :=
  { base := some .rip, idx := none, disp := .sub (.gotSlot "f") .after_current_instruction }

private def gotTestExecutable (op : Operation .W64) : Executable :=
  { startAddr := 0x20
    program := [{ directive := .instr (.regular .W64 .W64 op), size := 6 }] }

private abbrev gotTestLabels : Labels :=
  { label := fun _ => 0x7000, gotSlot := fun _ => 0x1000 }

private def gotPrologueProgram : Program :=
  [.instr (.regular .W64 .W64 (.mov (.reg .rax) (.imm (.gotSlot "f"))))]

example [layout : Layout] (s : MachineData) :
    straightlineStep (labels := gotTestLabels) (layout gotPrologueProgram)
      ⟨s, layout.start⟩ (fun st => st.data.regs.rax = 0x1000) := by
  kprologue gotPrologueProgram with s
  sym => kstep; tactic =>
  rfl

example (slot pc : Int64) :
    letI : Labels := { label := fun _ => 0x7000, gotSlot := fun _ => slot }
    ConstExpr.interp (.sub (.gotSlot "f") .after_current_instruction) ⟨0, pc⟩ =
      slot - pc := by
  rfl

example [Host] (name : Label) (addr : Int64) (h : Host.gotSlot name = addr)
    (p : Std.Rco Int64) : (ConstExpr.gotSlot name).interp p = addr := by
  exact h

example [Labels] (a b : ConstExpr) (p : Std.Rco Int64) :
    (ConstExpr.add a b).interp p = a.interp p + b.interp p := by
  rfl

example [Labels] (name : Label) (p : Std.Rco Int64) :
    (ConstExpr.label name).interp p = Labels.label name := by
  rfl

example [Layout] (s : MachineData) (post : MachineState → Prop) :
    step1 (gotTestExecutable (.mov (.reg .rax) (.mem gotTestAddress)))
      (labels := gotTestLabels) ⟨s, 0x20⟩ post =
    (s.load 0x1000 .W64 (fun v s => .done ⟨s.setReg .rax v, 0x26⟩)).All post := by
  simp only [step1, Executable.step, gotTestExecutable, Kraken.Executable.directivesAtAddress,
    Kraken.Executable.withAddresses.eq_1, Kraken.Executable.withAddresses.eq_2]
  rfl

example [Layout] (s : MachineData) (post : MachineState → Prop) :
    step1 (gotTestExecutable (.jmp (.mem gotTestAddress)))
      (labels := gotTestLabels) ⟨s, 0x20⟩ post =
    (s.load 0x1000 .W64 (fun target s => .done ⟨s, .ofBitVec target⟩)).All post := by
  simp only [step1, Executable.step, gotTestExecutable, Kraken.Executable.directivesAtAddress,
    Kraken.Executable.withAddresses.eq_1, Kraken.Executable.withAddresses.eq_2]
  rfl

example [Layout] (s : MachineData) (post : MachineState → Prop) :
    step1 (gotTestExecutable (.call (.mem gotTestAddress)))
      (labels := gotTestLabels) ⟨s, 0x20⟩ post =
    (s.load 0x1000 .W64 (fun target s =>
      let rsp := s.regs.get64 .rsp - Width.W64.bytesv
      { s with regs := s.regs.set64 .rsp rsp }.store rsp (w := .W64) (0x26 : Int64).toBitVec
        (fun s => .done ⟨s, .ofBitVec target⟩))).All post := by
  simp only [step1, Executable.step, gotTestExecutable, Kraken.Executable.directivesAtAddress,
    Kraken.Executable.withAddresses.eq_1, Kraken.Executable.withAddresses.eq_2]
  rfl

example [Layout] (s : MachineData) (post : MachineState → Prop) :
    straightlineStep (gotTestExecutable (.mov (.reg .rax) (.mem gotTestAddress)))
      (labels := gotTestLabels) ⟨s, 0x20⟩ post =
    (s.load 0x1000 .W64 (fun v s => .done ⟨s.setReg .rax v, 0x26⟩)).All post := by
  simp only [straightlineStep, Executable.straightline, gotTestExecutable,
    Kraken.Executable.directivesFromAddress,
    Kraken.Executable.withAddresses.eq_1, Kraken.Executable.withAddresses.eq_2]
  rfl

end got
