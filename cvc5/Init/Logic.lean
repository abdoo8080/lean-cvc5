/-
Copyright (c) 2023-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5.Init.Basic


namespace cvc5

namespace Logic

inductive Arith.Kind
| diff
| nonDiff (linear : Bool) (transcendental : Bool)

inductive Arith.IntReal
| int
| real
| both
def Arith.IntReal.toSmtLib : IntReal → String
| int => "I"
| real => "R"
| both => "IR"

structure Arith where
  kind : Arith.Kind
  intReal : Arith.IntReal
namespace Arith
def toSmtLib (self : Arith) : String :=
  let (pref, suff) :=
    match self.kind with
    | .diff => ("", "DL")
    | .nonDiff l t => (if l then "L" else "N", if t then "AT" else "A")
  pref ++ self.intReal.toSmtLib ++ suff

def lia : Arith := ⟨.nonDiff true false, .int⟩
def lra : Arith := ⟨.nonDiff true false, .real⟩
def lira : Arith := ⟨.nonDiff true false, .both⟩

def nia : Arith := ⟨.nonDiff false false, .int⟩
def nra : Arith := ⟨.nonDiff false false, .real⟩
def nira : Arith := ⟨.nonDiff false false, .both⟩

def liat : Arith := ⟨.nonDiff true true, .int⟩
def lrat : Arith := ⟨.nonDiff true true, .real⟩
def lirat : Arith := ⟨.nonDiff true true, .both⟩

def niat : Arith := ⟨.nonDiff false true, .int⟩
def nrat : Arith := ⟨.nonDiff false true, .real⟩
def nirat : Arith := ⟨.nonDiff false true, .both⟩

def idl : Arith := ⟨.diff, .int⟩
def rdl : Arith := ⟨.diff, .real⟩
def irdl : Arith := ⟨.diff, .both⟩

/-- info:
LIA,  LRA,  LIRA,  NIA,  NRA,  NIRA
LIAT, LRAT, LIRAT, NIAT, NRAT, NIRAT
IDL, RDL, IRDL
-/
#guard_msgs in #eval do
  println! "\
    {Arith.lia.toSmtLib},  {Arith.lra.toSmtLib},  {Arith.lira.toSmtLib},  \
    {Arith.nia.toSmtLib},  {Arith.nra.toSmtLib},  {Arith.nira.toSmtLib}\
  "
  println! "\
    {Arith.liat.toSmtLib}, {Arith.lrat.toSmtLib}, {Arith.lirat.toSmtLib}, \
    {Arith.niat.toSmtLib}, {Arith.nrat.toSmtLib}, {Arith.nirat.toSmtLib}\
  "
  println! "{Arith.idl.toSmtLib}, {Arith.rdl.toSmtLib}, {Arith.irdl.toSmtLib}"
end Arith

end Logic



/--

Based on

- <https://github.com/cvc5/cvc5/blob/7ee7051df025e6db566fc67086a7aa4e1023c8f2/src/theory/logic_info.cpp#L270-L367>
-/
structure Logic : Type where private mkRaw ::
  private all? : Bool := false
  private ho? : Bool := false
  private qf? : Bool := false
  private sep? : Bool := false
  private array? : Bool := false
  private uf? : Bool := false
  private card? : Bool := false
  private bitvec? : Bool := false
  private ff? : Bool := false
  private float? : Bool := false
  private datatype? : Bool := false
  private string? : Bool := false
  private arith? : Option Logic.Arith := none

namespace Logic

@[simp]
private def oneTrailing? (ignoreArray : Bool) : Logic → Bool
| { all? := _, ho? := _, qf? := _, sep? := _,
    array?, uf?, card?, bitvec?, ff?, float?, datatype?, string?, arith?
} =>
  (¬ ignoreArray ∧ array?) ∨ uf? ∨ card? ∨ bitvec? ∨ ff? ∨ float? ∨ datatype? ∨ string?
  ∨ arith?.isSome



variable (self : Logic)



private def oneAfterArray? : Bool :=
  self.oneTrailing? true

def toSmtLib : String :=
  if let
      { all? := false, ho?, qf?, sep?,
        array?, uf?, card?, bitvec?, ff?, float?, datatype?, string?, arith?
      }
      := self
  then Id.run do
    let mut s := ""
    if ho? then s := s ++ "HO_"
    if qf? then s := s ++ "QF_"
    if sep? then s := s ++ "SEP_"
    if array? then
      s := s ++ if self.oneAfterArray? then "A" else "AX"
    if uf? then s := s ++ "UF"
    if card? then s := s ++ "C"
    if bitvec? then s := s ++ "BV"
    if ff? then s := s ++ "FF"
    if float? then s := s ++ "FP"
    if datatype? then s := s ++ "DT"
    if string? then s := s ++ "S"
    if let some arith := arith? then
      s := s ++ arith.toSmtLib
    s
  else "ALL"



@[simp]
def isValid : Bool :=
  self.all? ∨ self.oneTrailing? false

@[simp]
def valid : Prop :=
  self.isValid

instance : Decidable self.valid :=
  if h : self.isValid then .isTrue h else .isFalse h



structure Builder extends Logic
where private mk ::

namespace Builder
variable (self : Builder)

def ho : Builder := {self with all? := false, ho? := true}
def qf : Builder := {self with all? := false, qf? := true}
def sep : Builder := {self with all? := false, sep? := true}
def array : Builder := {self with all? := false, array? := true}
def uf : Builder := {self with all? := false, uf? := true}

def card : Logic := {self with all? := false, card? := true}
theorem card_valid {b : Builder} : b.card.valid := by
  simp [Builder.card]

def bitvec : Logic := {self with all? := false, bitvec? := true}
theorem bitvec_valid {b : Builder} : b.bitvec.valid := by
  simp [Builder.bitvec]

def ff : Logic := {self with all? := false, ff? := true}
theorem ff_valid {b : Builder} : b.ff.valid := by
  simp [Builder.ff]

def float : Logic := {self with all? := false, float? := true}
theorem float_valid {b : Builder} : b.float.valid := by
  simp [Builder.float]

def datatype : Logic := {self with all? := false, datatype? := true}
theorem datatype_valid {b : Builder} : b.datatype.valid := by
  simp [Builder.datatype]

def string : Logic := {self with all? := false, string? := true}
theorem string_valid {b : Builder} : b.string.valid := by
  simp [Builder.string]

def arith (arith : Arith) : Logic := {self with all? := false, arith? := arith}
theorem arith_valid {b : Builder} {a : Arith} : (b.arith a).valid := by
  simp [Builder.arith]

end Builder




def all : Logic where
  all? := true
theorem all_valid : all.valid := by simp [all]

def mk : Builder := ⟨{}⟩

variable (self : Logic)

def ho : Logic := {self with ho? := true}
theorem ho_valid {l : Logic} : l.valid → l.ho.valid := by
  simp [ho]

def qf : Logic := {self with qf? := true}
theorem qf_valid {l : Logic} : l.valid → l.qf.valid := by
  simp [qf]

def sep : Logic := {self with sep? := true}
theorem sep_valid {l : Logic} : l.valid → l.sep.valid := by
  simp [sep]

def array : Logic := {self with array? := true}
theorem array_valid {l : Logic} : l.valid → l.array.valid := by
  simp [array]

def uf : Logic := {self with uf? := true}
theorem uf_valid {l : Logic} : l.valid → l.uf.valid := by
  simp [uf]


def card : Logic := {self with card? := true}
theorem card_valid {l : Logic} : l.card.valid := by
  simp [card]

def bitvec : Logic := {self with bitvec? := true}
theorem bitvec_valid {l : Logic} : l.bitvec.valid := by
  simp [bitvec]

def ff : Logic := {self with ff? := true}
theorem ff_valid {l : Logic} : l.ff.valid := by
  simp [ff]

def float : Logic := {self with float? := true}
theorem float_valid {l : Logic} : l.float.valid := by
  simp [float]

def datatype : Logic := {self with datatype? := true}
theorem datatype_valid {l : Logic} : l.datatype.valid := by
  simp [datatype]

def string : Logic := {self with string? := true}
theorem string_valid {l : Logic} : l.string.valid := by
  simp [string]

def arith (arith : Arith) : Logic := {self with arith? := arith}
theorem arith_valid {l : Logic} {a : Arith} : (l.arith a).valid := by
  simp [arith]



/-! ### Convenient `Logic` constructors for `Arith` -/

def lia := mk |>.arith .lia
def lra := mk |>.arith .lra
def lira := mk |>.arith .lira

def nia := mk |>.arith .nia
def nra := mk |>.arith .nra
def nira := mk |>.arith .nira

def liat := mk |>.arith .liat
def lrat := mk |>.arith .lrat
def lirat := mk |>.arith .lirat

def niat := mk |>.arith .niat
def nrat := mk |>.arith .nrat
def nirat := mk |>.arith .nirat

def idl := mk |>.arith .idl
def rdl := mk |>.arith .rdl
def irdl := mk |>.arith .irdl

/-! ### Ubiquitous logics -/

def qf_lia := lia.qf
def qf_lra := lra.qf
def qf_lira := lira.qf

def qf_nia := nia.qf
def qf_nra := nra.qf
def qf_nira := nira.qf

end Logic



section test
open Test (check!)
open Logic

/-- info: -/
#guard_msgs in #eval do
  check! "LIA" lia.toSmtLib
  check! "LRA" lra.toSmtLib
  check! "LIRA" lira.toSmtLib

  check! "NIA" nia.toSmtLib
  check! "NRA" nra.toSmtLib
  check! "NIRA" nira.toSmtLib

  check! "QF_LIA" qf_lia.toSmtLib
  check! "QF_LRA" qf_lra.toSmtLib
  check! "QF_LIRA" qf_lira.toSmtLib

  check! "QF_NIA" qf_nia.toSmtLib
  check! "QF_NRA" qf_nra.toSmtLib
  check! "QF_NIRA" qf_nira.toSmtLib

  check! "QF_AX" mk.qf.array.toSmtLib

  check! "ALIA" lia.array.toSmtLib
  check! "QF_ALIA" qf_lia.array.toSmtLib

  check! "AUFNIRA" nira.array.uf.toSmtLib
end test
