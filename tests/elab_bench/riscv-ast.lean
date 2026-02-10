/-
Benchmark taken from
https://github.com/opencompl/sail-riscv-lean
file LeanRV64D/Defs.lean
a6a0249ea3b7a218c51d30e91dfed8432d54b252
https://raw.githubusercontent.com/opencompl/sail-riscv-lean/refs/heads/main/LeanRV64D/Defs.lean

The original file was generated from the Sail RISC-V model:

This Sail RISC-V architecture model, comprising all files and
directories except for the snapshots of the Lem and Sail libraries
in the prover_snapshots directory (which include copies of their
licences), is subject to the BSD two-clause licence.

-/

import Std

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

-- manually inlined from imported files


inductive Primitive where
  | bool
  | bit
  | int
  | nat
  | string
  | fin (n : Nat)
  | bitvector (n : Nat)

abbrev Primitive.reflect : Primitive → Type
  | bool => Bool
  | bit => BitVec 1
  | int => Int
  | nat => Nat
  | string => String
  | fin n => Fin (n + 1)
  | bitvector n => BitVec n

structure ChoiceSource where
  (α : Type)
  (nextState : Primitive → α → α)
  (choose : ∀ p : Primitive, α → p.reflect)


def trivialChoiceSource : ChoiceSource where
  α := Unit
  nextState _ _ := ()
  choose p _ :=
    match p with
    | .bool => false
    | .bit => 0
    | .int => 0
    | .nat => 0
    | .string => ""
    | .fin _ => 0
    | .bitvector _ => 0

inductive Access_variety where
  | AV_plain
  | AV_exclusive
  | AV_atomic_rmw
  deriving Inhabited, DecidableEq, Repr

inductive Result (α : Type) (β : Type) where
  | Ok (_ : α)
  | Err (_ : β)
  deriving Repr
export Result(Ok Err)

/- The Units are placeholders for a future implementation of the state monad some Sail functions use. -/
inductive Error (ue: Type) where
  | Exit
  | Unreachable
  | OutOfMemoryRange (n : Nat)
  | Assertion (s : String)
  | User (e : ue)
open Error

section Regs

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

structure SequentialState (RegisterType : Register → Type) (c : ChoiceSource) where
  regs : Std.ExtDHashMap Register RegisterType
  choiceState : c.α
  mem : Std.ExtHashMap Nat (BitVec 8)
  tags : Unit
  cycleCount : Nat -- Part of the concurrency interface. See `{get_}cycle_count`
  sailOutput : Array String -- TODO: be able to use the IO monad to run

inductive RegisterRef (RegisterType : Register → Type) : Type → Type where
  | Reg (r : Register) : RegisterRef _ (RegisterType r)
export RegisterRef (Reg)

abbrev PreSailM (RegisterType : Register → Type) (c : ChoiceSource) (ue: Type) :=
  EStateM (Error ue) (SequentialState RegisterType c)

end Regs


class Arch where
  va_size : Nat
  pa : Type
  arch_ak : Type
  translation : Type
  trans_start : Type
  trans_end : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlb_op : Type
  fault : Type
  sys_reg_id : Type

-- Now the main file

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr

abbrev bits k_n := (BitVec k_n)

inductive regidx where
  | Regidx (_ : (BitVec (if ( false  : Bool) then 4 else 5)))
  deriving Inhabited, BEq, Repr

abbrev base_E_enabled : Bool := false

abbrev regidx_bit_width : Int := (if ( base_E_enabled  : Bool) then 4 else 5)

inductive vregidx where
  | Vregidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr

abbrev xlenbits := (BitVec 64)

inductive virtaddr where
  | Virtaddr (_ : xlenbits)
  deriving Inhabited, BEq, Repr

abbrev nat1 := Int

abbrev max_mem_access : Int := 4096

abbrev mem_access_width := Nat

inductive exception where
  | Error_not_implemented (_ : String)
  | Error_internal_error (_ : Unit)
  deriving Inhabited, BEq, Repr

abbrev xlen : Int := 64

abbrev log2_xlen : Int := (if ( xlen = 32  : Bool) then 5 else 6)

abbrev xlen_bytes : Int := (if ( xlen = 32  : Bool) then 4 else 8)

abbrev physaddrbits_len : Int := (if ( xlen = 32  : Bool) then 34 else 64)

abbrev asidlen : Int := (if ( xlen = 32  : Bool) then 9 else 16)

abbrev asidbits := (BitVec (if ( 64 = 32  : Bool) then 9 else 16))

abbrev ext_d_supported : Bool := true

abbrev flen_bytes : Int := (if ( ext_d_supported  : Bool) then 8 else 4)

abbrev flen : Int := (if ( true  : Bool) then 8 else 4 * 8)

abbrev flenbits := (BitVec (if ( true  : Bool) then 8 else 4 * 8))

abbrev vlen_exp : Int := 8

abbrev elen_exp : Int := 6

abbrev vlen : Int := (2 ^ 8)

abbrev elen : Int := (2 ^ 6)

abbrev physaddrbits := (BitVec (if ( 64 = 32  : Bool) then 34 else 64))

inductive physaddr where
  | Physaddr (_ : physaddrbits)
  deriving Inhabited, BEq, Repr

abbrev mem_meta := Unit

inductive write_kind where | Write_plain | Write_RISCV_release | Write_RISCV_strong_release | Write_RISCV_conditional | Write_RISCV_conditional_release | Write_RISCV_conditional_strong_release
  deriving BEq, Inhabited, Repr

inductive read_kind where | Read_plain | Read_ifetch | Read_RISCV_acquire | Read_RISCV_strong_acquire | Read_RISCV_reserved | Read_RISCV_reserved_acquire | Read_RISCV_reserved_strong_acquire
  deriving BEq, Inhabited, Repr

inductive barrier_kind where | Barrier_RISCV_rw_rw | Barrier_RISCV_r_rw | Barrier_RISCV_r_r | Barrier_RISCV_rw_w | Barrier_RISCV_w_w | Barrier_RISCV_w_rw | Barrier_RISCV_rw_r | Barrier_RISCV_r_w | Barrier_RISCV_w_r | Barrier_RISCV_tso | Barrier_RISCV_i
  deriving BEq, Inhabited, Repr

structure RISCV_strong_access where
  variety : Access_variety
  deriving BEq, Inhabited, Repr

abbrev RVFI_DII_Instruction_Packet := (BitVec 64)

abbrev RVFI_DII_Execution_Packet_InstMetaData := (BitVec 192)

abbrev RVFI_DII_Execution_Packet_PC := (BitVec 128)

abbrev RVFI_DII_Execution_Packet_Ext_Integer := (BitVec 320)

abbrev RVFI_DII_Execution_Packet_Ext_MemAccess := (BitVec 704)

abbrev RVFI_DII_Execution_Packet_V1 := (BitVec 704)

abbrev RVFI_DII_Execution_PacketV2 := (BitVec 512)

inductive extension where | Ext_M | Ext_A | Ext_F | Ext_D | Ext_B | Ext_V | Ext_S | Ext_U | Ext_H | Ext_Zicbom | Ext_Zicbop | Ext_Zicboz | Ext_Zicntr | Ext_Zicond | Ext_Zicsr | Ext_Zifencei | Ext_Zihintntl | Ext_Zihintpause | Ext_Zihpm | Ext_Zimop | Ext_Zmmul | Ext_Zaamo | Ext_Zabha | Ext_Zacas | Ext_Zalrsc | Ext_Zawrs | Ext_Zfa | Ext_Zfbfmin | Ext_Zfh | Ext_Zfhmin | Ext_Zfinx | Ext_Zdinx | Ext_Zca | Ext_Zcb | Ext_Zcd | Ext_Zcf | Ext_Zcmop | Ext_C | Ext_Zba | Ext_Zbb | Ext_Zbc | Ext_Zbkb | Ext_Zbkc | Ext_Zbkx | Ext_Zbs | Ext_Zknd | Ext_Zkne | Ext_Zknh | Ext_Zkr | Ext_Zksed | Ext_Zksh | Ext_Zkt | Ext_Zhinx | Ext_Zhinxmin | Ext_Zvbb | Ext_Zvbc | Ext_Zvkb | Ext_Zvkg | Ext_Zvkned | Ext_Zvknha | Ext_Zvknhb | Ext_Zvksed | Ext_Zvksh | Ext_Zvkt | Ext_Zvkn | Ext_Zvknc | Ext_Zvkng | Ext_Zvks | Ext_Zvksc | Ext_Zvksg | Ext_Sscofpmf | Ext_Sstc | Ext_Svbare | Ext_Sv32 | Ext_Sv39 | Ext_Sv48 | Ext_Sv57 | Ext_Svinval | Ext_Svnapot | Ext_Svpbmt | Ext_Svrsw60t59b | Ext_Smcntrpmf
  deriving BEq, Inhabited, Repr

abbrev exc_code := (BitVec 8)

abbrev ext_ptw := Unit

abbrev ext_ptw_fail := Unit

abbrev ext_ptw_error := Unit

abbrev ext_exc_type := Unit

abbrev half := (BitVec 16)

abbrev word := (BitVec 32)

abbrev instbits := (BitVec 32)

abbrev pagesize_bits : Int := 12

inductive cregidx where
  | Cregidx (_ : (BitVec 3))
  deriving Inhabited, BEq, Repr

abbrev csreg := (BitVec 12)

inductive regno where
  | Regno (_ : Nat)
  deriving Inhabited, BEq, Repr

inductive Architecture where | RV32 | RV64 | RV128
  deriving BEq, Inhabited, Repr

abbrev arch_xlen := (BitVec 2)

abbrev nom_priv_bits := (BitVec 2)

abbrev virt_mode_bit := (BitVec 1)

inductive Privilege where | User | VirtualUser | Supervisor | VirtualSupervisor | Machine
  deriving BEq, Inhabited, Repr

abbrev Misa := (BitVec 64)

abbrev Mstatus := (BitVec 64)

/-- Type quantifiers: k_a : Type -/
inductive AccessType (k_a : Type) where
  | Read (_ : k_a)
  | Write (_ : k_a)
  | ReadWrite (_ : (k_a × k_a))
  | InstructionFetch (_ : Unit)
  deriving Inhabited, BEq, Repr

inductive ExceptionType where
  | E_Fetch_Addr_Align (_ : Unit)
  | E_Fetch_Access_Fault (_ : Unit)
  | E_Illegal_Instr (_ : Unit)
  | E_Breakpoint (_ : Unit)
  | E_Load_Addr_Align (_ : Unit)
  | E_Load_Access_Fault (_ : Unit)
  | E_SAMO_Addr_Align (_ : Unit)
  | E_SAMO_Access_Fault (_ : Unit)
  | E_U_EnvCall (_ : Unit)
  | E_S_EnvCall (_ : Unit)
  | E_Reserved_10 (_ : Unit)
  | E_M_EnvCall (_ : Unit)
  | E_Fetch_Page_Fault (_ : Unit)
  | E_Load_Page_Fault (_ : Unit)
  | E_Reserved_14 (_ : Unit)
  | E_SAMO_Page_Fault (_ : Unit)
  | E_Extension (_ : ext_exc_type)
  deriving Inhabited, BEq, Repr

inductive amoop where | AMOSWAP | AMOADD | AMOXOR | AMOAND | AMOOR | AMOMIN | AMOMAX | AMOMINU | AMOMAXU | AMOCAS
  deriving BEq, Inhabited, Repr

inductive bop where | BEQ | BNE | BLT | BGE | BLTU | BGEU
  deriving BEq, Inhabited, Repr

inductive cbop_zicbom where | CBO_CLEAN | CBO_FLUSH | CBO_INVAL
  deriving BEq, Inhabited, Repr

inductive fregidx where
  | Fregidx (_ : (BitVec 5))
  deriving Inhabited, BEq, Repr

inductive cfregidx where
  | Cfregidx (_ : (BitVec 3))
  deriving Inhabited, BEq, Repr

inductive csrop where | CSRRW | CSRRS | CSRRC
  deriving BEq, Inhabited, Repr

inductive f_bin_f_op_D where | FSGNJ_D | FSGNJN_D | FSGNJX_D | FMIN_D | FMAX_D
  deriving BEq, Inhabited, Repr

inductive f_bin_f_op_H where | FSGNJ_H | FSGNJN_H | FSGNJX_H | FMIN_H | FMAX_H
  deriving BEq, Inhabited, Repr

inductive f_bin_rm_op_D where | FADD_D | FSUB_D | FMUL_D | FDIV_D
  deriving BEq, Inhabited, Repr

inductive f_bin_rm_op_H where | FADD_H | FSUB_H | FMUL_H | FDIV_H
  deriving BEq, Inhabited, Repr

inductive f_bin_rm_op_S where | FADD_S | FSUB_S | FMUL_S | FDIV_S
  deriving BEq, Inhabited, Repr

inductive f_bin_op_f_S where | FSGNJ_S | FSGNJN_S | FSGNJX_S | FMIN_S | FMAX_S
  deriving BEq, Inhabited, Repr

inductive f_bin_op_x_S where | FEQ_S | FLT_S | FLE_S
  deriving BEq, Inhabited, Repr

inductive f_bin_x_op_D where | FEQ_D | FLT_D | FLE_D
  deriving BEq, Inhabited, Repr

inductive f_bin_x_op_H where | FEQ_H | FLT_H | FLE_H
  deriving BEq, Inhabited, Repr

inductive f_madd_op_D where | FMADD_D | FMSUB_D | FNMSUB_D | FNMADD_D
  deriving BEq, Inhabited, Repr

inductive f_madd_op_H where | FMADD_H | FMSUB_H | FNMSUB_H | FNMADD_H
  deriving BEq, Inhabited, Repr

inductive f_madd_op_S where | FMADD_S | FMSUB_S | FNMSUB_S | FNMADD_S
  deriving BEq, Inhabited, Repr

inductive f_un_f_op_D where | FMV_D_X
  deriving BEq, Inhabited, Repr

inductive f_un_f_op_H where | FMV_H_X
  deriving BEq, Inhabited, Repr

inductive f_un_rm_ff_op_D where | FSQRT_D | FCVT_S_D | FCVT_D_S
  deriving BEq, Inhabited, Repr

inductive f_un_rm_ff_op_H where | FSQRT_H | FCVT_H_S | FCVT_H_D | FCVT_S_H | FCVT_D_H
  deriving BEq, Inhabited, Repr

inductive f_un_rm_fx_op_D where | FCVT_W_D | FCVT_WU_D | FCVT_L_D | FCVT_LU_D
  deriving BEq, Inhabited, Repr

inductive f_un_rm_fx_op_H where | FCVT_W_H | FCVT_WU_H | FCVT_L_H | FCVT_LU_H
  deriving BEq, Inhabited, Repr

inductive f_un_rm_fx_op_S where | FCVT_W_S | FCVT_WU_S | FCVT_L_S | FCVT_LU_S
  deriving BEq, Inhabited, Repr

inductive f_un_rm_xf_op_D where | FCVT_D_W | FCVT_D_WU | FCVT_D_L | FCVT_D_LU
  deriving BEq, Inhabited, Repr

inductive f_un_rm_xf_op_H where | FCVT_H_W | FCVT_H_WU | FCVT_H_L | FCVT_H_LU
  deriving BEq, Inhabited, Repr

inductive f_un_rm_xf_op_S where | FCVT_S_W | FCVT_S_WU | FCVT_S_L | FCVT_S_LU
  deriving BEq, Inhabited, Repr

inductive f_un_op_f_S where | FMV_W_X
  deriving BEq, Inhabited, Repr

inductive f_un_op_x_S where | FCLASS_S | FMV_X_W
  deriving BEq, Inhabited, Repr

inductive f_un_x_op_D where | FCLASS_D | FMV_X_D
  deriving BEq, Inhabited, Repr

inductive f_un_x_op_H where | FCLASS_H | FMV_X_H
  deriving BEq, Inhabited, Repr

inductive rounding_mode where | RM_RNE | RM_RTZ | RM_RDN | RM_RUP | RM_RMM | RM_DYN
  deriving BEq, Inhabited, Repr

inductive fvfmafunct6 where | VF_VMADD | VF_VNMADD | VF_VMSUB | VF_VNMSUB | VF_VMACC | VF_VNMACC | VF_VMSAC | VF_VNMSAC
  deriving BEq, Inhabited, Repr

inductive fvfmfunct6 where | VFM_VMFEQ | VFM_VMFLE | VFM_VMFLT | VFM_VMFNE | VFM_VMFGT | VFM_VMFGE
  deriving BEq, Inhabited, Repr

inductive fvffunct6 where | VF_VADD | VF_VSUB | VF_VMIN | VF_VMAX | VF_VSGNJ | VF_VSGNJN | VF_VSGNJX | VF_VDIV | VF_VRDIV | VF_VMUL | VF_VRSUB | VF_VSLIDE1UP | VF_VSLIDE1DOWN
  deriving BEq, Inhabited, Repr

inductive fvvmafunct6 where | FVV_VMADD | FVV_VNMADD | FVV_VMSUB | FVV_VNMSUB | FVV_VMACC | FVV_VNMACC | FVV_VMSAC | FVV_VNMSAC
  deriving BEq, Inhabited, Repr

inductive fvvmfunct6 where | FVVM_VMFEQ | FVVM_VMFLE | FVVM_VMFLT | FVVM_VMFNE
  deriving BEq, Inhabited, Repr

inductive fvvfunct6 where | FVV_VADD | FVV_VSUB | FVV_VMIN | FVV_VMAX | FVV_VSGNJ | FVV_VSGNJN | FVV_VSGNJX | FVV_VDIV | FVV_VMUL
  deriving BEq, Inhabited, Repr

inductive fwffunct6 where | FWF_VADD | FWF_VSUB
  deriving BEq, Inhabited, Repr

inductive fwvfmafunct6 where | FWVF_VMACC | FWVF_VNMACC | FWVF_VMSAC | FWVF_VNMSAC
  deriving BEq, Inhabited, Repr

inductive fwvffunct6 where | FWVF_VADD | FWVF_VSUB | FWVF_VMUL
  deriving BEq, Inhabited, Repr

inductive fwvfunct6 where | FWV_VADD | FWV_VSUB
  deriving BEq, Inhabited, Repr

inductive fwvvmafunct6 where | FWVV_VMACC | FWVV_VNMACC | FWVV_VMSAC | FWVV_VNMSAC
  deriving BEq, Inhabited, Repr

inductive fwvvfunct6 where | FWVV_VADD | FWVV_VSUB | FWVV_VMUL
  deriving BEq, Inhabited, Repr

inductive iop where | ADDI | SLTI | SLTIU | XORI | ORI | ANDI
  deriving BEq, Inhabited, Repr

inductive mmfunct6 where | MM_VMAND | MM_VMNAND | MM_VMANDN | MM_VMXOR | MM_VMOR | MM_VMNOR | MM_VMORN | MM_VMXNOR
  deriving BEq, Inhabited, Repr

structure mul_op where
  high : Bool
  signed_rs1 : Bool
  signed_rs2 : Bool
  deriving BEq, Inhabited, Repr

inductive mvvmafunct6 where | MVV_VMACC | MVV_VNMSAC | MVV_VMADD | MVV_VNMSUB
  deriving BEq, Inhabited, Repr

inductive mvvfunct6 where | MVV_VAADDU | MVV_VAADD | MVV_VASUBU | MVV_VASUB | MVV_VMUL | MVV_VMULH | MVV_VMULHU | MVV_VMULHSU | MVV_VDIVU | MVV_VDIV | MVV_VREMU | MVV_VREM
  deriving BEq, Inhabited, Repr

inductive mvxmafunct6 where | MVX_VMACC | MVX_VNMSAC | MVX_VMADD | MVX_VNMSUB
  deriving BEq, Inhabited, Repr

inductive mvxfunct6 where | MVX_VAADDU | MVX_VAADD | MVX_VASUBU | MVX_VASUB | MVX_VSLIDE1UP | MVX_VSLIDE1DOWN | MVX_VMUL | MVX_VMULH | MVX_VMULHU | MVX_VMULHSU | MVX_VDIVU | MVX_VDIV | MVX_VREMU | MVX_VREM
  deriving BEq, Inhabited, Repr

inductive nisfunct6 where | NIS_VNSRL | NIS_VNSRA
  deriving BEq, Inhabited, Repr

inductive nifunct6 where | NI_VNCLIPU | NI_VNCLIP
  deriving BEq, Inhabited, Repr

inductive ntl_type where | NTL_P1 | NTL_PALL | NTL_S1 | NTL_ALL
  deriving BEq, Inhabited, Repr

inductive nvsfunct6 where | NVS_VNSRL | NVS_VNSRA
  deriving BEq, Inhabited, Repr

inductive nvfunct6 where | NV_VNCLIPU | NV_VNCLIP
  deriving BEq, Inhabited, Repr

inductive nxsfunct6 where | NXS_VNSRL | NXS_VNSRA
  deriving BEq, Inhabited, Repr

inductive nxfunct6 where | NX_VNCLIPU | NX_VNCLIP
  deriving BEq, Inhabited, Repr

inductive cbop_zicbop where | PREFETCH_I | PREFETCH_R | PREFETCH_W
  deriving BEq, Inhabited, Repr

inductive rfvvfunct6 where | FVV_VFREDOSUM | FVV_VFREDUSUM | FVV_VFREDMAX | FVV_VFREDMIN | FVV_VFWREDOSUM | FVV_VFWREDUSUM
  deriving BEq, Inhabited, Repr

inductive rivvfunct6 where | IVV_VWREDSUMU | IVV_VWREDSUM
  deriving BEq, Inhabited, Repr

inductive rmvvfunct6 where | MVV_VREDSUM | MVV_VREDAND | MVV_VREDOR | MVV_VREDXOR | MVV_VREDMINU | MVV_VREDMIN | MVV_VREDMAXU | MVV_VREDMAX
  deriving BEq, Inhabited, Repr

inductive rop where | ADD | SUB | SLL | SLT | SLTU | XOR | SRL | SRA | OR | AND
  deriving BEq, Inhabited, Repr

inductive ropw where | ADDW | SUBW | SLLW | SRLW | SRAW
  deriving BEq, Inhabited, Repr

inductive sop where | SLLI | SRLI | SRAI
  deriving BEq, Inhabited, Repr

inductive sopw where | SLLIW | SRLIW | SRAIW
  deriving BEq, Inhabited, Repr

inductive uop where | LUI | AUIPC
  deriving BEq, Inhabited, Repr

inductive zvk_vaesdf_funct6 where | ZVK_VAESDF_VV | ZVK_VAESDF_VS
  deriving BEq, Inhabited, Repr

inductive zvk_vaesdm_funct6 where | ZVK_VAESDM_VV | ZVK_VAESDM_VS
  deriving BEq, Inhabited, Repr

inductive zvk_vaesef_funct6 where | ZVK_VAESEF_VV | ZVK_VAESEF_VS
  deriving BEq, Inhabited, Repr

inductive zvk_vaesem_funct6 where | ZVK_VAESEM_VV | ZVK_VAESEM_VS
  deriving BEq, Inhabited, Repr

inductive vextfunct6 where | VEXT2_ZVF2 | VEXT2_SVF2 | VEXT4_ZVF4 | VEXT4_SVF4 | VEXT8_ZVF8 | VEXT8_SVF8
  deriving BEq, Inhabited, Repr

inductive vfnunary0 where | FNV_CVT_XU_F | FNV_CVT_X_F | FNV_CVT_F_XU | FNV_CVT_F_X | FNV_CVT_F_F | FNV_CVT_ROD_F_F | FNV_CVT_RTZ_XU_F | FNV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr

inductive vfunary0 where | FV_CVT_XU_F | FV_CVT_X_F | FV_CVT_F_XU | FV_CVT_F_X | FV_CVT_RTZ_XU_F | FV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr

inductive vfunary1 where | FVV_VSQRT | FVV_VRSQRT7 | FVV_VREC7 | FVV_VCLASS
  deriving BEq, Inhabited, Repr

inductive vfwunary0 where | FWV_CVT_XU_F | FWV_CVT_X_F | FWV_CVT_F_XU | FWV_CVT_F_X | FWV_CVT_F_F | FWV_CVT_RTZ_XU_F | FWV_CVT_RTZ_X_F
  deriving BEq, Inhabited, Repr

inductive vicmpfunct6 where | VICMP_VMSEQ | VICMP_VMSNE | VICMP_VMSLEU | VICMP_VMSLE | VICMP_VMSGTU | VICMP_VMSGT
  deriving BEq, Inhabited, Repr

inductive vimcfunct6 where | VIMC_VMADC
  deriving BEq, Inhabited, Repr

inductive vimsfunct6 where | VIMS_VADC
  deriving BEq, Inhabited, Repr

inductive vimfunct6 where | VIM_VMADC
  deriving BEq, Inhabited, Repr

inductive visgfunct6 where | VI_VSLIDEUP | VI_VSLIDEDOWN | VI_VRGATHER
  deriving BEq, Inhabited, Repr

inductive vifunct6 where | VI_VADD | VI_VRSUB | VI_VAND | VI_VOR | VI_VXOR | VI_VSADDU | VI_VSADD | VI_VSLL | VI_VSRL | VI_VSRA | VI_VSSRL | VI_VSSRA
  deriving BEq, Inhabited, Repr

inductive vlewidth where | VLE8 | VLE16 | VLE32 | VLE64
  deriving BEq, Inhabited, Repr

inductive vmlsop where | VLM | VSM
  deriving BEq, Inhabited, Repr

inductive zvk_vsha2_funct6 where | ZVK_VSHA2CH_VV | ZVK_VSHA2CL_VV
  deriving BEq, Inhabited, Repr

inductive zvk_vsm4r_funct6 where | ZVK_VSM4R_VV | ZVK_VSM4R_VS
  deriving BEq, Inhabited, Repr

inductive vvcmpfunct6 where | VVCMP_VMSEQ | VVCMP_VMSNE | VVCMP_VMSLTU | VVCMP_VMSLT | VVCMP_VMSLEU | VVCMP_VMSLE
  deriving BEq, Inhabited, Repr

inductive vvmcfunct6 where | VVMC_VMADC | VVMC_VMSBC
  deriving BEq, Inhabited, Repr

inductive vvmsfunct6 where | VVMS_VADC | VVMS_VSBC
  deriving BEq, Inhabited, Repr

inductive vvmfunct6 where | VVM_VMADC | VVM_VMSBC
  deriving BEq, Inhabited, Repr

inductive vvfunct6 where | VV_VADD | VV_VSUB | VV_VMINU | VV_VMIN | VV_VMAXU | VV_VMAX | VV_VAND | VV_VOR | VV_VXOR | VV_VRGATHER | VV_VRGATHEREI16 | VV_VSADDU | VV_VSADD | VV_VSSUBU | VV_VSSUB | VV_VSLL | VV_VSMUL | VV_VSRL | VV_VSRA | VV_VSSRL | VV_VSSRA
  deriving BEq, Inhabited, Repr

inductive vxcmpfunct6 where | VXCMP_VMSEQ | VXCMP_VMSNE | VXCMP_VMSLTU | VXCMP_VMSLT | VXCMP_VMSLEU | VXCMP_VMSLE | VXCMP_VMSGTU | VXCMP_VMSGT
  deriving BEq, Inhabited, Repr

inductive vxmcfunct6 where | VXMC_VMADC | VXMC_VMSBC
  deriving BEq, Inhabited, Repr

inductive vxmsfunct6 where | VXMS_VADC | VXMS_VSBC
  deriving BEq, Inhabited, Repr

inductive vxmfunct6 where | VXM_VMADC | VXM_VMSBC
  deriving BEq, Inhabited, Repr

inductive vxsgfunct6 where | VX_VSLIDEUP | VX_VSLIDEDOWN | VX_VRGATHER
  deriving BEq, Inhabited, Repr

inductive vxfunct6 where | VX_VADD | VX_VSUB | VX_VRSUB | VX_VMINU | VX_VMIN | VX_VMAXU | VX_VMAX | VX_VAND | VX_VOR | VX_VXOR | VX_VSADDU | VX_VSADD | VX_VSSUBU | VX_VSSUB | VX_VSLL | VX_VSMUL | VX_VSRL | VX_VSRA | VX_VSSRL | VX_VSSRA
  deriving BEq, Inhabited, Repr

inductive wmvvfunct6 where | WMVV_VWMACCU | WMVV_VWMACC | WMVV_VWMACCSU
  deriving BEq, Inhabited, Repr

inductive wmvxfunct6 where | WMVX_VWMACCU | WMVX_VWMACC | WMVX_VWMACCUS | WMVX_VWMACCSU
  deriving BEq, Inhabited, Repr

inductive wvfunct6 where | WV_VADD | WV_VSUB | WV_VADDU | WV_VSUBU
  deriving BEq, Inhabited, Repr

inductive wvvfunct6 where | WVV_VADD | WVV_VSUB | WVV_VADDU | WVV_VSUBU | WVV_VWMUL | WVV_VWMULU | WVV_VWMULSU
  deriving BEq, Inhabited, Repr

inductive wvxfunct6 where | WVX_VADD | WVX_VSUB | WVX_VADDU | WVX_VSUBU | WVX_VWMUL | WVX_VWMULU | WVX_VWMULSU
  deriving BEq, Inhabited, Repr

inductive wxfunct6 where | WX_VADD | WX_VSUB | WX_VADDU | WX_VSUBU
  deriving BEq, Inhabited, Repr

inductive extop_zbb where | SEXTB | SEXTH | ZEXTH
  deriving BEq, Inhabited, Repr

inductive brop_zbb where | ANDN | ORN | XNOR | MAX | MAXU | MIN | MINU | ROL | ROR
  deriving BEq, Inhabited, Repr

inductive bropw_zbb where | ROLW | RORW
  deriving BEq, Inhabited, Repr

inductive brop_zbkb where | PACK | PACKH
  deriving BEq, Inhabited, Repr

inductive biop_zbs where | BCLRI | BEXTI | BINVI | BSETI
  deriving BEq, Inhabited, Repr

inductive brop_zbs where | BCLR | BEXT | BINV | BSET
  deriving BEq, Inhabited, Repr

inductive zicondop where | CZERO_EQZ | CZERO_NEZ
  deriving BEq, Inhabited, Repr

inductive f_un_rm_ff_op_S where | FSQRT_S
  deriving BEq, Inhabited, Repr



abbrev nfields := Int



abbrev nfields_pow2 := Int

abbrev shamt_zba := (BitVec 2)

abbrev word_width := Int

abbrev word_width_wide := Int

inductive wrsop where | WRS_STO | WRS_NTO
  deriving BEq, Inhabited, Repr

inductive instruction where
  | ILLEGAL (_ : word)
  | C_ILLEGAL (_ : half)
  | ZICBOP (_ : (cbop_zicbop × regidx × (BitVec 12)))
  | NTL (_ : ntl_type)
  | C_NTL (_ : ntl_type)
  | PAUSE (_ : Unit)
  | UTYPE (_ : ((BitVec 20) × regidx × uop))
  | JAL (_ : ((BitVec 21) × regidx))
  | JALR (_ : ((BitVec 12) × regidx × regidx))
  | BTYPE (_ : ((BitVec 13) × regidx × regidx × bop))
  | ITYPE (_ : ((BitVec 12) × regidx × regidx × iop))
  | SHIFTIOP (_ : ((BitVec 6) × regidx × regidx × sop))
  | RTYPE (_ : (regidx × regidx × regidx × rop))
  | LOAD (_ : ((BitVec 12) × regidx × regidx × Bool × word_width))
  | STORE (_ : ((BitVec 12) × regidx × regidx × word_width))
  | ADDIW (_ : ((BitVec 12) × regidx × regidx))
  | RTYPEW (_ : (regidx × regidx × regidx × ropw))
  | SHIFTIWOP (_ : ((BitVec 5) × regidx × regidx × sopw))
  | FENCE (_ : ((BitVec 4) × (BitVec 4)))
  | FENCE_TSO (_ : Unit)
  | ECALL (_ : Unit)
  | MRET (_ : Unit)
  | SRET (_ : Unit)
  | EBREAK (_ : Unit)
  | WFI (_ : Unit)
  | SFENCE_VMA (_ : (regidx × regidx))
  | FENCE_RESERVED (_ : ((BitVec 4) × (BitVec 4) × (BitVec 4) × regidx × regidx))
  | FENCEI_RESERVED (_ : ((BitVec 12) × regidx × regidx))
  | AMO (_ : (amoop × Bool × Bool × regidx × regidx × word_width_wide × regidx))
  | LOADRES (_ : (Bool × Bool × regidx × word_width × regidx))
  | STORECON (_ : (Bool × Bool × regidx × regidx × word_width × regidx))
  | MUL (_ : (regidx × regidx × regidx × mul_op))
  | DIV (_ : (regidx × regidx × regidx × Bool))
  | REM (_ : (regidx × regidx × regidx × Bool))
  | MULW (_ : (regidx × regidx × regidx))
  | DIVW (_ : (regidx × regidx × regidx × Bool))
  | REMW (_ : (regidx × regidx × regidx × Bool))
  | SLLIUW (_ : ((BitVec 6) × regidx × regidx))
  | ZBA_RTYPEUW (_ : (regidx × regidx × regidx × shamt_zba))
  | ZBA_RTYPE (_ : (regidx × regidx × regidx × shamt_zba))
  | RORIW (_ : ((BitVec 5) × regidx × regidx))
  | RORI (_ : ((BitVec 6) × regidx × regidx))
  | ZBB_RTYPEW (_ : (regidx × regidx × regidx × bropw_zbb))
  | ZBB_RTYPE (_ : (regidx × regidx × regidx × brop_zbb))
  | ZBB_EXTOP (_ : (regidx × regidx × extop_zbb))
  | REV8 (_ : (regidx × regidx))
  | ORCB (_ : (regidx × regidx))
  | CPOP (_ : (regidx × regidx))
  | CPOPW (_ : (regidx × regidx))
  | CLZ (_ : (regidx × regidx))
  | CLZW (_ : (regidx × regidx))
  | CTZ (_ : (regidx × regidx))
  | CTZW (_ : (regidx × regidx))
  | CLMUL (_ : (regidx × regidx × regidx))
  | CLMULH (_ : (regidx × regidx × regidx))
  | CLMULR (_ : (regidx × regidx × regidx))
  | ZBS_IOP (_ : ((BitVec 6) × regidx × regidx × biop_zbs))
  | ZBS_RTYPE (_ : (regidx × regidx × regidx × brop_zbs))
  | C_NOP (_ : (BitVec 6))
  | C_ADDI4SPN (_ : (cregidx × (BitVec 8)))
  | C_LW (_ : ((BitVec 5) × cregidx × cregidx))
  | C_LD (_ : ((BitVec 5) × cregidx × cregidx))
  | C_SW (_ : ((BitVec 5) × cregidx × cregidx))
  | C_SD (_ : ((BitVec 5) × cregidx × cregidx))
  | C_ADDI (_ : ((BitVec 6) × regidx))
  | C_JAL (_ : (BitVec 11))
  | C_ADDIW (_ : ((BitVec 6) × regidx))
  | C_LI (_ : ((BitVec 6) × regidx))
  | C_ADDI16SP (_ : (BitVec 6))
  | C_LUI (_ : ((BitVec 6) × regidx))
  | C_SRLI (_ : ((BitVec 6) × cregidx))
  | C_SRAI (_ : ((BitVec 6) × cregidx))
  | C_ANDI (_ : ((BitVec 6) × cregidx))
  | C_SUB (_ : (cregidx × cregidx))
  | C_XOR (_ : (cregidx × cregidx))
  | C_OR (_ : (cregidx × cregidx))
  | C_AND (_ : (cregidx × cregidx))
  | C_SUBW (_ : (cregidx × cregidx))
  | C_ADDW (_ : (cregidx × cregidx))
  | C_J (_ : (BitVec 11))
  | C_BEQZ (_ : ((BitVec 8) × cregidx))
  | C_BNEZ (_ : ((BitVec 8) × cregidx))
  | C_SLLI (_ : ((BitVec 6) × regidx))
  | C_LWSP (_ : ((BitVec 6) × regidx))
  | C_LDSP (_ : ((BitVec 6) × regidx))
  | C_SWSP (_ : ((BitVec 6) × regidx))
  | C_SDSP (_ : ((BitVec 6) × regidx))
  | C_JR (_ : regidx)
  | C_JALR (_ : regidx)
  | C_MV (_ : (regidx × regidx))
  | C_EBREAK (_ : Unit)
  | C_ADD (_ : (regidx × regidx))
  | C_LBU (_ : ((BitVec 2) × cregidx × cregidx))
  | C_LHU (_ : ((BitVec 2) × cregidx × cregidx))
  | C_LH (_ : ((BitVec 2) × cregidx × cregidx))
  | C_SB (_ : ((BitVec 2) × cregidx × cregidx))
  | C_SH (_ : ((BitVec 2) × cregidx × cregidx))
  | C_ZEXT_B (_ : cregidx)
  | C_SEXT_B (_ : cregidx)
  | C_ZEXT_H (_ : cregidx)
  | C_SEXT_H (_ : cregidx)
  | C_ZEXT_W (_ : cregidx)
  | C_NOT (_ : cregidx)
  | C_MUL (_ : (cregidx × cregidx))
  | LOAD_FP (_ : ((BitVec 12) × regidx × fregidx × word_width))
  | STORE_FP (_ : ((BitVec 12) × fregidx × regidx × word_width))
  | F_MADD_TYPE_S (_ : (fregidx × fregidx × fregidx × rounding_mode × fregidx × f_madd_op_S))
  | F_BIN_RM_TYPE_S (_ : (fregidx × fregidx × rounding_mode × fregidx × f_bin_rm_op_S))
  | F_UN_RM_FF_TYPE_S (_ : (fregidx × rounding_mode × fregidx × f_un_rm_ff_op_S))
  | F_UN_RM_FX_TYPE_S (_ : (fregidx × rounding_mode × regidx × f_un_rm_fx_op_S))
  | F_UN_RM_XF_TYPE_S (_ : (regidx × rounding_mode × fregidx × f_un_rm_xf_op_S))
  | F_BIN_TYPE_F_S (_ : (fregidx × fregidx × fregidx × f_bin_op_f_S))
  | F_BIN_TYPE_X_S (_ : (fregidx × fregidx × regidx × f_bin_op_x_S))
  | F_UN_TYPE_F_S (_ : (regidx × fregidx × f_un_op_f_S))
  | F_UN_TYPE_X_S (_ : (fregidx × regidx × f_un_op_x_S))
  | C_FLWSP (_ : ((BitVec 6) × fregidx))
  | C_FSWSP (_ : ((BitVec 6) × fregidx))
  | C_FLW (_ : ((BitVec 5) × cregidx × cfregidx))
  | C_FSW (_ : ((BitVec 5) × cregidx × cfregidx))
  | F_MADD_TYPE_D (_ : (fregidx × fregidx × fregidx × rounding_mode × fregidx × f_madd_op_D))
  | F_BIN_RM_TYPE_D (_ : (fregidx × fregidx × rounding_mode × fregidx × f_bin_rm_op_D))
  | F_UN_RM_FF_TYPE_D (_ : (fregidx × rounding_mode × fregidx × f_un_rm_ff_op_D))
  | F_UN_RM_XF_TYPE_D (_ : (regidx × rounding_mode × fregidx × f_un_rm_xf_op_D))
  | F_UN_RM_FX_TYPE_D (_ : (fregidx × rounding_mode × regidx × f_un_rm_fx_op_D))
  | F_BIN_F_TYPE_D (_ : (fregidx × fregidx × fregidx × f_bin_f_op_D))
  | F_BIN_X_TYPE_D (_ : (fregidx × fregidx × regidx × f_bin_x_op_D))
  | F_UN_X_TYPE_D (_ : (fregidx × regidx × f_un_x_op_D))
  | F_UN_F_TYPE_D (_ : (regidx × fregidx × f_un_f_op_D))
  | C_FLDSP (_ : ((BitVec 6) × fregidx))
  | C_FSDSP (_ : ((BitVec 6) × fregidx))
  | C_FLD (_ : ((BitVec 5) × cregidx × cfregidx))
  | C_FSD (_ : ((BitVec 5) × cregidx × cfregidx))
  | F_BIN_RM_TYPE_H (_ : (fregidx × fregidx × rounding_mode × fregidx × f_bin_rm_op_H))
  | F_MADD_TYPE_H (_ : (fregidx × fregidx × fregidx × rounding_mode × fregidx × f_madd_op_H))
  | F_BIN_F_TYPE_H (_ : (fregidx × fregidx × fregidx × f_bin_f_op_H))
  | F_BIN_X_TYPE_H (_ : (fregidx × fregidx × regidx × f_bin_x_op_H))
  | F_UN_RM_FF_TYPE_H (_ : (fregidx × rounding_mode × fregidx × f_un_rm_ff_op_H))
  | F_UN_RM_FX_TYPE_H (_ : (fregidx × rounding_mode × regidx × f_un_rm_fx_op_H))
  | F_UN_RM_XF_TYPE_H (_ : (regidx × rounding_mode × fregidx × f_un_rm_xf_op_H))
  | F_UN_F_TYPE_H (_ : (regidx × fregidx × f_un_f_op_H))
  | F_UN_X_TYPE_H (_ : (fregidx × regidx × f_un_x_op_H))
  | FLI_H (_ : ((BitVec 5) × fregidx))
  | FLI_S (_ : ((BitVec 5) × fregidx))
  | FLI_D (_ : ((BitVec 5) × fregidx))
  | FMINM_H (_ : (fregidx × fregidx × fregidx))
  | FMAXM_H (_ : (fregidx × fregidx × fregidx))
  | FMINM_S (_ : (fregidx × fregidx × fregidx))
  | FMAXM_S (_ : (fregidx × fregidx × fregidx))
  | FMINM_D (_ : (fregidx × fregidx × fregidx))
  | FMAXM_D (_ : (fregidx × fregidx × fregidx))
  | FROUND_H (_ : (fregidx × rounding_mode × fregidx))
  | FROUNDNX_H (_ : (fregidx × rounding_mode × fregidx))
  | FROUND_S (_ : (fregidx × rounding_mode × fregidx))
  | FROUNDNX_S (_ : (fregidx × rounding_mode × fregidx))
  | FROUND_D (_ : (fregidx × rounding_mode × fregidx))
  | FROUNDNX_D (_ : (fregidx × rounding_mode × fregidx))
  | FMVH_X_D (_ : (fregidx × regidx))
  | FMVP_D_X (_ : (regidx × regidx × fregidx))
  | FLEQ_H (_ : (fregidx × fregidx × regidx))
  | FLTQ_H (_ : (fregidx × fregidx × regidx))
  | FLEQ_S (_ : (fregidx × fregidx × regidx))
  | FLTQ_S (_ : (fregidx × fregidx × regidx))
  | FLEQ_D (_ : (fregidx × fregidx × regidx))
  | FLTQ_D (_ : (fregidx × fregidx × regidx))
  | FCVTMOD_W_D (_ : (fregidx × regidx))
  | VSETVLI (_ : ((BitVec 1) × (BitVec 1) × (BitVec 3) × (BitVec 3) × regidx × regidx))
  | VSETVL (_ : (regidx × regidx × regidx))
  | VSETIVLI (_ : ((BitVec 1) × (BitVec 1) × (BitVec 3) × (BitVec 3) × (BitVec 5) × regidx))
  | VVTYPE (_ : (vvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | NVSTYPE (_ : (nvsfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | NVTYPE (_ : (nvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | MASKTYPEV (_ : (vregidx × vregidx × vregidx))
  | MOVETYPEV (_ : (vregidx × vregidx))
  | VXTYPE (_ : (vxfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | NXSTYPE (_ : (nxsfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | NXTYPE (_ : (nxfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | VXSG (_ : (vxsgfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | MASKTYPEX (_ : (vregidx × regidx × vregidx))
  | MOVETYPEX (_ : (regidx × vregidx))
  | VITYPE (_ : (vifunct6 × (BitVec 1) × vregidx × (BitVec 5) × vregidx))
  | NISTYPE (_ : (nisfunct6 × (BitVec 1) × vregidx × (BitVec 5) × vregidx))
  | NITYPE (_ : (nifunct6 × (BitVec 1) × vregidx × (BitVec 5) × vregidx))
  | VISG (_ : (visgfunct6 × (BitVec 1) × vregidx × (BitVec 5) × vregidx))
  | MASKTYPEI (_ : (vregidx × (BitVec 5) × vregidx))
  | MOVETYPEI (_ : (vregidx × (BitVec 5)))
  | VMVRTYPE (_ : (vregidx × Int × vregidx))
  | MVVTYPE (_ : (mvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | MVVMATYPE (_ : (mvvmafunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | WVVTYPE (_ : (wvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | WVTYPE (_ : (wvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | WMVVTYPE (_ : (wmvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | VEXTTYPE (_ : (vextfunct6 × (BitVec 1) × vregidx × vregidx))
  | VMVXS (_ : (vregidx × regidx))
  | MVVCOMPRESS (_ : (vregidx × vregidx × vregidx))
  | MVXTYPE (_ : (mvxfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | MVXMATYPE (_ : (mvxmafunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | WVXTYPE (_ : (wvxfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | WXTYPE (_ : (wxfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | WMVXTYPE (_ : (wmvxfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | VMVSX (_ : (regidx × vregidx))
  | FVVTYPE (_ : (fvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | FVVMATYPE (_ : (fvvmafunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | FWVVTYPE (_ : (fwvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | FWVVMATYPE (_ : (fwvvmafunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | FWVTYPE (_ : (fwvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | VFUNARY0 (_ : ((BitVec 1) × vregidx × vfunary0 × vregidx))
  | VFWUNARY0 (_ : ((BitVec 1) × vregidx × vfwunary0 × vregidx))
  | VFNUNARY0 (_ : ((BitVec 1) × vregidx × vfnunary0 × vregidx))
  | VFUNARY1 (_ : ((BitVec 1) × vregidx × vfunary1 × vregidx))
  | VFMVFS (_ : (vregidx × fregidx))
  | FVFTYPE (_ : (fvffunct6 × (BitVec 1) × vregidx × fregidx × vregidx))
  | FVFMATYPE (_ : (fvfmafunct6 × (BitVec 1) × vregidx × fregidx × vregidx))
  | FWVFTYPE (_ : (fwvffunct6 × (BitVec 1) × vregidx × fregidx × vregidx))
  | FWVFMATYPE (_ : (fwvfmafunct6 × (BitVec 1) × fregidx × vregidx × vregidx))
  | FWFTYPE (_ : (fwffunct6 × (BitVec 1) × vregidx × fregidx × vregidx))
  | VFMERGE (_ : (vregidx × fregidx × vregidx))
  | VFMV (_ : (fregidx × vregidx))
  | VFMVSF (_ : (fregidx × vregidx))
  | VLSEGTYPE (_ : (nfields × (BitVec 1) × regidx × vlewidth × vregidx))
  | VLSEGFFTYPE (_ : (nfields × (BitVec 1) × regidx × vlewidth × vregidx))
  | VSSEGTYPE (_ : (nfields × (BitVec 1) × regidx × vlewidth × vregidx))
  | VLSSEGTYPE (_ : (nfields × (BitVec 1) × regidx × regidx × vlewidth × vregidx))
  | VSSSEGTYPE (_ : (nfields × (BitVec 1) × regidx × regidx × vlewidth × vregidx))
  | VLUXSEGTYPE (_ : (nfields × (BitVec 1) × vregidx × regidx × vlewidth × vregidx))
  | VLOXSEGTYPE (_ : (nfields × (BitVec 1) × vregidx × regidx × vlewidth × vregidx))
  | VSUXSEGTYPE (_ : (nfields × (BitVec 1) × vregidx × regidx × vlewidth × vregidx))
  | VSOXSEGTYPE (_ : (nfields × (BitVec 1) × vregidx × regidx × vlewidth × vregidx))
  | VLRETYPE (_ : (nfields_pow2 × regidx × vlewidth × vregidx))
  | VSRETYPE (_ : (nfields_pow2 × regidx × vregidx))
  | VMTYPE (_ : (regidx × vregidx × vmlsop))
  | MMTYPE (_ : (mmfunct6 × vregidx × vregidx × vregidx))
  | VCPOP_M (_ : ((BitVec 1) × vregidx × regidx))
  | VFIRST_M (_ : ((BitVec 1) × vregidx × regidx))
  | VMSBF_M (_ : ((BitVec 1) × vregidx × vregidx))
  | VMSIF_M (_ : ((BitVec 1) × vregidx × vregidx))
  | VMSOF_M (_ : ((BitVec 1) × vregidx × vregidx))
  | VIOTA_M (_ : ((BitVec 1) × vregidx × vregidx))
  | VID_V (_ : ((BitVec 1) × vregidx))
  | VVMTYPE (_ : (vvmfunct6 × vregidx × vregidx × vregidx))
  | VVMCTYPE (_ : (vvmcfunct6 × vregidx × vregidx × vregidx))
  | VVMSTYPE (_ : (vvmsfunct6 × vregidx × vregidx × vregidx))
  | VVCMPTYPE (_ : (vvcmpfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | VXMTYPE (_ : (vxmfunct6 × vregidx × regidx × vregidx))
  | VXMCTYPE (_ : (vxmcfunct6 × vregidx × regidx × vregidx))
  | VXMSTYPE (_ : (vxmsfunct6 × vregidx × regidx × vregidx))
  | VXCMPTYPE (_ : (vxcmpfunct6 × (BitVec 1) × vregidx × regidx × vregidx))
  | VIMTYPE (_ : (vimfunct6 × vregidx × (BitVec 5) × vregidx))
  | VIMCTYPE (_ : (vimcfunct6 × vregidx × (BitVec 5) × vregidx))
  | VIMSTYPE (_ : (vimsfunct6 × vregidx × (BitVec 5) × vregidx))
  | VICMPTYPE (_ : (vicmpfunct6 × (BitVec 1) × vregidx × (BitVec 5) × vregidx))
  | FVVMTYPE (_ : (fvvmfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | FVFMTYPE (_ : (fvfmfunct6 × (BitVec 1) × vregidx × fregidx × vregidx))
  | RIVVTYPE (_ : (rivvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | RMVVTYPE (_ : (rmvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | RFVVTYPE (_ : (rfvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | SHA256SIG0 (_ : (regidx × regidx))
  | SHA256SIG1 (_ : (regidx × regidx))
  | SHA256SUM0 (_ : (regidx × regidx))
  | SHA256SUM1 (_ : (regidx × regidx))
  | AES32ESMI (_ : ((BitVec 2) × regidx × regidx × regidx))
  | AES32ESI (_ : ((BitVec 2) × regidx × regidx × regidx))
  | AES32DSMI (_ : ((BitVec 2) × regidx × regidx × regidx))
  | AES32DSI (_ : ((BitVec 2) × regidx × regidx × regidx))
  | SHA512SIG0L (_ : (regidx × regidx × regidx))
  | SHA512SIG0H (_ : (regidx × regidx × regidx))
  | SHA512SIG1L (_ : (regidx × regidx × regidx))
  | SHA512SIG1H (_ : (regidx × regidx × regidx))
  | SHA512SUM0R (_ : (regidx × regidx × regidx))
  | SHA512SUM1R (_ : (regidx × regidx × regidx))
  | AES64KS1I (_ : ((BitVec 4) × regidx × regidx))
  | AES64KS2 (_ : (regidx × regidx × regidx))
  | AES64IM (_ : (regidx × regidx))
  | AES64ESM (_ : (regidx × regidx × regidx))
  | AES64ES (_ : (regidx × regidx × regidx))
  | AES64DSM (_ : (regidx × regidx × regidx))
  | AES64DS (_ : (regidx × regidx × regidx))
  | SHA512SIG0 (_ : (regidx × regidx))
  | SHA512SIG1 (_ : (regidx × regidx))
  | SHA512SUM0 (_ : (regidx × regidx))
  | SHA512SUM1 (_ : (regidx × regidx))
  | SM3P0 (_ : (regidx × regidx))
  | SM3P1 (_ : (regidx × regidx))
  | SM4ED (_ : ((BitVec 2) × regidx × regidx × regidx))
  | SM4KS (_ : ((BitVec 2) × regidx × regidx × regidx))
  | ZBKB_RTYPE (_ : (regidx × regidx × regidx × brop_zbkb))
  | ZBKB_PACKW (_ : (regidx × regidx × regidx))
  | ZIP (_ : (regidx × regidx))
  | UNZIP (_ : (regidx × regidx))
  | BREV8 (_ : (regidx × regidx))
  | XPERM8 (_ : (regidx × regidx × regidx))
  | XPERM4 (_ : (regidx × regidx × regidx))
  | VANDN_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VANDN_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VBREV_V (_ : ((BitVec 1) × vregidx × vregidx))
  | VBREV8_V (_ : ((BitVec 1) × vregidx × vregidx))
  | VREV8_V (_ : ((BitVec 1) × vregidx × vregidx))
  | VCLZ_V (_ : ((BitVec 1) × vregidx × vregidx))
  | VCTZ_V (_ : ((BitVec 1) × vregidx × vregidx))
  | VCPOP_V (_ : ((BitVec 1) × vregidx × vregidx))
  | VROL_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VROL_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VROR_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VROR_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VROR_VI (_ : ((BitVec 1) × vregidx × (BitVec 6) × vregidx))
  | VWSLL_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VWSLL_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VWSLL_VI (_ : ((BitVec 1) × vregidx × (BitVec 5) × vregidx))
  | VCLMUL_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VCLMUL_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VCLMULH_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VCLMULH_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VGHSH_VV (_ : (vregidx × vregidx × vregidx))
  | VGMUL_VV (_ : (vregidx × vregidx))
  | VAESDF (_ : (zvk_vaesdf_funct6 × vregidx × vregidx))
  | VAESDM (_ : (zvk_vaesdm_funct6 × vregidx × vregidx))
  | VAESEF (_ : (zvk_vaesef_funct6 × vregidx × vregidx))
  | VAESEM (_ : (zvk_vaesem_funct6 × vregidx × vregidx))
  | VAESKF1_VI (_ : (vregidx × (BitVec 5) × vregidx))
  | VAESKF2_VI (_ : (vregidx × (BitVec 5) × vregidx))
  | VAESZ_VS (_ : (vregidx × vregidx))
  | VSM4K_VI (_ : (vregidx × (BitVec 5) × vregidx))
  | ZVKSM4RTYPE (_ : (zvk_vsm4r_funct6 × vregidx × vregidx))
  | VSHA2MS_VV (_ : (vregidx × vregidx × vregidx))
  | ZVKSHA2TYPE (_ : (zvk_vsha2_funct6 × vregidx × vregidx × vregidx))
  | VSM3ME_VV (_ : (vregidx × vregidx × vregidx))
  | VSM3C_VI (_ : (vregidx × (BitVec 5) × vregidx))
  | CSRReg (_ : (csreg × regidx × regidx × csrop))
  | CSRImm (_ : (csreg × (BitVec 5) × regidx × csrop))
  | SINVAL_VMA (_ : (regidx × regidx))
  | SFENCE_W_INVAL (_ : Unit)
  | SFENCE_INVAL_IR (_ : Unit)
  | WRS (_ : wrsop)
  | ZICOND_RTYPE (_ : (regidx × regidx × regidx × zicondop))
  | ZICBOM (_ : (cbop_zicbom × regidx))
  | ZICBOZ (_ : regidx)
  | FENCEI (_ : Unit)
  | FCVT_BF16_S (_ : (fregidx × rounding_mode × fregidx))
  | FCVT_S_BF16 (_ : (fregidx × rounding_mode × fregidx))
  | ZIMOP_MOP_R (_ : ((BitVec 5) × regidx × regidx))
  | ZIMOP_MOP_RR (_ : ((BitVec 3) × regidx × regidx × regidx))
  | ZCMOP (_ : (BitVec 3))
  deriving Inhabited, Repr

inductive PTW_Error where
  | PTW_Invalid_Addr (_ : Unit)
  | PTW_Access (_ : Unit)
  | PTW_Invalid_PTE (_ : Unit)
  | PTW_No_Permission (_ : Unit)
  | PTW_Misaligned (_ : Unit)
  | PTW_PTE_Update (_ : Unit)
  | PTW_Ext_Error (_ : ext_ptw_error)
  deriving Inhabited, BEq, Repr

inductive WaitReason where | WAIT_WFI | WAIT_WRS_STO | WAIT_WRS_NTO
  deriving BEq, Inhabited, Repr



inductive InterruptType where | I_U_Software | I_S_Software | I_M_Software | I_U_Timer | I_S_Timer | I_M_Timer | I_U_External | I_S_External | I_M_External
  deriving BEq, Inhabited, Repr

abbrev tv_mode := (BitVec 2)

inductive TrapVectorMode where | TV_Direct | TV_Vector | TV_Reserved
  deriving BEq, Inhabited, Repr

abbrev ext_status := (BitVec 2)

inductive ExtStatus where | Off | Initial | Clean | Dirty
  deriving BEq, Inhabited, Repr

abbrev satp_mode := (BitVec 4)

inductive SATPMode where | Bare | Sv32 | Sv39 | Sv48 | Sv57
  deriving BEq, Inhabited, Repr

abbrev csrRW := (BitVec 2)



abbrev level_range (k_v : Nat) := Nat

abbrev pte_bits k_v := (BitVec (if ( k_v = 32  : Bool) then 32 else 64))

abbrev ppn_bits k_v := (BitVec (if ( k_v = 32  : Bool) then 22 else 44))

abbrev vpn_bits k_v := (BitVec (k_v - 12))

abbrev ext_access_type := Unit

abbrev regtype := xlenbits

abbrev Seccfg := (BitVec 64)

abbrev MEnvcfg := (BitVec 64)

abbrev SEnvcfg := (BitVec 64)

abbrev Minterrupts := (BitVec 64)

abbrev Medeleg := (BitVec 64)

abbrev Mtvec := (BitVec 64)

abbrev Mcause := (BitVec 64)

abbrev Counteren := (BitVec 32)

abbrev Counterin := (BitVec 32)

abbrev Sstatus := (BitVec 64)

abbrev Sinterrupts := (BitVec 64)

abbrev Satp64 := (BitVec 64)

abbrev Satp32 := (BitVec 32)

/-- Type quantifiers: k_a : Type -/
inductive Ext_DataAddr_Check (k_a : Type) where
  | Ext_DataAddr_OK (_ : virtaddr)
  | Ext_DataAddr_Error (_ : k_a)
  deriving Inhabited, BEq, Repr

abbrev ext_fetch_addr_error := Unit

abbrev ext_control_addr_error := Unit

abbrev ext_data_addr_error := Unit

abbrev bits_rm := (BitVec 3)

abbrev bits_fflags := (BitVec 5)

abbrev bits_BF16 := (BitVec 16)

abbrev bits_H := (BitVec 16)

abbrev bits_S := (BitVec 32)

abbrev bits_D := (BitVec 64)

abbrev bits_W := (BitVec 32)

abbrev bits_WU := (BitVec 32)

abbrev bits_L := (BitVec 64)

abbrev bits_LU := (BitVec 64)

abbrev ext_exception := Unit

structure sync_exception where
  trap : ExceptionType
  excinfo : (Option xlenbits)
  ext : (Option ext_exception)
  deriving BEq, Inhabited, Repr

inductive PmpAddrMatchType where | OFF | TOR | NA4 | NAPOT
  deriving BEq, Inhabited, Repr

abbrev Pmpcfg_ent := (BitVec 8)

inductive pmpAddrMatch where | PMP_NoMatch | PMP_PartialMatch | PMP_Match
  deriving BEq, Inhabited, Repr

abbrev fregtype := flenbits

inductive fregno where
  | Fregno (_ : Nat)
  deriving Inhabited, BEq, Repr

abbrev Fcsr := (BitVec 32)

abbrev vlenbits := (BitVec (2 ^ 8))

inductive maskfunct3 where | VV_VMERGE | VI_VMERGE | VX_VMERGE
  deriving BEq, Inhabited, Repr

inductive vregno where
  | Vregno (_ : Nat)
  deriving Inhabited, BEq, Repr

abbrev Vtype := (BitVec 64)

abbrev SEW_pow := Nat

abbrev LMUL_pow := Int

abbrev sew_bitsize := Int



inductive agtype where | UNDISTURBED | AGNOSTIC
  deriving BEq, Inhabited, Repr

abbrev Vcsr := (BitVec 3)

abbrev CountSmcntrpmf := (BitVec 64)

inductive ctl_result where
  | CTL_TRAP (_ : sync_exception)
  | CTL_SRET (_ : Unit)
  | CTL_MRET (_ : Unit)
  deriving Inhabited, BEq, Repr

abbrev MemoryOpResult k_a := (Result k_a ExceptionType)

abbrev htif_cmd := (BitVec 64)

inductive ExecutionResult where
  | Retire_Success (_ : Unit)
  | Enter_Wait (_ : WaitReason)
  | Illegal_Instruction (_ : Unit)
  | Trap (_ : (Privilege × ctl_result × xlenbits))
  | Memory_Exception (_ : (virtaddr × ExceptionType))
  | Ext_CSR_Check_Failure (_ : Unit)
  | Ext_ControlAddr_Check_Failure (_ : ext_control_addr_error)
  | Ext_DataAddr_Check_Failure (_ : ext_data_addr_error)
  | Ext_XRET_Priv_Failure (_ : Unit)
  deriving Inhabited, BEq, Repr

abbrev pte_flags_bits := (BitVec 8)

abbrev pte_ext_bits := (BitVec 10)

abbrev PTE_Ext := (BitVec 10)

abbrev PTE_Flags := (BitVec 8)

inductive PTE_Check where
  | PTE_Check_Success (_ : ext_ptw)
  | PTE_Check_Failure (_ : (ext_ptw × ext_ptw_fail))
  deriving Inhabited, BEq, Repr

abbrev tlb_vpn_bits : Int := (57 - 12)

abbrev tlb_ppn_bits : Int := 44

structure TLB_Entry where
  asid : asidbits
  global : Bool
  vpn : (BitVec (57 - 12))
  levelMask : (BitVec (57 - 12))
  ppn : (BitVec 44)
  pte : (BitVec 64)
  pteAddr : physaddr
  deriving BEq, Inhabited, Repr

abbrev num_tlb_entries : Int := 64

abbrev tlb_index_range := Nat

/-- Type quantifiers: k_v : Int, is_sv_mode(k_v) -/
structure PTW_Output (k_v : Nat) where
  ppn : (ppn_bits k_v)
  pte : (pte_bits k_v)
  pteAddr : physaddr
  level : (level_range k_v)
  global : Bool
  deriving BEq, Inhabited, Repr

abbrev PTW_Result k_v := (Result ((PTW_Output k_v) × ext_ptw) (PTW_Error × ext_ptw))

abbrev TR_Result k_paddr k_failure := (Result (k_paddr × ext_ptw) (k_failure × ext_ptw))



inductive seed_opst where | BIST | ES16 | WAIT | DEAD
  deriving BEq, Inhabited, Repr

abbrev HpmEvent := (BitVec 64)

abbrev hpmidx := Nat

inductive cbie where | CBIE_ILLEGAL | CBIE_EXEC_FLUSH | CBIE_EXEC_INVAL
  deriving BEq, Inhabited, Repr

inductive checked_cbop where | CBOP_ILLEGAL | CBOP_ILLEGAL_VIRTUAL | CBOP_INVAL_FLUSH | CBOP_INVAL_INVAL
  deriving BEq, Inhabited, Repr

inductive HartState where
  | HART_ACTIVE (_ : Unit)
  | HART_WAITING (_ : (WaitReason × instbits))
  deriving Inhabited, BEq, Repr

inductive FetchResult where
  | F_Ext_Error (_ : ext_fetch_addr_error)
  | F_Base (_ : word)
  | F_RVC (_ : half)
  | F_Error (_ : (ExceptionType × xlenbits))
  deriving Inhabited, BEq, Repr

inductive Step where
  | Step_Pending_Interrupt (_ : (InterruptType × Privilege))
  | Step_Ext_Fetch_Failure (_ : ext_fetch_addr_error)
  | Step_Fetch_Failure (_ : (virtaddr × ExceptionType))
  | Step_Execute (_ : (ExecutionResult × instbits))
  | Step_Waiting (_ : WaitReason)
  deriving Inhabited, BEq, Repr

inductive ISA_Format where | Canonical_Lowercase | DeviceTree_ISA_Extensions
  deriving BEq, Inhabited, Repr

inductive Register : Type where
  | hart_state
  | mhpmcounter
  | mhpmevent
  | satp
  | tlb
  | htif_payload_writes
  | htif_cmd_write
  | htif_exit_code
  | htif_done
  | htif_tohost
  | stimecmp
  | mtimecmp
  | htif_tohost_base
  | plat_clint_size
  | plat_clint_base
  | plat_rom_size
  | plat_rom_base
  | plat_ram_size
  | plat_ram_base
  | pc_reset_address
  | minstretcfg
  | mcyclecfg
  | vcsr
  | vtype
  | vl
  | vstart
  | vr31
  | vr30
  | vr29
  | vr28
  | vr27
  | vr26
  | vr25
  | vr24
  | vr23
  | vr22
  | vr21
  | vr20
  | vr19
  | vr18
  | vr17
  | vr16
  | vr15
  | vr14
  | vr13
  | vr12
  | vr11
  | vr10
  | vr9
  | vr8
  | vr7
  | vr6
  | vr5
  | vr4
  | vr3
  | vr2
  | vr1
  | vr0
  | fcsr
  | f31
  | f30
  | f29
  | f28
  | f27
  | f26
  | f25
  | f24
  | f23
  | f22
  | f21
  | f20
  | f19
  | f18
  | f17
  | f16
  | f15
  | f14
  | f13
  | f12
  | f11
  | f10
  | f9
  | f8
  | f7
  | f6
  | f5
  | f4
  | f3
  | f2
  | f1
  | f0
  | pmpaddr_n
  | pmpcfg_n
  | tselect
  | stval
  | scause
  | sepc
  | sscratch
  | stvec
  | mconfigptr
  | mhartid
  | marchid
  | mimpid
  | mvendorid
  | minstret_increment
  | minstret
  | mtime
  | mcycle
  | mcountinhibit
  | mcounteren
  | scounteren
  | mscratch
  | mtval
  | mepc
  | mcause
  | mtvec
  | mideleg
  | medeleg
  | mip
  | mie
  | senvcfg
  | menvcfg
  | mseccfg
  | cur_inst
  | cur_privilege
  | x31
  | x30
  | x29
  | x28
  | x27
  | x26
  | x25
  | x24
  | x23
  | x22
  | x21
  | x20
  | x19
  | x18
  | x17
  | x16
  | x15
  | x14
  | x13
  | x12
  | x11
  | x10
  | x9
  | x8
  | x7
  | x6
  | x5
  | x4
  | x3
  | x2
  | x1
  | nextPC
  | PC
  | mstatus
  | misa
  | rvfi_mem_data_present
  | rvfi_mem_data
  | rvfi_int_data_present
  | rvfi_int_data
  | rvfi_pc_data
  | rvfi_inst_data
  | rvfi_instruction
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .hart_state => HartState
  | .mhpmcounter => (Vector (BitVec 64) 32)
  | .mhpmevent => (Vector (BitVec 64) 32)
  | .satp => (BitVec 64)
  | .tlb => (Vector (Option TLB_Entry) 64)
  | .htif_payload_writes => (BitVec 4)
  | .htif_cmd_write => (BitVec 1)
  | .htif_exit_code => (BitVec 64)
  | .htif_done => Bool
  | .htif_tohost => (BitVec 64)
  | .stimecmp => (BitVec 64)
  | .mtimecmp => (BitVec 64)
  | .htif_tohost_base => (Option (BitVec (if ( 64 = 32  : Bool) then 34 else 64)))
  | .plat_clint_size => (BitVec (if ( 64 = 32  : Bool) then 34 else 64))
  | .plat_clint_base => (BitVec (if ( 64 = 32  : Bool) then 34 else 64))
  | .plat_rom_size => (BitVec (if ( 64 = 32  : Bool) then 34 else 64))
  | .plat_rom_base => (BitVec (if ( 64 = 32  : Bool) then 34 else 64))
  | .plat_ram_size => (BitVec (if ( 64 = 32  : Bool) then 34 else 64))
  | .plat_ram_base => (BitVec (if ( 64 = 32  : Bool) then 34 else 64))
  | .pc_reset_address => (BitVec 64)
  | .minstretcfg => (BitVec 64)
  | .mcyclecfg => (BitVec 64)
  | .vcsr => (BitVec 3)
  | .vtype => (BitVec 64)
  | .vl => (BitVec 64)
  | .vstart => (BitVec 64)
  | .vr31 => (BitVec (2 ^ 8))
  | .vr30 => (BitVec (2 ^ 8))
  | .vr29 => (BitVec (2 ^ 8))
  | .vr28 => (BitVec (2 ^ 8))
  | .vr27 => (BitVec (2 ^ 8))
  | .vr26 => (BitVec (2 ^ 8))
  | .vr25 => (BitVec (2 ^ 8))
  | .vr24 => (BitVec (2 ^ 8))
  | .vr23 => (BitVec (2 ^ 8))
  | .vr22 => (BitVec (2 ^ 8))
  | .vr21 => (BitVec (2 ^ 8))
  | .vr20 => (BitVec (2 ^ 8))
  | .vr19 => (BitVec (2 ^ 8))
  | .vr18 => (BitVec (2 ^ 8))
  | .vr17 => (BitVec (2 ^ 8))
  | .vr16 => (BitVec (2 ^ 8))
  | .vr15 => (BitVec (2 ^ 8))
  | .vr14 => (BitVec (2 ^ 8))
  | .vr13 => (BitVec (2 ^ 8))
  | .vr12 => (BitVec (2 ^ 8))
  | .vr11 => (BitVec (2 ^ 8))
  | .vr10 => (BitVec (2 ^ 8))
  | .vr9 => (BitVec (2 ^ 8))
  | .vr8 => (BitVec (2 ^ 8))
  | .vr7 => (BitVec (2 ^ 8))
  | .vr6 => (BitVec (2 ^ 8))
  | .vr5 => (BitVec (2 ^ 8))
  | .vr4 => (BitVec (2 ^ 8))
  | .vr3 => (BitVec (2 ^ 8))
  | .vr2 => (BitVec (2 ^ 8))
  | .vr1 => (BitVec (2 ^ 8))
  | .vr0 => (BitVec (2 ^ 8))
  | .fcsr => (BitVec 32)
  | .f31 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f30 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f29 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f28 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f27 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f26 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f25 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f24 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f23 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f22 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f21 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f20 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f19 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f18 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f17 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f16 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f15 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f14 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f13 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f12 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f11 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f10 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f9 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f8 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f7 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f6 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f5 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f4 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f3 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f2 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f1 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .f0 => (BitVec (if ( true  : Bool) then 8 else 4 * 8))
  | .pmpaddr_n => (Vector (BitVec 64) 64)
  | .pmpcfg_n => (Vector (BitVec 8) 64)
  | .tselect => (BitVec 64)
  | .stval => (BitVec 64)
  | .scause => (BitVec 64)
  | .sepc => (BitVec 64)
  | .sscratch => (BitVec 64)
  | .stvec => (BitVec 64)
  | .mconfigptr => (BitVec 64)
  | .mhartid => (BitVec 64)
  | .marchid => (BitVec 64)
  | .mimpid => (BitVec 64)
  | .mvendorid => (BitVec 32)
  | .minstret_increment => Bool
  | .minstret => (BitVec 64)
  | .mtime => (BitVec 64)
  | .mcycle => (BitVec 64)
  | .mcountinhibit => (BitVec 32)
  | .mcounteren => (BitVec 32)
  | .scounteren => (BitVec 32)
  | .mscratch => (BitVec 64)
  | .mtval => (BitVec 64)
  | .mepc => (BitVec 64)
  | .mcause => (BitVec 64)
  | .mtvec => (BitVec 64)
  | .mideleg => (BitVec 64)
  | .medeleg => (BitVec 64)
  | .mip => (BitVec 64)
  | .mie => (BitVec 64)
  | .senvcfg => (BitVec 64)
  | .menvcfg => (BitVec 64)
  | .mseccfg => (BitVec 64)
  | .cur_inst => (BitVec 64)
  | .cur_privilege => Privilege
  | .x31 => (BitVec 64)
  | .x30 => (BitVec 64)
  | .x29 => (BitVec 64)
  | .x28 => (BitVec 64)
  | .x27 => (BitVec 64)
  | .x26 => (BitVec 64)
  | .x25 => (BitVec 64)
  | .x24 => (BitVec 64)
  | .x23 => (BitVec 64)
  | .x22 => (BitVec 64)
  | .x21 => (BitVec 64)
  | .x20 => (BitVec 64)
  | .x19 => (BitVec 64)
  | .x18 => (BitVec 64)
  | .x17 => (BitVec 64)
  | .x16 => (BitVec 64)
  | .x15 => (BitVec 64)
  | .x14 => (BitVec 64)
  | .x13 => (BitVec 64)
  | .x12 => (BitVec 64)
  | .x11 => (BitVec 64)
  | .x10 => (BitVec 64)
  | .x9 => (BitVec 64)
  | .x8 => (BitVec 64)
  | .x7 => (BitVec 64)
  | .x6 => (BitVec 64)
  | .x5 => (BitVec 64)
  | .x4 => (BitVec 64)
  | .x3 => (BitVec 64)
  | .x2 => (BitVec 64)
  | .x1 => (BitVec 64)
  | .nextPC => (BitVec 64)
  | .PC => (BitVec 64)
  | .mstatus => (BitVec 64)
  | .misa => (BitVec 64)
  | .rvfi_mem_data_present => Bool
  | .rvfi_mem_data => (BitVec 704)
  | .rvfi_int_data_present => Bool
  | .rvfi_int_data => (BitVec 320)
  | .rvfi_pc_data => (BitVec 128)
  | .rvfi_inst_data => (BitVec 192)
  | .rvfi_instruction => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType HartState) where
  default := .Reg hart_state
instance : Inhabited (RegisterRef RegisterType Privilege) where
  default := .Reg cur_privilege
instance : Inhabited (RegisterRef RegisterType (BitVec 1)) where
  default := .Reg htif_cmd_write
instance : Inhabited (RegisterRef RegisterType (BitVec 128)) where
  default := .Reg rvfi_pc_data
instance : Inhabited (RegisterRef RegisterType (BitVec 192)) where
  default := .Reg rvfi_inst_data
instance : Inhabited (RegisterRef RegisterType (BitVec 3)) where
  default := .Reg vcsr
instance : Inhabited (RegisterRef RegisterType (BitVec 32)) where
  default := .Reg scounteren
instance : Inhabited (RegisterRef RegisterType (BitVec 320)) where
  default := .Reg rvfi_int_data
instance : Inhabited (RegisterRef RegisterType (BitVec 4)) where
  default := .Reg htif_payload_writes
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg rvfi_instruction
instance : Inhabited (RegisterRef RegisterType (BitVec 704)) where
  default := .Reg rvfi_mem_data
instance : Inhabited (RegisterRef RegisterType (BitVec (2 ^ 8))) where
  default := .Reg vr0
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg rvfi_int_data_present
instance : Inhabited (RegisterRef RegisterType (Option (BitVec (if ( 64 = 32  : Bool) then 34 else 64)))) where
  default := .Reg htif_tohost_base
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 32)) where
  default := .Reg mhpmevent
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 64)) where
  default := .Reg pmpaddr_n
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 8) 64)) where
  default := .Reg pmpcfg_n
instance : Inhabited (RegisterRef RegisterType (Vector (Option TLB_Entry) 64)) where
  default := .Reg tlb
abbrev SailM := PreSailM RegisterType trivialChoiceSource exception

instance : Arch where
  va_size := 64
  pa := (BitVec (if ( 64 = 32  : Bool) then 34 else 64))
  abort := Unit
  translation := Unit
  trans_start := Unit
  trans_end := Unit
  fault := Unit
  tlb_op := Unit
  cache_op := Unit
  barrier := barrier_kind
  arch_ak := RISCV_strong_access
  sys_reg_id := Unit
