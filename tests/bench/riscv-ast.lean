/-
Benchmark taken from
https://github.com/opencompl/sail-riscv-lean
file LeanRV64D/Defs.lean
revision 1d0e7341582a65d194acf84252d55165ae99add3
https://raw.githubusercontent.com/opencompl/sail-riscv-lean/refs/heads/main/LeanRV64D/Defs.lean

The original file was generated from the Sail RISC-V model:

This Sail RISC-V architecture model, comprising all files and
directories except for the snapshots of the Lem and Sail libraries
in the prover_snapshots directory (which include copies of their
licences), is subject to the BSD two-clause licence.

We truncated the file using, `#exit`, after the 200th constructor of the `ast` inductive, for a
manageable benchmark size.
-/

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

set_option trace.profiler true
set_option trace.profiler.threshold 100
set_option pp.oneline true

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq

abbrev bits k_n := (BitVec k_n)

abbrev xlenbits := (BitVec (2 ^ 3 * 8))

inductive virtaddr where
  | Virtaddr (_ : xlenbits)
  deriving Inhabited, BEq

abbrev max_mem_access : Int := 4096

abbrev mem_access_width := Nat

inductive exception where
  | Error_not_implemented (_ : String)
  | Error_internal_error (_ : Unit)
  deriving Inhabited, BEq

abbrev log2_xlen_bytes : Int := 3

abbrev physaddrbits_len : Int := 64

abbrev asidlen : Int := 16

abbrev log2_xlen : Int := (3 + 3)

abbrev xlen_bytes : Int := (2 ^ 3)

abbrev xlen : Int := (2 ^ 3 * 8)

abbrev asidbits := (BitVec 16)

abbrev flen_bytes : Int := 8

abbrev flen : Int := (8 * 8)

abbrev flenbits := (BitVec (8 * 8))

abbrev vlenmax : Int := 65536

abbrev physaddrbits := (BitVec 64)

inductive physaddr where
  | Physaddr (_ : physaddrbits)
  deriving Inhabited, BEq

abbrev mem_meta := Unit

inductive write_kind where | Write_plain | Write_RISCV_release | Write_RISCV_strong_release | Write_RISCV_conditional | Write_RISCV_conditional_release | Write_RISCV_conditional_strong_release
  deriving Inhabited, BEq

inductive read_kind where | Read_plain | Read_ifetch | Read_RISCV_acquire | Read_RISCV_strong_acquire | Read_RISCV_reserved | Read_RISCV_reserved_acquire | Read_RISCV_reserved_strong_acquire
  deriving Inhabited, BEq

inductive barrier_kind where | Barrier_RISCV_rw_rw | Barrier_RISCV_r_rw | Barrier_RISCV_r_r | Barrier_RISCV_rw_w | Barrier_RISCV_w_w | Barrier_RISCV_w_rw | Barrier_RISCV_rw_r | Barrier_RISCV_r_w | Barrier_RISCV_w_r | Barrier_RISCV_tso | Barrier_RISCV_i
  deriving Inhabited, BEq

inductive Access_variety where
  | AV_plain
  | AV_exclusive
  | AV_atomic_rmw
  deriving Inhabited, DecidableEq

structure RISCV_strong_access where
  variety : Access_variety
  deriving Inhabited, BEq

inductive extension where | Ext_M | Ext_A | Ext_F | Ext_D | Ext_B | Ext_V | Ext_S | Ext_U | Ext_Zicbom | Ext_Zicboz | Ext_Zicntr | Ext_Zicond | Ext_Zifencei | Ext_Zihpm | Ext_Zimop | Ext_Zmmul | Ext_Zaamo | Ext_Zabha | Ext_Zalrsc | Ext_Zfa | Ext_Zfh | Ext_Zfhmin | Ext_Zfinx | Ext_Zdinx | Ext_Zca | Ext_Zcb | Ext_Zcd | Ext_Zcf | Ext_Zcmop | Ext_C | Ext_Zba | Ext_Zbb | Ext_Zbc | Ext_Zbkb | Ext_Zbkc | Ext_Zbkx | Ext_Zbs | Ext_Zknd | Ext_Zkne | Ext_Zknh | Ext_Zkr | Ext_Zksed | Ext_Zksh | Ext_Zhinx | Ext_Zvbb | Ext_Zvkb | Ext_Zvbc | Ext_Zvknha | Ext_Zvknhb | Ext_Sscofpmf | Ext_Sstc | Ext_Svinval | Ext_Svnapot | Ext_Svpbmt | Ext_Smcntrpmf
  deriving Inhabited, BEq

abbrev exc_code := (BitVec 8)

abbrev ext_ptw := Unit

abbrev ext_ptw_fail := Unit

abbrev ext_ptw_error := Unit

abbrev ext_exc_type := Unit

abbrev half := (BitVec 16)

abbrev word := (BitVec 32)

abbrev pagesize_bits : Int := 12

inductive regidx where
  | Regidx (_ : (BitVec 5))
  deriving Inhabited, BEq

inductive cregidx where
  | Cregidx (_ : (BitVec 3))
  deriving Inhabited, BEq

abbrev csreg := (BitVec 12)

inductive regno where
  | Regno (_ : Nat)
  deriving Inhabited, BEq

abbrev opcode := (BitVec 7)

abbrev imm12 := (BitVec 12)

abbrev imm20 := (BitVec 20)

abbrev amo := (BitVec 1)

inductive Architecture where | RV32 | RV64 | RV128
  deriving Inhabited, BEq

abbrev arch_xlen := (BitVec 2)

abbrev priv_level := (BitVec 2)

inductive Privilege where | User | Supervisor | Machine
  deriving Inhabited, BEq

/-- Type quantifiers: k_a : Type -/
inductive AccessType (k_a : Type) where
  | Read (_ : k_a)
  | Write (_ : k_a)
  | ReadWrite (_ : (k_a × k_a))
  | Execute (_ : Unit)
  deriving Inhabited, BEq

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
  deriving Inhabited, BEq

inductive amoop where | AMOSWAP | AMOADD | AMOXOR | AMOAND | AMOOR | AMOMIN | AMOMAX | AMOMINU | AMOMAXU
  deriving Inhabited, BEq

inductive bop where | RISCV_BEQ | RISCV_BNE | RISCV_BLT | RISCV_BGE | RISCV_BLTU | RISCV_BGEU
  deriving Inhabited, BEq

inductive cbop_zicbom where | CBO_CLEAN | CBO_FLUSH | CBO_INVAL
  deriving Inhabited, BEq

inductive csrop where | CSRRW | CSRRS | CSRRC
  deriving Inhabited, BEq

inductive f_bin_f_op_D where | FSGNJ_D | FSGNJN_D | FSGNJX_D | FMIN_D | FMAX_D
  deriving Inhabited, BEq

inductive f_bin_f_op_H where | FSGNJ_H | FSGNJN_H | FSGNJX_H | FMIN_H | FMAX_H
  deriving Inhabited, BEq

inductive f_bin_rm_op_D where | FADD_D | FSUB_D | FMUL_D | FDIV_D
  deriving Inhabited, BEq

inductive f_bin_rm_op_H where | FADD_H | FSUB_H | FMUL_H | FDIV_H
  deriving Inhabited, BEq

inductive f_bin_rm_op_S where | FADD_S | FSUB_S | FMUL_S | FDIV_S
  deriving Inhabited, BEq

inductive f_bin_op_f_S where | FSGNJ_S | FSGNJN_S | FSGNJX_S | FMIN_S | FMAX_S
  deriving Inhabited, BEq

inductive f_bin_op_x_S where | FEQ_S | FLT_S | FLE_S
  deriving Inhabited, BEq

inductive f_bin_x_op_D where | FEQ_D | FLT_D | FLE_D
  deriving Inhabited, BEq

inductive f_bin_x_op_H where | FEQ_H | FLT_H | FLE_H
  deriving Inhabited, BEq

inductive f_madd_op_D where | FMADD_D | FMSUB_D | FNMSUB_D | FNMADD_D
  deriving Inhabited, BEq

inductive f_madd_op_H where | FMADD_H | FMSUB_H | FNMSUB_H | FNMADD_H
  deriving Inhabited, BEq

inductive f_madd_op_S where | FMADD_S | FMSUB_S | FNMSUB_S | FNMADD_S
  deriving Inhabited, BEq

inductive f_un_f_op_D where | FMV_D_X
  deriving Inhabited, BEq

inductive f_un_f_op_H where | FMV_H_X
  deriving Inhabited, BEq

inductive f_un_rm_ff_op_D where | FSQRT_D | FCVT_S_D | FCVT_D_S
  deriving Inhabited, BEq

inductive f_un_rm_ff_op_H where | FSQRT_H | FCVT_H_S | FCVT_H_D | FCVT_S_H | FCVT_D_H
  deriving Inhabited, BEq

inductive f_un_rm_fx_op_D where | FCVT_W_D | FCVT_WU_D | FCVT_L_D | FCVT_LU_D
  deriving Inhabited, BEq

inductive f_un_rm_fx_op_H where | FCVT_W_H | FCVT_WU_H | FCVT_L_H | FCVT_LU_H
  deriving Inhabited, BEq

inductive f_un_rm_fx_op_S where | FCVT_W_S | FCVT_WU_S | FCVT_L_S | FCVT_LU_S
  deriving Inhabited, BEq

inductive f_un_rm_xf_op_D where | FCVT_D_W | FCVT_D_WU | FCVT_D_L | FCVT_D_LU
  deriving Inhabited, BEq

inductive f_un_rm_xf_op_H where | FCVT_H_W | FCVT_H_WU | FCVT_H_L | FCVT_H_LU
  deriving Inhabited, BEq

inductive f_un_rm_xf_op_S where | FCVT_S_W | FCVT_S_WU | FCVT_S_L | FCVT_S_LU
  deriving Inhabited, BEq

inductive f_un_op_f_S where | FMV_W_X
  deriving Inhabited, BEq

inductive f_un_op_x_S where | FCLASS_S | FMV_X_W
  deriving Inhabited, BEq

inductive f_un_x_op_D where | FCLASS_D | FMV_X_D
  deriving Inhabited, BEq

inductive f_un_x_op_H where | FCLASS_H | FMV_X_H
  deriving Inhabited, BEq

inductive fregidx where
  | Fregidx (_ : (BitVec 5))
  deriving Inhabited, BEq

inductive rounding_mode where | RM_RNE | RM_RTZ | RM_RDN | RM_RUP | RM_RMM | RM_DYN
  deriving Inhabited, BEq

inductive fvfmafunct6 where | VF_VMADD | VF_VNMADD | VF_VMSUB | VF_VNMSUB | VF_VMACC | VF_VNMACC | VF_VMSAC | VF_VNMSAC
  deriving Inhabited, BEq

inductive fvfmfunct6 where | VFM_VMFEQ | VFM_VMFLE | VFM_VMFLT | VFM_VMFNE | VFM_VMFGT | VFM_VMFGE
  deriving Inhabited, BEq

inductive fvffunct6 where | VF_VADD | VF_VSUB | VF_VMIN | VF_VMAX | VF_VSGNJ | VF_VSGNJN | VF_VSGNJX | VF_VDIV | VF_VRDIV | VF_VMUL | VF_VRSUB | VF_VSLIDE1UP | VF_VSLIDE1DOWN
  deriving Inhabited, BEq

inductive fvvmafunct6 where | FVV_VMADD | FVV_VNMADD | FVV_VMSUB | FVV_VNMSUB | FVV_VMACC | FVV_VNMACC | FVV_VMSAC | FVV_VNMSAC
  deriving Inhabited, BEq

inductive fvvmfunct6 where | FVVM_VMFEQ | FVVM_VMFLE | FVVM_VMFLT | FVVM_VMFNE
  deriving Inhabited, BEq

inductive fvvfunct6 where | FVV_VADD | FVV_VSUB | FVV_VMIN | FVV_VMAX | FVV_VSGNJ | FVV_VSGNJN | FVV_VSGNJX | FVV_VDIV | FVV_VMUL
  deriving Inhabited, BEq

inductive fwffunct6 where | FWF_VADD | FWF_VSUB
  deriving Inhabited, BEq

inductive fwvfmafunct6 where | FWVF_VMACC | FWVF_VNMACC | FWVF_VMSAC | FWVF_VNMSAC
  deriving Inhabited, BEq

inductive fwvffunct6 where | FWVF_VADD | FWVF_VSUB | FWVF_VMUL
  deriving Inhabited, BEq

inductive fwvfunct6 where | FWV_VADD | FWV_VSUB
  deriving Inhabited, BEq

inductive fwvvmafunct6 where | FWVV_VMACC | FWVV_VNMACC | FWVV_VMSAC | FWVV_VNMSAC
  deriving Inhabited, BEq

inductive fwvvfunct6 where | FWVV_VADD | FWVV_VSUB | FWVV_VMUL
  deriving Inhabited, BEq

inductive iop where | RISCV_ADDI | RISCV_SLTI | RISCV_SLTIU | RISCV_XORI | RISCV_ORI | RISCV_ANDI
  deriving Inhabited, BEq

inductive mmfunct6 where | MM_VMAND | MM_VMNAND | MM_VMANDN | MM_VMXOR | MM_VMOR | MM_VMNOR | MM_VMORN | MM_VMXNOR
  deriving Inhabited, BEq

structure mul_op where
  high : Bool
  signed_rs1 : Bool
  signed_rs2 : Bool
  deriving Inhabited, BEq

inductive mvvmafunct6 where | MVV_VMACC | MVV_VNMSAC | MVV_VMADD | MVV_VNMSUB
  deriving Inhabited, BEq

inductive mvvfunct6 where | MVV_VAADDU | MVV_VAADD | MVV_VASUBU | MVV_VASUB | MVV_VMUL | MVV_VMULH | MVV_VMULHU | MVV_VMULHSU | MVV_VDIVU | MVV_VDIV | MVV_VREMU | MVV_VREM
  deriving Inhabited, BEq

inductive mvxmafunct6 where | MVX_VMACC | MVX_VNMSAC | MVX_VMADD | MVX_VNMSUB
  deriving Inhabited, BEq

inductive mvxfunct6 where | MVX_VAADDU | MVX_VAADD | MVX_VASUBU | MVX_VASUB | MVX_VSLIDE1UP | MVX_VSLIDE1DOWN | MVX_VMUL | MVX_VMULH | MVX_VMULHU | MVX_VMULHSU | MVX_VDIVU | MVX_VDIV | MVX_VREMU | MVX_VREM
  deriving Inhabited, BEq

inductive nisfunct6 where | NIS_VNSRL | NIS_VNSRA
  deriving Inhabited, BEq

inductive nifunct6 where | NI_VNCLIPU | NI_VNCLIP
  deriving Inhabited, BEq

inductive nvsfunct6 where | NVS_VNSRL | NVS_VNSRA
  deriving Inhabited, BEq

inductive nvfunct6 where | NV_VNCLIPU | NV_VNCLIP
  deriving Inhabited, BEq

inductive nxsfunct6 where | NXS_VNSRL | NXS_VNSRA
  deriving Inhabited, BEq

inductive nxfunct6 where | NX_VNCLIPU | NX_VNCLIP
  deriving Inhabited, BEq

inductive rfvvfunct6 where | FVV_VFREDOSUM | FVV_VFREDUSUM | FVV_VFREDMAX | FVV_VFREDMIN | FVV_VFWREDOSUM | FVV_VFWREDUSUM
  deriving Inhabited, BEq

inductive rivvfunct6 where | IVV_VWREDSUMU | IVV_VWREDSUM
  deriving Inhabited, BEq

inductive rmvvfunct6 where | MVV_VREDSUM | MVV_VREDAND | MVV_VREDOR | MVV_VREDXOR | MVV_VREDMINU | MVV_VREDMIN | MVV_VREDMAXU | MVV_VREDMAX
  deriving Inhabited, BEq

inductive rop where | RISCV_ADD | RISCV_SUB | RISCV_SLL | RISCV_SLT | RISCV_SLTU | RISCV_XOR | RISCV_SRL | RISCV_SRA | RISCV_OR | RISCV_AND
  deriving Inhabited, BEq

inductive ropw where | RISCV_ADDW | RISCV_SUBW | RISCV_SLLW | RISCV_SRLW | RISCV_SRAW
  deriving Inhabited, BEq

inductive sop where | RISCV_SLLI | RISCV_SRLI | RISCV_SRAI
  deriving Inhabited, BEq

inductive sopw where | RISCV_SLLIW | RISCV_SRLIW | RISCV_SRAIW
  deriving Inhabited, BEq

inductive word_width where | BYTE | HALF | WORD | DOUBLE
  deriving Inhabited, BEq

inductive uop where | RISCV_LUI | RISCV_AUIPC
  deriving Inhabited, BEq

inductive vext2funct6 where | VEXT2_ZVF2 | VEXT2_SVF2
  deriving Inhabited, BEq

inductive vext4funct6 where | VEXT4_ZVF4 | VEXT4_SVF4
  deriving Inhabited, BEq

inductive vext8funct6 where | VEXT8_ZVF8 | VEXT8_SVF8
  deriving Inhabited, BEq

inductive vfnunary0 where | FNV_CVT_XU_F | FNV_CVT_X_F | FNV_CVT_F_XU | FNV_CVT_F_X | FNV_CVT_F_F | FNV_CVT_ROD_F_F | FNV_CVT_RTZ_XU_F | FNV_CVT_RTZ_X_F
  deriving Inhabited, BEq

inductive vfunary0 where | FV_CVT_XU_F | FV_CVT_X_F | FV_CVT_F_XU | FV_CVT_F_X | FV_CVT_RTZ_XU_F | FV_CVT_RTZ_X_F
  deriving Inhabited, BEq

inductive vfunary1 where | FVV_VSQRT | FVV_VRSQRT7 | FVV_VREC7 | FVV_VCLASS
  deriving Inhabited, BEq

inductive vfwunary0 where | FWV_CVT_XU_F | FWV_CVT_X_F | FWV_CVT_F_XU | FWV_CVT_F_X | FWV_CVT_F_F | FWV_CVT_RTZ_XU_F | FWV_CVT_RTZ_X_F
  deriving Inhabited, BEq

inductive vicmpfunct6 where | VICMP_VMSEQ | VICMP_VMSNE | VICMP_VMSLEU | VICMP_VMSLE | VICMP_VMSGTU | VICMP_VMSGT
  deriving Inhabited, BEq

inductive vimcfunct6 where | VIMC_VMADC
  deriving Inhabited, BEq

inductive vimsfunct6 where | VIMS_VADC
  deriving Inhabited, BEq

inductive vimfunct6 where | VIM_VMADC
  deriving Inhabited, BEq

inductive visgfunct6 where | VI_VSLIDEUP | VI_VSLIDEDOWN | VI_VRGATHER
  deriving Inhabited, BEq

inductive vifunct6 where | VI_VADD | VI_VRSUB | VI_VAND | VI_VOR | VI_VXOR | VI_VSADDU | VI_VSADD | VI_VSLL | VI_VSRL | VI_VSRA | VI_VSSRL | VI_VSSRA
  deriving Inhabited, BEq

inductive vlewidth where | VLE8 | VLE16 | VLE32 | VLE64
  deriving Inhabited, BEq

inductive vmlsop where | VLM | VSM
  deriving Inhabited, BEq

inductive vregidx where
  | Vregidx (_ : (BitVec 5))
  deriving Inhabited, BEq

inductive zvkfunct6 where | ZVK_VSHA2CH | ZVK_VSHA2CL
  deriving Inhabited, BEq

inductive vvcmpfunct6 where | VVCMP_VMSEQ | VVCMP_VMSNE | VVCMP_VMSLTU | VVCMP_VMSLT | VVCMP_VMSLEU | VVCMP_VMSLE
  deriving Inhabited, BEq

inductive vvmcfunct6 where | VVMC_VMADC | VVMC_VMSBC
  deriving Inhabited, BEq

inductive vvmsfunct6 where | VVMS_VADC | VVMS_VSBC
  deriving Inhabited, BEq

inductive vvmfunct6 where | VVM_VMADC | VVM_VMSBC
  deriving Inhabited, BEq

inductive vvfunct6 where | VV_VADD | VV_VSUB | VV_VMINU | VV_VMIN | VV_VMAXU | VV_VMAX | VV_VAND | VV_VOR | VV_VXOR | VV_VRGATHER | VV_VRGATHEREI16 | VV_VSADDU | VV_VSADD | VV_VSSUBU | VV_VSSUB | VV_VSLL | VV_VSMUL | VV_VSRL | VV_VSRA | VV_VSSRL | VV_VSSRA
  deriving Inhabited, BEq

inductive vxcmpfunct6 where | VXCMP_VMSEQ | VXCMP_VMSNE | VXCMP_VMSLTU | VXCMP_VMSLT | VXCMP_VMSLEU | VXCMP_VMSLE | VXCMP_VMSGTU | VXCMP_VMSGT
  deriving Inhabited, BEq

inductive vxmcfunct6 where | VXMC_VMADC | VXMC_VMSBC
  deriving Inhabited, BEq

inductive vxmsfunct6 where | VXMS_VADC | VXMS_VSBC
  deriving Inhabited, BEq

inductive vxmfunct6 where | VXM_VMADC | VXM_VMSBC
  deriving Inhabited, BEq

inductive vxsgfunct6 where | VX_VSLIDEUP | VX_VSLIDEDOWN | VX_VRGATHER
  deriving Inhabited, BEq

inductive vxfunct6 where | VX_VADD | VX_VSUB | VX_VRSUB | VX_VMINU | VX_VMIN | VX_VMAXU | VX_VMAX | VX_VAND | VX_VOR | VX_VXOR | VX_VSADDU | VX_VSADD | VX_VSSUBU | VX_VSSUB | VX_VSLL | VX_VSMUL | VX_VSRL | VX_VSRA | VX_VSSRL | VX_VSSRA
  deriving Inhabited, BEq

inductive wmvvfunct6 where | WMVV_VWMACCU | WMVV_VWMACC | WMVV_VWMACCSU
  deriving Inhabited, BEq

inductive wmvxfunct6 where | WMVX_VWMACCU | WMVX_VWMACC | WMVX_VWMACCUS | WMVX_VWMACCSU
  deriving Inhabited, BEq

inductive wvfunct6 where | WV_VADD | WV_VSUB | WV_VADDU | WV_VSUBU
  deriving Inhabited, BEq

inductive wvvfunct6 where | WVV_VADD | WVV_VSUB | WVV_VADDU | WVV_VSUBU | WVV_VWMUL | WVV_VWMULU | WVV_VWMULSU
  deriving Inhabited, BEq

inductive wvxfunct6 where | WVX_VADD | WVX_VSUB | WVX_VADDU | WVX_VSUBU | WVX_VWMUL | WVX_VWMULU | WVX_VWMULSU
  deriving Inhabited, BEq

inductive wxfunct6 where | WX_VADD | WX_VSUB | WX_VADDU | WX_VSUBU
  deriving Inhabited, BEq

inductive brop_zba where | RISCV_SH1ADD | RISCV_SH2ADD | RISCV_SH3ADD
  deriving Inhabited, BEq

inductive bropw_zba where | RISCV_ADDUW | RISCV_SH1ADDUW | RISCV_SH2ADDUW | RISCV_SH3ADDUW
  deriving Inhabited, BEq

inductive extop_zbb where | RISCV_SEXTB | RISCV_SEXTH | RISCV_ZEXTH
  deriving Inhabited, BEq

inductive brop_zbb where | RISCV_ANDN | RISCV_ORN | RISCV_XNOR | RISCV_MAX | RISCV_MAXU | RISCV_MIN | RISCV_MINU | RISCV_ROL | RISCV_ROR
  deriving Inhabited, BEq

inductive bropw_zbb where | RISCV_ROLW | RISCV_RORW
  deriving Inhabited, BEq

inductive brop_zbkb where | RISCV_PACK | RISCV_PACKH
  deriving Inhabited, BEq

inductive biop_zbs where | RISCV_BCLRI | RISCV_BEXTI | RISCV_BINVI | RISCV_BSETI
  deriving Inhabited, BEq

inductive brop_zbs where | RISCV_BCLR | RISCV_BEXT | RISCV_BINV | RISCV_BSET
  deriving Inhabited, BEq

inductive zicondop where | RISCV_CZERO_EQZ | RISCV_CZERO_NEZ
  deriving Inhabited, BEq

inductive f_un_rm_ff_op_S where | FSQRT_S
  deriving Inhabited, BEq

inductive ast where
  | ILLEGAL (_ : word)
  | C_ILLEGAL (_ : half)
  | UTYPE (_ : ((BitVec 20) × regidx × uop))
  | RISCV_JAL (_ : ((BitVec 21) × regidx))
  | RISCV_JALR (_ : ((BitVec 12) × regidx × regidx))
  | BTYPE (_ : ((BitVec 13) × regidx × regidx × bop))
  | ITYPE (_ : ((BitVec 12) × regidx × regidx × iop))
  | SHIFTIOP (_ : ((BitVec 6) × regidx × regidx × sop))
  | RTYPE (_ : (regidx × regidx × regidx × rop))
  | LOAD (_ : ((BitVec 12) × regidx × regidx × Bool × word_width × Bool × Bool))
  | STORE (_ : ((BitVec 12) × regidx × regidx × word_width × Bool × Bool))
  | ADDIW (_ : ((BitVec 12) × regidx × regidx))
  | RTYPEW (_ : (regidx × regidx × regidx × ropw))
  | SHIFTIWOP (_ : ((BitVec 5) × regidx × regidx × sopw))
  | FENCE (_ : ((BitVec 4) × (BitVec 4)))
  | FENCE_TSO (_ : ((BitVec 4) × (BitVec 4)))
  | ECALL (_ : Unit)
  | MRET (_ : Unit)
  | SRET (_ : Unit)
  | EBREAK (_ : Unit)
  | WFI (_ : Unit)
  | SFENCE_VMA (_ : (regidx × regidx))
  | FENCEI (_ : Unit)
  | LOADRES (_ : (Bool × Bool × regidx × word_width × regidx))
  | STORECON (_ : (Bool × Bool × regidx × regidx × word_width × regidx))
  | AMO (_ : (amoop × Bool × Bool × regidx × regidx × word_width × regidx))
  | C_NOP (_ : Unit)
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
  | MUL (_ : (regidx × regidx × regidx × mul_op))
  | DIV (_ : (regidx × regidx × regidx × Bool))
  | REM (_ : (regidx × regidx × regidx × Bool))
  | MULW (_ : (regidx × regidx × regidx))
  | DIVW (_ : (regidx × regidx × regidx × Bool))
  | REMW (_ : (regidx × regidx × regidx × Bool))
  | CSRReg (_ : (csreg × regidx × regidx × csrop))
  | CSRImm (_ : (csreg × (BitVec 5) × regidx × csrop))
  | C_NOP_HINT (_ : (BitVec 6))
  | C_ADDI_HINT (_ : regidx)
  | C_LI_HINT (_ : (BitVec 6))
  | C_LUI_HINT (_ : (BitVec 6))
  | C_MV_HINT (_ : regidx)
  | C_ADD_HINT (_ : regidx)
  | C_SLLI_HINT (_ : ((BitVec 6) × regidx))
  | C_SRLI_HINT (_ : cregidx)
  | C_SRAI_HINT (_ : cregidx)
  | FENCE_RESERVED (_ : ((BitVec 4) × (BitVec 4) × (BitVec 4) × regidx × regidx))
  | FENCEI_RESERVED (_ : ((BitVec 12) × regidx × regidx))
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
  | C_FLW (_ : ((BitVec 5) × cregidx × cregidx))
  | C_FSW (_ : ((BitVec 5) × cregidx × cregidx))
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
  | C_FLD (_ : ((BitVec 5) × cregidx × cregidx))
  | C_FSD (_ : ((BitVec 5) × cregidx × cregidx))
  | SINVAL_VMA (_ : (regidx × regidx))
  | SFENCE_W_INVAL (_ : Unit)
  | SFENCE_INVAL_IR (_ : Unit)
  | RISCV_SLLIUW (_ : ((BitVec 6) × regidx × regidx))
  | ZBA_RTYPEUW (_ : (regidx × regidx × regidx × bropw_zba))
  | ZBA_RTYPE (_ : (regidx × regidx × regidx × brop_zba))
  | RISCV_RORIW (_ : ((BitVec 5) × regidx × regidx))
  | RISCV_RORI (_ : ((BitVec 6) × regidx × regidx))
  | ZBB_RTYPEW (_ : (regidx × regidx × regidx × bropw_zbb))
  | ZBB_RTYPE (_ : (regidx × regidx × regidx × brop_zbb))
  | ZBB_EXTOP (_ : (regidx × regidx × extop_zbb))
  | RISCV_REV8 (_ : (regidx × regidx))
  | RISCV_ORCB (_ : (regidx × regidx))
  | RISCV_CPOP (_ : (regidx × regidx))
  | RISCV_CPOPW (_ : (regidx × regidx))
  | RISCV_CLZ (_ : (regidx × regidx))
  | RISCV_CLZW (_ : (regidx × regidx))
  | RISCV_CTZ (_ : (regidx × regidx))
  | RISCV_CTZW (_ : (regidx × regidx))
  | RISCV_CLMUL (_ : (regidx × regidx × regidx))
  | RISCV_CLMULH (_ : (regidx × regidx × regidx))
  | RISCV_CLMULR (_ : (regidx × regidx × regidx))
  | ZBS_IOP (_ : ((BitVec 6) × regidx × regidx × biop_zbs))
  | ZBS_RTYPE (_ : (regidx × regidx × regidx × brop_zbs))
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
  | F_BIN_RM_TYPE_H (_ : (fregidx × fregidx × rounding_mode × fregidx × f_bin_rm_op_H))
  | F_MADD_TYPE_H (_ : (fregidx × fregidx × fregidx × rounding_mode × fregidx × f_madd_op_H))
  | F_BIN_F_TYPE_H (_ : (fregidx × fregidx × fregidx × f_bin_f_op_H))
  | F_BIN_X_TYPE_H (_ : (fregidx × fregidx × regidx × f_bin_x_op_H))
  | F_UN_RM_FF_TYPE_H (_ : (fregidx × rounding_mode × fregidx × f_un_rm_ff_op_H))
  | F_UN_RM_FX_TYPE_H (_ : (fregidx × rounding_mode × regidx × f_un_rm_fx_op_H))
  | F_UN_RM_XF_TYPE_H (_ : (regidx × rounding_mode × fregidx × f_un_rm_xf_op_H))
  | F_UN_F_TYPE_H (_ : (regidx × fregidx × f_un_f_op_H))
  | F_UN_X_TYPE_H (_ : (fregidx × regidx × f_un_x_op_H))
  | RISCV_FLI_H (_ : ((BitVec 5) × fregidx))
  | RISCV_FLI_S (_ : ((BitVec 5) × fregidx))
  | RISCV_FLI_D (_ : ((BitVec 5) × fregidx))
  | RISCV_FMINM_H (_ : (fregidx × fregidx × fregidx))
  | RISCV_FMAXM_H (_ : (fregidx × fregidx × fregidx))
  | RISCV_FMINM_S (_ : (fregidx × fregidx × fregidx))
  | RISCV_FMAXM_S (_ : (fregidx × fregidx × fregidx))
  | RISCV_FMINM_D (_ : (fregidx × fregidx × fregidx))
  | RISCV_FMAXM_D (_ : (fregidx × fregidx × fregidx))
  | RISCV_FROUND_H (_ : (fregidx × rounding_mode × fregidx))
  | RISCV_FROUNDNX_H (_ : (fregidx × rounding_mode × fregidx))
  | RISCV_FROUND_S (_ : (fregidx × rounding_mode × fregidx))
  | RISCV_FROUNDNX_S (_ : (fregidx × rounding_mode × fregidx))
  | RISCV_FROUND_D (_ : (fregidx × rounding_mode × fregidx))
  | RISCV_FROUNDNX_D (_ : (fregidx × rounding_mode × fregidx))
  | RISCV_FMVH_X_D (_ : (fregidx × regidx))
  | RISCV_FMVP_D_X (_ : (regidx × regidx × fregidx))
  | RISCV_FLEQ_H (_ : (fregidx × fregidx × regidx))
  | RISCV_FLTQ_H (_ : (fregidx × fregidx × regidx))
  | RISCV_FLEQ_S (_ : (fregidx × fregidx × regidx))
  | RISCV_FLTQ_S (_ : (fregidx × fregidx × regidx))
  | RISCV_FLEQ_D (_ : (fregidx × fregidx × regidx))
  | RISCV_FLTQ_D (_ : (fregidx × fregidx × regidx))
  | RISCV_FCVTMOD_W_D (_ : (fregidx × regidx))
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
  | RISCV_ZIP (_ : (regidx × regidx))
  | RISCV_UNZIP (_ : (regidx × regidx))
  | RISCV_BREV8 (_ : (regidx × regidx))
  | RISCV_XPERM8 (_ : (regidx × regidx × regidx))
  | RISCV_XPERM4 (_ : (regidx × regidx × regidx))
  | ZICOND_RTYPE (_ : (regidx × regidx × regidx × zicondop))
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
  | VMVRTYPE (_ : (vregidx × (BitVec 5) × vregidx))
  | MVVTYPE (_ : (mvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | MVVMATYPE (_ : (mvvmafunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | WVVTYPE (_ : (wvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | WVTYPE (_ : (wvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | WMVVTYPE (_ : (wmvvfunct6 × (BitVec 1) × vregidx × vregidx × vregidx))
  | VEXT2TYPE (_ : (vext2funct6 × (BitVec 1) × vregidx × vregidx))
  | VEXT4TYPE (_ : (vext4funct6 × (BitVec 1) × vregidx × vregidx))
  | VEXT8TYPE (_ : (vext8funct6 × (BitVec 1) × vregidx × vregidx))
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
  | VLSEGTYPE (_ : ((BitVec 3) × (BitVec 1) × regidx × vlewidth × vregidx))
  | VLSEGFFTYPE (_ : ((BitVec 3) × (BitVec 1) × regidx × vlewidth × vregidx))
  | VSSEGTYPE (_ : ((BitVec 3) × (BitVec 1) × regidx × vlewidth × vregidx))
  | VLSSEGTYPE (_ : ((BitVec 3) × (BitVec 1) × regidx × regidx × vlewidth × vregidx))
  | VSSSEGTYPE (_ : ((BitVec 3) × (BitVec 1) × regidx × regidx × vlewidth × vregidx))
  | VLUXSEGTYPE (_ : ((BitVec 3) × (BitVec 1) × vregidx × regidx × vlewidth × vregidx))
  | VLOXSEGTYPE (_ : ((BitVec 3) × (BitVec 1) × vregidx × regidx × vlewidth × vregidx))
  | VSUXSEGTYPE (_ : ((BitVec 3) × (BitVec 1) × vregidx × regidx × vlewidth × vregidx))
  | VSOXSEGTYPE (_ : ((BitVec 3) × (BitVec 1) × vregidx × regidx × vlewidth × vregidx))
  | VLRETYPE (_ : ((BitVec 3) × regidx × vlewidth × vregidx))
  | VSRETYPE (_ : ((BitVec 3) × regidx × vregidx))
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
  | RISCV_ZICBOM (_ : (cbop_zicbom × regidx))
  | RISCV_ZICBOZ (_ : regidx)
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
  | VROR_VI (_ : ((BitVec 1) × vregidx × (BitVec 5) × vregidx))
  | VWSLL_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VWSLL_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VWSLL_VI (_ : ((BitVec 1) × vregidx × (BitVec 5) × vregidx))
  | VCLMUL_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VCLMUL_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VCLMULH_VV (_ : ((BitVec 1) × vregidx × vregidx × vregidx))
  | VCLMULH_VX (_ : ((BitVec 1) × vregidx × regidx × vregidx))
  | VSHA2MS_VV (_ : (vregidx × vregidx × vregidx))
  | ZVKSHA2TYPE (_ : (zvkfunct6 × vregidx × vregidx × vregidx))
  | ZIMOP_MOP_R (_ : ((BitVec 5) × regidx × regidx))
  | ZIMOP_MOP_RR (_ : ((BitVec 3) × regidx × regidx × regidx))
  | ZCMOP (_ : (BitVec 3))
  -- deriving Inhabited, BEq
  deriving Inhabited

inductive PTW_Error where
  | PTW_Invalid_Addr (_ : Unit)
  | PTW_Access (_ : Unit)
  | PTW_Invalid_PTE (_ : Unit)
  | PTW_No_Permission (_ : Unit)
  | PTW_Misaligned (_ : Unit)
  | PTW_PTE_Update (_ : Unit)
  | PTW_Ext_Error (_ : ext_ptw_error)
  deriving Inhabited, BEq

/-- Type quantifiers: k_a : Type -/
inductive ExecutionResult (k_a : Type) where
  | RETIRE_OK (_ : Unit)
  | RETIRE_FAIL (_ : k_a)
  deriving Inhabited, BEq

inductive InterruptType where | I_U_Software | I_S_Software | I_M_Software | I_U_Timer | I_S_Timer | I_M_Timer | I_U_External | I_S_External | I_M_External
  deriving Inhabited, BEq

abbrev tv_mode := (BitVec 2)

inductive TrapVectorMode where | TV_Direct | TV_Vector | TV_Reserved
  deriving Inhabited, BEq

abbrev ext_status := (BitVec 2)

inductive ExtStatus where | Off | Initial | Clean | Dirty
  deriving Inhabited, BEq

abbrev satp_mode := (BitVec 4)

inductive SATPMode where | Bare | Sv32 | Sv39 | Sv48 | Sv57
  deriving Inhabited, BEq

abbrev csrRW := (BitVec 2)



abbrev level_range (k_v : Nat) := Nat

abbrev pte_bits k_v := (BitVec (bif k_v = 32 then 32 else 64))

abbrev ppn_bits k_v := (BitVec (bif k_v = 32 then 22 else 44))

abbrev vpn_bits k_v := (BitVec (k_v - 12))

abbrev ext_access_type := Unit

abbrev regtype := xlenbits

abbrev fregtype := flenbits

abbrev Misa := (BitVec (2 ^ 3 * 8))

abbrev Mstatus := (BitVec 64)

abbrev MEnvcfg := (BitVec 64)

abbrev SEnvcfg := (BitVec (2 ^ 3 * 8))

abbrev Minterrupts := (BitVec (2 ^ 3 * 8))

abbrev Medeleg := (BitVec 64)

abbrev Mtvec := (BitVec (2 ^ 3 * 8))

abbrev Mcause := (BitVec (2 ^ 3 * 8))

abbrev Counteren := (BitVec 32)

abbrev Counterin := (BitVec 32)

abbrev Sstatus := (BitVec 64)

abbrev Sinterrupts := (BitVec (2 ^ 3 * 8))

abbrev Satp64 := (BitVec 64)

abbrev Satp32 := (BitVec 32)

abbrev Vtype := (BitVec (2 ^ 3 * 8))

inductive agtype where | UNDISTURBED | AGNOSTIC
  deriving Inhabited, BEq

inductive PmpAddrMatchType where | OFF | TOR | NA4 | NAPOT
  deriving Inhabited, BEq

abbrev Pmpcfg_ent := (BitVec 8)

inductive pmpAddrMatch where | PMP_NoMatch | PMP_PartialMatch | PMP_Match
  deriving Inhabited, BEq

inductive pmpMatch where | PMP_Success | PMP_Continue | PMP_Fail
  deriving Inhabited, BEq

/-- Type quantifiers: k_a : Type -/
inductive Ext_FetchAddr_Check (k_a : Type) where
  | Ext_FetchAddr_OK (_ : virtaddr)
  | Ext_FetchAddr_Error (_ : k_a)
  deriving Inhabited, BEq

/-- Type quantifiers: k_a : Type -/
inductive Ext_ControlAddr_Check (k_a : Type) where
  | Ext_ControlAddr_OK (_ : virtaddr)
  | Ext_ControlAddr_Error (_ : k_a)
  deriving Inhabited, BEq

/-- Type quantifiers: k_a : Type -/
inductive Ext_DataAddr_Check (k_a : Type) where
  | Ext_DataAddr_OK (_ : virtaddr)
  | Ext_DataAddr_Error (_ : k_a)
  deriving Inhabited, BEq

inductive Ext_PhysAddr_Check where
  | Ext_PhysAddr_OK (_ : Unit)
  | Ext_PhysAddr_Error (_ : ExceptionType)
  deriving Inhabited, BEq

abbrev ext_fetch_addr_error := Unit

abbrev ext_control_addr_error := Unit

abbrev ext_data_addr_error := Unit

abbrev vreglenbits := (BitVec 65536)

abbrev vregtype := vreglenbits

inductive maskfunct3 where | VV_VMERGE | VI_VMERGE | VX_VMERGE
  deriving Inhabited, BEq

inductive vregno where
  | Vregno (_ : Nat)
  deriving Inhabited, BEq

abbrev Vcsr := (BitVec 3)

abbrev ext_exception := Unit

structure sync_exception where
  trap : ExceptionType
  excinfo : (Option xlenbits)
  ext : (Option ext_exception)
  deriving Inhabited, BEq

abbrev HpmEvent := (BitVec 64)

abbrev hpmidx := Nat

inductive seed_opst where | BIST | ES16 | WAIT | DEAD
  deriving Inhabited, BEq

abbrev bits_rm := (BitVec 3)

abbrev bits_fflags := (BitVec 5)

abbrev bits_H := (BitVec 16)

abbrev bits_S := (BitVec 32)

abbrev bits_D := (BitVec 64)

abbrev bits_W := (BitVec 32)

abbrev bits_WU := (BitVec 32)

abbrev bits_L := (BitVec 64)

abbrev bits_LU := (BitVec 64)

inductive fregno where
  | Fregno (_ : Nat)
  deriving Inhabited, BEq

abbrev Fcsr := (BitVec 32)

abbrev CountSmcntrpmf := (BitVec 64)

inductive ctl_result where
  | CTL_TRAP (_ : sync_exception)
  | CTL_SRET (_ : Unit)
  | CTL_MRET (_ : Unit)
  deriving Inhabited, BEq

inductive Result (α : Type) (β : Type) where
  | Ok (_ : α)
  | Err (_ : β)
  deriving Repr
export Result(Ok Err)

abbrev MemoryOpResult k_a := (Result k_a ExceptionType)

abbrev htif_cmd := (BitVec 64)

abbrev pte_flags_bits := (BitVec 8)

abbrev pte_ext_bits := (BitVec 10)

abbrev PTE_Ext := (BitVec 10)

abbrev PTE_Flags := (BitVec 8)

inductive PTE_Check where
  | PTE_Check_Success (_ : ext_ptw)
  | PTE_Check_Failure (_ : (ext_ptw × ext_ptw_fail))
  deriving Inhabited, BEq

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
  deriving Inhabited, BEq

abbrev num_tlb_entries : Int := 64

abbrev tlb_index_range := Nat

/-- Type quantifiers: k_v : Int, is_sv_mode(k_v) -/
structure PTW_Output (k_v : Nat) where
  ppn : (ppn_bits k_v)
  pte : (pte_bits k_v)
  pteAddr : physaddr
  level : (level_range k_v)
  global : Bool
  deriving Inhabited, BEq

/-- Type quantifiers: k_v : Int, is_sv_mode(k_v) -/
inductive PTW_Result (k_v : Nat) where
  | PTW_Success (_ : ((PTW_Output k_v) × ext_ptw))
  | PTW_Failure (_ : (PTW_Error × ext_ptw))
  deriving Inhabited, BEq

/-- Type quantifiers: k_paddr : Type, k_failure : Type -/
inductive TR_Result (k_paddr : Type) (k_failure : Type) where
  | TR_Address (_ : (k_paddr × ext_ptw))
  | TR_Failure (_ : (k_failure × ext_ptw))
  deriving Inhabited, BEq

inductive Retire_Failure where
  | Illegal_Instruction (_ : Unit)
  | Wait_For_Interrupt (_ : Unit)
  | Trap (_ : (Privilege × ctl_result × xlenbits))
  | Memory_Exception (_ : (virtaddr × ExceptionType))
  | Ext_CSR_Check_Failure (_ : Unit)
  | Ext_ControlAddr_Check_Failure (_ : ext_control_addr_error)
  | Ext_DataAddr_Check_Failure (_ : ext_data_addr_error)
  | Ext_XRET_Priv_Failure (_ : Unit)
  deriving Inhabited, BEq





abbrev nfields := Int

inductive cbie where | CBIE_ILLEGAL | CBIE_EXEC_FLUSH | CBIE_EXEC_INVAL
  deriving Inhabited, BEq

inductive checked_cbop where | CBOP_ILLEGAL | CBOP_ILLEGAL_VIRTUAL | CBOP_INVAL_FLUSH | CBOP_INVAL_INVAL
  deriving Inhabited, BEq

abbrev instbits := xlenbits

inductive HartState where
  | HART_ACTIVE (_ : Unit)
  | HART_WAITING (_ : instbits)
  deriving Inhabited, BEq

inductive FetchResult where
  | F_Ext_Error (_ : ext_fetch_addr_error)
  | F_Base (_ : word)
  | F_RVC (_ : half)
  | F_Error (_ : (ExceptionType × xlenbits))
  deriving Inhabited, BEq

inductive Step where
  | Step_Pending_Interrupt (_ : (InterruptType × Privilege))
  | Step_Ext_Fetch_Failure (_ : ext_fetch_addr_error)
  | Step_Fetch_Failure (_ : (virtaddr × ExceptionType))
  | Step_Execute (_ : ((ExecutionResult Retire_Failure) × instbits))
  | Step_Waiting (_ : Unit)
  deriving Inhabited, BEq

inductive Register : Type where
  | hart_state
  | satp
  | tlb
  | htif_payload_writes
  | htif_cmd_write
  | htif_exit_code
  | htif_done
  | htif_tohost
  | stimecmp
  | mtimecmp
  | minstretcfg
  | mcyclecfg
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
  | float_fflags
  | float_result
  | mhpmcounter
  | mhpmevent
  | vcsr
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
  | pmpaddr_n
  | pmpcfg_n
  | vtype
  | vl
  | vstart
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
  | mstatus
  | misa
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
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .hart_state => HartState
  | .satp => (BitVec (2 ^ 3 * 8))
  | .tlb => (Vector (Option TLB_Entry) 64)
  | .htif_payload_writes => (BitVec 4)
  | .htif_cmd_write => (BitVec 1)
  | .htif_exit_code => (BitVec 64)
  | .htif_done => Bool
  | .htif_tohost => (BitVec 64)
  | .stimecmp => (BitVec 64)
  | .mtimecmp => (BitVec 64)
  | .minstretcfg => (BitVec 64)
  | .mcyclecfg => (BitVec 64)
  | .fcsr => (BitVec 32)
  | .f31 => (BitVec (8 * 8))
  | .f30 => (BitVec (8 * 8))
  | .f29 => (BitVec (8 * 8))
  | .f28 => (BitVec (8 * 8))
  | .f27 => (BitVec (8 * 8))
  | .f26 => (BitVec (8 * 8))
  | .f25 => (BitVec (8 * 8))
  | .f24 => (BitVec (8 * 8))
  | .f23 => (BitVec (8 * 8))
  | .f22 => (BitVec (8 * 8))
  | .f21 => (BitVec (8 * 8))
  | .f20 => (BitVec (8 * 8))
  | .f19 => (BitVec (8 * 8))
  | .f18 => (BitVec (8 * 8))
  | .f17 => (BitVec (8 * 8))
  | .f16 => (BitVec (8 * 8))
  | .f15 => (BitVec (8 * 8))
  | .f14 => (BitVec (8 * 8))
  | .f13 => (BitVec (8 * 8))
  | .f12 => (BitVec (8 * 8))
  | .f11 => (BitVec (8 * 8))
  | .f10 => (BitVec (8 * 8))
  | .f9 => (BitVec (8 * 8))
  | .f8 => (BitVec (8 * 8))
  | .f7 => (BitVec (8 * 8))
  | .f6 => (BitVec (8 * 8))
  | .f5 => (BitVec (8 * 8))
  | .f4 => (BitVec (8 * 8))
  | .f3 => (BitVec (8 * 8))
  | .f2 => (BitVec (8 * 8))
  | .f1 => (BitVec (8 * 8))
  | .f0 => (BitVec (8 * 8))
  | .float_fflags => (BitVec 64)
  | .float_result => (BitVec 64)
  | .mhpmcounter => (Vector (BitVec 64) 32)
  | .mhpmevent => (Vector (BitVec 64) 32)
  | .vcsr => (BitVec 3)
  | .vr31 => (BitVec 65536)
  | .vr30 => (BitVec 65536)
  | .vr29 => (BitVec 65536)
  | .vr28 => (BitVec 65536)
  | .vr27 => (BitVec 65536)
  | .vr26 => (BitVec 65536)
  | .vr25 => (BitVec 65536)
  | .vr24 => (BitVec 65536)
  | .vr23 => (BitVec 65536)
  | .vr22 => (BitVec 65536)
  | .vr21 => (BitVec 65536)
  | .vr20 => (BitVec 65536)
  | .vr19 => (BitVec 65536)
  | .vr18 => (BitVec 65536)
  | .vr17 => (BitVec 65536)
  | .vr16 => (BitVec 65536)
  | .vr15 => (BitVec 65536)
  | .vr14 => (BitVec 65536)
  | .vr13 => (BitVec 65536)
  | .vr12 => (BitVec 65536)
  | .vr11 => (BitVec 65536)
  | .vr10 => (BitVec 65536)
  | .vr9 => (BitVec 65536)
  | .vr8 => (BitVec 65536)
  | .vr7 => (BitVec 65536)
  | .vr6 => (BitVec 65536)
  | .vr5 => (BitVec 65536)
  | .vr4 => (BitVec 65536)
  | .vr3 => (BitVec 65536)
  | .vr2 => (BitVec 65536)
  | .vr1 => (BitVec 65536)
  | .vr0 => (BitVec 65536)
  | .pmpaddr_n => (Vector (BitVec (2 ^ 3 * 8)) 64)
  | .pmpcfg_n => (Vector (BitVec 8) 64)
  | .vtype => (BitVec (2 ^ 3 * 8))
  | .vl => (BitVec (2 ^ 3 * 8))
  | .vstart => (BitVec 16)
  | .tselect => (BitVec (2 ^ 3 * 8))
  | .stval => (BitVec (2 ^ 3 * 8))
  | .scause => (BitVec (2 ^ 3 * 8))
  | .sepc => (BitVec (2 ^ 3 * 8))
  | .sscratch => (BitVec (2 ^ 3 * 8))
  | .stvec => (BitVec (2 ^ 3 * 8))
  | .mconfigptr => (BitVec (2 ^ 3 * 8))
  | .mhartid => (BitVec (2 ^ 3 * 8))
  | .marchid => (BitVec (2 ^ 3 * 8))
  | .mimpid => (BitVec (2 ^ 3 * 8))
  | .mvendorid => (BitVec 32)
  | .minstret_increment => Bool
  | .minstret => (BitVec 64)
  | .mtime => (BitVec 64)
  | .mcycle => (BitVec 64)
  | .mcountinhibit => (BitVec 32)
  | .mcounteren => (BitVec 32)
  | .scounteren => (BitVec 32)
  | .mscratch => (BitVec (2 ^ 3 * 8))
  | .mtval => (BitVec (2 ^ 3 * 8))
  | .mepc => (BitVec (2 ^ 3 * 8))
  | .mcause => (BitVec (2 ^ 3 * 8))
  | .mtvec => (BitVec (2 ^ 3 * 8))
  | .mideleg => (BitVec (2 ^ 3 * 8))
  | .medeleg => (BitVec 64)
  | .mip => (BitVec (2 ^ 3 * 8))
  | .mie => (BitVec (2 ^ 3 * 8))
  | .senvcfg => (BitVec (2 ^ 3 * 8))
  | .menvcfg => (BitVec 64)
  | .mstatus => (BitVec 64)
  | .misa => (BitVec (2 ^ 3 * 8))
  | .cur_inst => (BitVec (2 ^ 3 * 8))
  | .cur_privilege => Privilege
  | .x31 => (BitVec (2 ^ 3 * 8))
  | .x30 => (BitVec (2 ^ 3 * 8))
  | .x29 => (BitVec (2 ^ 3 * 8))
  | .x28 => (BitVec (2 ^ 3 * 8))
  | .x27 => (BitVec (2 ^ 3 * 8))
  | .x26 => (BitVec (2 ^ 3 * 8))
  | .x25 => (BitVec (2 ^ 3 * 8))
  | .x24 => (BitVec (2 ^ 3 * 8))
  | .x23 => (BitVec (2 ^ 3 * 8))
  | .x22 => (BitVec (2 ^ 3 * 8))
  | .x21 => (BitVec (2 ^ 3 * 8))
  | .x20 => (BitVec (2 ^ 3 * 8))
  | .x19 => (BitVec (2 ^ 3 * 8))
  | .x18 => (BitVec (2 ^ 3 * 8))
  | .x17 => (BitVec (2 ^ 3 * 8))
  | .x16 => (BitVec (2 ^ 3 * 8))
  | .x15 => (BitVec (2 ^ 3 * 8))
  | .x14 => (BitVec (2 ^ 3 * 8))
  | .x13 => (BitVec (2 ^ 3 * 8))
  | .x12 => (BitVec (2 ^ 3 * 8))
  | .x11 => (BitVec (2 ^ 3 * 8))
  | .x10 => (BitVec (2 ^ 3 * 8))
  | .x9 => (BitVec (2 ^ 3 * 8))
  | .x8 => (BitVec (2 ^ 3 * 8))
  | .x7 => (BitVec (2 ^ 3 * 8))
  | .x6 => (BitVec (2 ^ 3 * 8))
  | .x5 => (BitVec (2 ^ 3 * 8))
  | .x4 => (BitVec (2 ^ 3 * 8))
  | .x3 => (BitVec (2 ^ 3 * 8))
  | .x2 => (BitVec (2 ^ 3 * 8))
  | .x1 => (BitVec (2 ^ 3 * 8))
  | .nextPC => (BitVec (2 ^ 3 * 8))
  | .PC => (BitVec (2 ^ 3 * 8))
