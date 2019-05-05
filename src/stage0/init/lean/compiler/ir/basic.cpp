// Lean compiler output
// Module: init.lean.compiler.ir.basic
// Imports: init.lean.name init.lean.kvmap init.lean.format init.data.array.default
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l___private_init_lean_compiler_ir_basic_12__collectArgs___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_Arg_hasFreeVar(obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_IR_FnBody_beq___boxed(obj*, obj*);
obj* l_Lean_IR_mkJDecl___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_setBody(obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___boxed(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FreeVariables_insertParams___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_1__skip___rarg___boxed(obj*);
namespace lean {
namespace ir {
obj* mk_sset_core(obj*, obj*, obj*, obj*, uint8, obj*);
}}
obj* l_Lean_IR_FnBody_collectFreeVars(obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_IR_mkVDecl___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_setBody(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_vsetInh;
obj* l_Lean_IR_VarId_Lean_HasFormat(obj*);
obj* l_Lean_IR_Alt_isDefault___boxed(obj*);
obj* l___private_init_lean_compiler_ir_basic_10__collectArg___main(obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_beq(uint8, uint8);
obj* l___private_init_lean_compiler_ir_basic_20__collectArg___main___boxed(obj*, obj*);
uint8 l_Lean_IR_Arg_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___main___rarg___closed__1;
obj* l_Lean_IR_AltCore_mmodifyBody___main(obj*);
namespace lean {
namespace ir {
obj* mk_jdecl_core(obj*, obj*, uint8, obj*, obj*);
}}
namespace lean {
namespace ir {
obj* mk_var_arg_core(obj*);
}}
obj* l_Lean_IR_JoinPointId_HasToString___closed__1;
obj* l_Lean_IR_mmodifyJPs(obj*);
uint8 l_Lean_IR_HasIndex_visitParams(obj*, obj*);
obj* l_Lean_IR_FnBody_isTerminal___boxed(obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Lean_IR_AltCore_mmodifyBody(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Arg_hasFreeVar___boxed(obj*, obj*);
obj* l_Lean_IR_addParamsRename___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2(obj*, obj*, obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_fapp_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_AltCore_modifyBody___main(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_11__collectArray(obj*);
obj* l___private_init_lean_compiler_ir_basic_15__skip___boxed(obj*);
uint8 l_Lean_IR_HasIndex_visitExpr___main(obj*, obj*);
obj* l_Lean_IR_addParamRename(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_23__collectParam(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_FreeVariables_insertParams___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_22__collectArgs(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_19__seq(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_20__collectArg___main(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_alt_core(obj*, obj*, obj*, obj*, obj*, obj*);
}}
obj* l_Lean_IR_modifyJPs(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_15__skip(obj*);
uint8 l_Lean_IR_LitVal_beq___main(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main___boxed(obj*);
obj* l_Lean_IR_mmodifyJPs___boxed(obj*);
obj* l_Lean_IR_mkParam___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_HasBeq;
obj* l___private_init_lean_compiler_ir_basic_1__skip___rarg(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_anyAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(obj*, obj*, obj*);
uint8 l_Lean_IR_VarId_HasBeq(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_body(obj*);
obj* l___private_init_lean_compiler_ir_basic_8__withParams___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_HasIndex_visitArg___main___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_alphaEqv___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_VarId_alphaEqv(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_jmp_core(obj*, obj*);
}}
obj* l_Lean_IR_AltCore_modifyBody(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_JoinPointId_HasBeq___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_nil;
uint8 l_Lean_IR_FnBody_alphaEqv(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_2__collectIndex(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_str_expr_core(obj*);
}}
namespace lean {
namespace ir {
obj* mk_proj_expr_core(obj*, obj*);
}}
obj* l_Array_anyAux___main___at_Lean_IR_HasIndex_visitParams___spec__1___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_CtorInfo_beq(obj*, obj*);
obj* l_Lean_IR_FreeVariables_insertParams(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_20__collectArg___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_6__withVar(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_25__collectExpr(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_17__collectVar(obj*, obj*);
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1___boxed(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_9__seq(obj*, obj*, obj*, obj*);
obj* l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___boxed(obj*);
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Alt_default(obj*);
obj* l___private_init_lean_compiler_ir_basic_16__collect(obj*, obj*);
obj* l_Lean_IR_Decl_maxVar(obj*);
namespace lean {
namespace ir {
obj* mk_num_expr_core(obj*);
}}
obj* l___private_init_lean_compiler_ir_basic_24__collectParams___boxed(obj*, obj*);
uint8 l_Lean_IR_FnBody_isPure(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_VarId_hasAeqv;
obj* l___private_init_lean_compiler_ir_basic_1__skip(obj*);
namespace lean {
namespace ir {
obj* mk_sproj_expr_core(obj*, obj*, obj*);
}}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_LitVal_beq(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_mkSSet___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FreeVariables_collectFnBody(obj*, obj*, obj*);
uint8 l_Lean_IR_Expr_isPure___main(obj*);
obj* l___private_init_lean_compiler_ir_basic_25__collectExpr___main(obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_FnBody_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_MaxVar_collectFnBody(obj*, obj*);
uint8 l_Lean_IR_FnBody_alphaEqv___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_26__collectAlts(obj*, obj*, obj*);
obj* l_Lean_IR_Arg_alphaEqv___boxed(obj*, obj*, obj*);
uint8 l_Array_anyAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_23__collectParam___boxed(obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___main___boxed(obj*);
obj* l_Lean_IR_HasIndex_visitVar___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1(obj*);
obj* l_Lean_IR_FnBody_freeVars(obj*);
obj* l_Lean_IR_MaxVar_collectDecl___main(obj*, obj*);
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(obj*, obj*);
uint8 l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body(obj*);
obj* l_Lean_IR_MaxVar_collectFnBody___main___closed__1;
obj* l_Lean_IR_AltCore_mmodifyBody___rarg(obj*, obj*, obj*);
uint8 l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_flattenAux___main(obj*, obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Lean_IR_JoinPointId_Lean_HasFormat(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(obj*, obj*, obj*, uint8, obj*, obj*);
uint8 l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_26__collectAlts___boxed(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_case_core(obj*, obj*, obj*);
}}
uint8 l_Lean_IR_Expr_hasFreeVar(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_addParamsRename(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_hasFreeVar___boxed(obj*, obj*);
obj* l_Lean_IR_MaxVar_collectDecl(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitArgs(obj*, obj*);
obj* l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_args_hasAeqv;
obj* l_Lean_IR_FreeVariables_collectFnBody___main___closed__1;
obj* l_Lean_IR_FreeVariables_HasAndthen;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_args_alphaEqv___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_HasBeq;
uint8 l_Lean_IR_Expr_alphaEqv(obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_12__collectArgs(obj*, obj*, obj*);
obj* l_Lean_IR_LitVal_beq___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_4__collectJP(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_8__withParams(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_17__collectVar___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__1(obj*, obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_ret_core(obj*);
}}
obj* l_Lean_IR_FnBody_flatten(obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_basic_10__collectArg(obj*, obj*, obj*);
obj* l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1___boxed(obj*, obj*, obj*);
obj* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___boxed(obj*);
namespace lean {
namespace ir {
obj* mk_param_core(obj*, uint8, uint8);
}}
obj* l_Lean_IR_AltCore_body___boxed(obj*);
obj* l_Lean_IR_paramInh;
uint8 l_RBNode_isRed___main___rarg(obj*);
uint8 l_Lean_KVMap_eqv(obj*, obj*);
obj* l_Lean_IR_Expr_hasAeqv;
namespace lean {
namespace ir {
obj* mk_uset_core(obj*, obj*, obj*, obj*);
}}
obj* l_Lean_IR_FnBody_body___boxed(obj*);
obj* l_Lean_IR_IRType_HasBeq;
obj* l_Array_anyAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_altInh;
obj* l_Lean_IR_FreeVariables_insertParams___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_body___main___boxed(obj*);
obj* l_Lean_IR_FnBody_isTerminal___main___boxed(obj*);
obj* l___private_init_lean_compiler_ir_basic_13__collectExpr___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_24__collectParams(obj*, obj*);
uint8 l_Lean_IR_Alt_isDefault___main(obj*);
obj* l_Lean_IR_VarId_HasBeq___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_5__withIndex(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Expr_isPure___boxed(obj*);
obj* l_Array_anyAux___main___at_Lean_IR_FnBody_isPure___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_split(obj*);
obj* l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1___boxed(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___boxed(obj*);
namespace lean {
namespace ir {
obj* mk_irrelevant_arg_core;
}}
obj* l_Lean_IR_Arg_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_LitVal_beq___main___boxed(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_app_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_Expr_isPure___main___boxed(obj*);
obj* l___private_init_lean_compiler_ir_basic_18__collectJP___boxed(obj*, obj*);
obj* l_Lean_IR_VarId_HasToString(obj*);
obj* l_Lean_IR_HasIndex_visitParams___boxed(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_unreachable_core;
}}
obj* l___private_init_lean_compiler_ir_basic_16__collect___boxed(obj*, obj*);
uint8 l_Lean_IR_FnBody_isTerminal(obj*);
obj* l_Lean_IR_addVarRename(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_hasFreeVar___boxed(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_modifyJPs___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitFnBody___main(obj*, obj*);
obj* l_Lean_IR_HasIndex_visitJP___boxed(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitVar(obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___main___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_20__collectArg(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_7__withJP(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_hasFreeVar(obj*, obj*);
obj* l_Lean_IR_HasIndex_visitExpr___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_22__collectArgs___boxed(obj*, obj*);
uint8 l_Lean_IR_FnBody_isPure___main(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_14__collectAlts(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__1(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___boxed(obj*);
uint8 l_Lean_IR_Arg_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_VarId_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_VarId_lt___boxed(obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitFnBody(obj*, obj*);
obj* l_Lean_IR_mkDecl___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_maxVar(obj*);
uint8 l_Lean_IR_CtorInfo_beq___main(obj*, obj*);
uint8 l_Lean_IR_FnBody_beq(obj*, obj*);
obj* l_Lean_IR_HasIndex_visitArgs___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_14__collectAlts___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_args_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_beq___main___boxed(obj*, obj*);
uint8 l_Lean_IR_Expr_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_VarId_HasToString___closed__1;
uint8 l_Lean_IR_Expr_isPure(obj*);
namespace lean {
namespace ir {
obj* mk_decl_core(obj*, obj*, uint8, obj*);
}}
uint8 l_Lean_IR_HasIndex_visitExpr(obj*, obj*);
uint8 l_Lean_IR_JoinPointId_HasBeq(obj*, obj*);
uint8 l_Lean_IR_VarId_lt(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_uproj_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_flattenAux(obj*, obj*);
obj* l_Lean_IR_Arg_hasAeqv;
obj* l_Lean_IR_FnBody_isPure___boxed(obj*);
obj* l_Lean_IR_Alt_ctor(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___rarg(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___boxed(obj*);
obj* l_Lean_IR_MData_HasEmptyc;
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_isEqvAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_1__skip___boxed(obj*);
obj* l_Lean_IR_HasIndex_visitFnBody___main___boxed(obj*, obj*);
obj* l_Lean_IR_argInh;
obj* l___private_init_lean_compiler_ir_basic_18__collectJP(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_isPure___main___boxed(obj*);
uint8 l_Lean_IR_Alt_isDefault(obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray(obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
obj* l___private_init_lean_compiler_ir_basic_13__collectExpr(obj*, obj*, obj*);
obj* l_Lean_IR_MaxVar_collectFnBody___main(obj*, obj*);
uint8 l_Array_anyAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__1(obj*, obj*);
obj* l_Lean_IR_push(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_papp_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_HasIndex_visitExpr___main___boxed(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_ctor_expr_core(obj*, obj*, obj*, obj*, obj*, obj*);
}}
obj* l_Lean_IR_mmodifyJPs___rarg(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_vdecl_core(obj*, uint8, obj*, obj*);
}}
obj* l_Lean_IR_JoinPointId_HasToString(obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__1(obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitJP(obj*, obj*);
obj* l_Lean_IR_IRType_beq___boxed(obj*, obj*);
obj* l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_setBody___main(obj*, obj*);
obj* l_Lean_IR_reshapeAux___main(obj*, obj*, obj*);
obj* l_Lean_IR_LitVal_HasBeq;
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___main___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_HasIndex_visitArg(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__1___boxed(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1(obj*);
uint8 l_Lean_IR_HasIndex_visitArg___main(obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1(obj*);
obj* l_Lean_IR_CtorInfo_beq___boxed(obj*, obj*);
obj* l_Lean_IR_HasIndex_visitArg___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_basic_3__collectVar(obj*, obj*, obj*);
obj* l_Lean_IR_reshapeAux(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_resetBody(obj*);
obj* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_MData_empty;
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Inhabited;
obj* l_Lean_IR_Alt_isDefault___main___boxed(obj*);
uint8 l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_beq___main___boxed(obj*, obj*);
obj* l_Lean_IR_FreeVariables_collectFnBody___main(obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj*, obj*);
obj* l_Lean_IR_MaxVar_HasAndthen;
obj* l_Lean_IR_HasIndex_visitFnBody___boxed(obj*, obj*);
uint8 l_Lean_IR_VarId_HasBeq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_eq(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_VarId_HasBeq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_VarId_HasBeq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_VarId_HasToString___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("x_");
return x_0;
}
}
obj* l_Lean_IR_VarId_HasToString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Nat_repr(x_0);
x_2 = l_Lean_IR_VarId_HasToString___closed__1;
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_VarId_Lean_HasFormat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; 
x_1 = l_Nat_repr(x_0);
x_2 = l_Lean_IR_VarId_HasToString___closed__1;
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_3);
return x_5;
}
}
uint8 l_Lean_IR_VarId_lt(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_lt(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_VarId_lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_VarId_lt(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_JoinPointId_HasBeq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_eq(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_JoinPointId_HasBeq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_JoinPointId_HasBeq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_JoinPointId_HasToString___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("block_");
return x_0;
}
}
obj* l_Lean_IR_JoinPointId_HasToString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Nat_repr(x_0);
x_2 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_JoinPointId_Lean_HasFormat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; 
x_1 = l_Nat_repr(x_0);
x_2 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_3 = lean::string_append(x_2, x_1);
lean::dec(x_1);
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_3);
return x_5;
}
}
obj* _init_l_Lean_IR_MData_empty() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_Lean_IR_MData_HasEmptyc() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
uint8 l_Lean_IR_IRType_beq___main(uint8 x_0, uint8 x_1) {
_start:
{
switch (x_0) {
case 0:
{
switch (x_1) {
case 0:
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
default:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
case 1:
{
switch (x_1) {
case 1:
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
default:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
case 2:
{
switch (x_1) {
case 2:
{
uint8 x_6; 
x_6 = 1;
return x_6;
}
default:
{
uint8 x_7; 
x_7 = 0;
return x_7;
}
}
}
case 3:
{
switch (x_1) {
case 3:
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
default:
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
}
}
case 4:
{
switch (x_1) {
case 4:
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
default:
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
}
}
case 5:
{
switch (x_1) {
case 5:
{
uint8 x_12; 
x_12 = 1;
return x_12;
}
default:
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
}
}
case 6:
{
switch (x_1) {
case 6:
{
uint8 x_14; 
x_14 = 1;
return x_14;
}
default:
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
}
}
case 7:
{
switch (x_1) {
case 7:
{
uint8 x_16; 
x_16 = 1;
return x_16;
}
default:
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
}
}
default:
{
switch (x_1) {
case 8:
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
default:
{
uint8 x_19; 
x_19 = 0;
return x_19;
}
}
}
}
}
}
obj* l_Lean_IR_IRType_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_Lean_IR_IRType_beq___main(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
uint8 l_Lean_IR_IRType_beq(uint8 x_0, uint8 x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_IRType_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_IRType_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; uint8 x_4; obj* x_5; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_Lean_IR_IRType_beq(x_2, x_3);
x_5 = lean::box(x_4);
return x_5;
}
}
obj* _init_l_Lean_IR_IRType_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_IRType_beq___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_IR_argInh() {
_start:
{
obj* x_0; 
x_0 = lean::box(1);
return x_0;
}
}
namespace lean {
namespace ir {
obj* mk_var_arg_core(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
}}
namespace lean {
namespace ir {
obj* _init_mk_irrelevant_arg_core() {
_start:
{
obj* x_0; 
x_0 = lean::box(1);
return x_0;
}
}
}}
uint8 l_Lean_IR_LitVal_beq___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::nat_dec_eq(x_2, x_3);
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_0, 0);
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::string_dec_eq(x_7, x_8);
return x_9;
}
}
}
}
obj* l_Lean_IR_LitVal_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_LitVal_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_LitVal_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_LitVal_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_LitVal_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_LitVal_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_LitVal_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_LitVal_beq___boxed), 2, 0);
return x_0;
}
}
uint8 l_Lean_IR_CtorInfo_beq___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_0, 2);
x_5 = lean::cnstr_get(x_0, 3);
x_6 = lean::cnstr_get(x_0, 4);
x_7 = lean::cnstr_get(x_1, 0);
x_8 = lean::cnstr_get(x_1, 1);
x_9 = lean::cnstr_get(x_1, 2);
x_10 = lean::cnstr_get(x_1, 3);
x_11 = lean::cnstr_get(x_1, 4);
x_12 = lean_name_dec_eq(x_2, x_7);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8 x_14; 
x_14 = lean::nat_dec_eq(x_3, x_8);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8 x_16; 
x_16 = lean::nat_dec_eq(x_4, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8 x_18; 
x_18 = lean::nat_dec_eq(x_5, x_10);
if (x_18 == 0)
{
uint8 x_19; 
x_19 = 0;
return x_19;
}
else
{
uint8 x_20; 
x_20 = lean::nat_dec_eq(x_6, x_11);
return x_20;
}
}
}
}
}
}
obj* l_Lean_IR_CtorInfo_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_CtorInfo_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_CtorInfo_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_CtorInfo_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_CtorInfo_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_CtorInfo_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_CtorInfo_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_CtorInfo_beq___boxed), 2, 0);
return x_0;
}
}
namespace lean {
namespace ir {
obj* mk_ctor_expr_core(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set(x_6, 4, x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}}
namespace lean {
namespace ir {
obj* mk_proj_expr_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}}
namespace lean {
namespace ir {
obj* mk_uproj_expr_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(4, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}}
namespace lean {
namespace ir {
obj* mk_sproj_expr_core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(5, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
}}
namespace lean {
namespace ir {
obj* mk_fapp_expr_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(6, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}}
namespace lean {
namespace ir {
obj* mk_papp_expr_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(7, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}}
namespace lean {
namespace ir {
obj* mk_app_expr_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(8, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}}
namespace lean {
namespace ir {
obj* mk_num_expr_core(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
}}
namespace lean {
namespace ir {
obj* mk_str_expr_core(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(11, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
}}
obj* _init_l_Lean_IR_paramInh() {
_start:
{
obj* x_0; uint8 x_1; uint8 x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = 0;
x_2 = 7;
x_3 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_1);
x_4 = x_3;
lean::cnstr_set_scalar(x_4, sizeof(void*)*1 + 1, x_2);
x_5 = x_4;
return x_5;
}
}
namespace lean {
namespace ir {
obj* mk_param_core(obj* x_0, uint8 x_1, uint8 x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_cnstr(0, 1, 2);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set_scalar(x_3, sizeof(void*)*1, x_1);
x_4 = x_3;
lean::cnstr_set_scalar(x_4, sizeof(void*)*1 + 1, x_2);
x_5 = x_4;
return x_5;
}
}
}}
obj* l_Lean_IR_mkParam___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; obj* x_5; 
x_3 = lean::unbox(x_1);
x_4 = lean::unbox(x_2);
x_5 = lean::ir::mk_param_core(x_0, x_3, x_4);
return x_5;
}
}
obj* _init_l_Lean_IR_Inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(12);
return x_0;
}
}
obj* _init_l_Lean_IR_FnBody_nil() {
_start:
{
obj* x_0; 
x_0 = lean::box(12);
return x_0;
}
}
namespace lean {
namespace ir {
obj* mk_vdecl_core(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_2);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*3, x_1);
x_5 = x_4;
return x_5;
}
}
}}
obj* l_Lean_IR_mkVDecl___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = lean::ir::mk_vdecl_core(x_0, x_4, x_2, x_3);
return x_5;
}
}
namespace lean {
namespace ir {
obj* mk_jdecl_core(obj* x_0, obj* x_1, uint8 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_4);
lean::cnstr_set_scalar(x_5, sizeof(void*)*4, x_2);
x_6 = x_5;
return x_6;
}
}
}}
obj* l_Lean_IR_mkJDecl___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = lean::ir::mk_jdecl_core(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
namespace lean {
namespace ir {
obj* mk_uset_core(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_cnstr(3, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_3);
return x_4;
}
}
}}
namespace lean {
namespace ir {
obj* mk_sset_core(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_cnstr(4, 5, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set(x_6, 4, x_5);
lean::cnstr_set_scalar(x_6, sizeof(void*)*5, x_4);
x_7 = x_6;
return x_7;
}
}
}}
obj* l_Lean_IR_mkSSet___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_4);
x_7 = lean::ir::mk_sset_core(x_0, x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
namespace lean {
namespace ir {
obj* mk_case_core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(9, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
return x_3;
}
}
}}
namespace lean {
namespace ir {
obj* mk_ret_core(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(10, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
}}
namespace lean {
namespace ir {
obj* mk_jmp_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(11, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
}}
namespace lean {
namespace ir {
obj* _init_mk_unreachable_core() {
_start:
{
obj* x_0; 
x_0 = lean::box(12);
return x_0;
}
}
}}
obj* l_Lean_IR_Alt_ctor(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_IR_Alt_default(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_altInh() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(12);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
uint8 l_Lean_IR_FnBody_isTerminal___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 9:
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
case 10:
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
case 11:
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
case 12:
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
default:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
}
}
obj* l_Lean_IR_FnBody_isTerminal___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_FnBody_isTerminal___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_FnBody_isTerminal(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_FnBody_isTerminal___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_FnBody_isTerminal___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_FnBody_isTerminal(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_FnBody_body___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 3);
lean::inc(x_1);
return x_1;
}
case 2:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 3);
lean::inc(x_3);
return x_3;
}
case 3:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_0, 3);
lean::inc(x_5);
return x_5;
}
case 4:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_0, 4);
lean::inc(x_7);
return x_7;
}
case 8:
{
obj* x_9; 
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
return x_9;
}
case 9:
{
lean::inc(x_0);
return x_0;
}
case 10:
{
lean::inc(x_0);
return x_0;
}
case 11:
{
lean::inc(x_0);
return x_0;
}
case 12:
{
return x_0;
}
default:
{
obj* x_14; 
x_14 = lean::cnstr_get(x_0, 2);
lean::inc(x_14);
return x_14;
}
}
}
}
obj* l_Lean_IR_FnBody_body___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_FnBody_body(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_FnBody_body___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_FnBody_body___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_FnBody_body(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_FnBody_setBody___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; uint8 x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_7 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_1);
lean::cnstr_set_scalar(x_8, sizeof(void*)*3, x_4);
x_9 = x_8;
return x_9;
}
case 1:
{
obj* x_10; obj* x_12; uint8 x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::cnstr_get(x_0, 0);
x_12 = lean::cnstr_get(x_0, 1);
x_14 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
x_15 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_17 = x_0;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_12);
lean::cnstr_set(x_18, 2, x_15);
lean::cnstr_set(x_18, 3, x_1);
lean::cnstr_set_scalar(x_18, sizeof(void*)*4, x_14);
x_19 = x_18;
return x_19;
}
case 2:
{
obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; 
x_20 = lean::cnstr_get(x_0, 0);
x_22 = lean::cnstr_get(x_0, 1);
x_24 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_26 = x_0;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_0);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_20);
lean::cnstr_set(x_27, 1, x_22);
lean::cnstr_set(x_27, 2, x_24);
lean::cnstr_set(x_27, 3, x_1);
return x_27;
}
case 3:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_34 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_0);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(3, 4, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_30);
lean::cnstr_set(x_35, 2, x_32);
lean::cnstr_set(x_35, 3, x_1);
return x_35;
}
case 4:
{
obj* x_36; obj* x_38; obj* x_40; obj* x_42; uint8 x_44; obj* x_45; obj* x_46; obj* x_47; 
x_36 = lean::cnstr_get(x_0, 0);
x_38 = lean::cnstr_get(x_0, 1);
x_40 = lean::cnstr_get(x_0, 2);
x_42 = lean::cnstr_get(x_0, 3);
x_44 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*5);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 4);
 x_45 = x_0;
} else {
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_0);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(4, 5, 1);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_36);
lean::cnstr_set(x_46, 1, x_38);
lean::cnstr_set(x_46, 2, x_40);
lean::cnstr_set(x_46, 3, x_42);
lean::cnstr_set(x_46, 4, x_1);
lean::cnstr_set_scalar(x_46, sizeof(void*)*5, x_44);
x_47 = x_46;
return x_47;
}
case 5:
{
obj* x_48; obj* x_50; obj* x_52; obj* x_53; 
x_48 = lean::cnstr_get(x_0, 0);
x_50 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_52 = x_0;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_0);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_48);
lean::cnstr_set(x_53, 1, x_50);
lean::cnstr_set(x_53, 2, x_1);
return x_53;
}
case 6:
{
obj* x_54; obj* x_56; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; 
x_54 = lean::cnstr_get(x_0, 0);
x_56 = lean::cnstr_get(x_0, 1);
x_58 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_59 = x_0;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::dec(x_0);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(6, 3, 1);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_54);
lean::cnstr_set(x_60, 1, x_56);
lean::cnstr_set(x_60, 2, x_1);
lean::cnstr_set_scalar(x_60, sizeof(void*)*3, x_58);
x_61 = x_60;
return x_61;
}
case 7:
{
obj* x_62; obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; 
x_62 = lean::cnstr_get(x_0, 0);
x_64 = lean::cnstr_get(x_0, 1);
x_66 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_67 = x_0;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_0);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_62);
lean::cnstr_set(x_68, 1, x_64);
lean::cnstr_set(x_68, 2, x_1);
lean::cnstr_set_scalar(x_68, sizeof(void*)*3, x_66);
x_69 = x_68;
return x_69;
}
case 8:
{
obj* x_70; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 1);
 x_72 = x_0;
} else {
 lean::inc(x_70);
 lean::dec(x_0);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set(x_73, 1, x_1);
return x_73;
}
default:
{
lean::dec(x_1);
return x_0;
}
}
}
}
obj* l_Lean_IR_FnBody_setBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_FnBody_setBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_FnBody_resetBody(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(12);
x_2 = l_Lean_IR_FnBody_setBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_FnBody_split(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_IR_FnBody_body___main(x_0);
x_2 = lean::box(12);
x_3 = l_Lean_IR_FnBody_setBody___main(x_0, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
obj* l_Lean_IR_AltCore_body___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
return x_3;
}
}
}
obj* l_Lean_IR_AltCore_body___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_AltCore_body___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_AltCore_body(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_AltCore_body___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_AltCore_body___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_AltCore_body(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_AltCore_setBody___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 1);
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
if (lean::is_scalar(x_4)) {
 x_5 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_5 = x_4;
}
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
else
{
obj* x_6; obj* x_7; 
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_6 = x_0;
} else {
 lean::dec(x_0);
 x_6 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_1);
return x_7;
}
}
}
obj* l_Lean_IR_AltCore_setBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_AltCore_setBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_AltCore_modifyBody___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_6 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::apply_1(x_0, x_4);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_11 = x_1;
} else {
 lean::inc(x_9);
 lean::dec(x_1);
 x_11 = lean::box(0);
}
x_12 = lean::apply_1(x_0, x_9);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* l_Lean_IR_AltCore_modifyBody(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 x_6 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::apply_1(x_0, x_4);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_11 = x_1;
} else {
 lean::inc(x_9);
 lean::dec(x_1);
 x_11 = lean::box(0);
}
x_12 = lean::apply_1(x_0, x_9);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
}
}
obj* _init_l_Lean_IR_AltCore_mmodifyBody___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Alt_default), 1, 0);
return x_0;
}
}
obj* l_Lean_IR_AltCore_mmodifyBody___main___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Alt_ctor), 2, 1);
lean::closure_set(x_17, 0, x_3);
x_18 = lean::apply_1(x_1, x_5);
x_19 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_26; obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
x_32 = lean::apply_1(x_1, x_20);
x_33 = l_Lean_IR_AltCore_mmodifyBody___main___rarg___closed__1;
x_34 = lean::apply_4(x_29, lean::box(0), lean::box(0), x_33, x_32);
return x_34;
}
}
}
obj* l_Lean_IR_AltCore_mmodifyBody___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_AltCore_mmodifyBody___main___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_IR_AltCore_mmodifyBody___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_AltCore_mmodifyBody___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_AltCore_mmodifyBody___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Alt_ctor), 2, 1);
lean::closure_set(x_17, 0, x_3);
x_18 = lean::apply_1(x_1, x_5);
x_19 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_26; obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_26, 0);
lean::inc(x_29);
lean::dec(x_26);
x_32 = lean::apply_1(x_1, x_20);
x_33 = l_Lean_IR_AltCore_mmodifyBody___main___rarg___closed__1;
x_34 = lean::apply_4(x_29, lean::box(0), lean::box(0), x_33, x_32);
return x_34;
}
}
}
obj* l_Lean_IR_AltCore_mmodifyBody(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_AltCore_mmodifyBody___rarg), 3, 0);
return x_1;
}
}
obj* l_Lean_IR_AltCore_mmodifyBody___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_AltCore_mmodifyBody(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Lean_IR_Alt_isDefault___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
else
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
}
}
obj* l_Lean_IR_Alt_isDefault___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Alt_isDefault___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_Alt_isDefault(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_Alt_isDefault___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Alt_isDefault___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Alt_isDefault(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_push(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(12);
x_3 = l_Lean_IR_FnBody_setBody___main(x_1, x_2);
x_4 = lean::array_push(x_0, x_3);
return x_4;
}
}
obj* l_Lean_IR_flattenAux___main(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_2 == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_IR_FnBody_body___main(x_0);
x_4 = l_Lean_IR_push(x_1, x_0);
x_0 = x_3;
x_1 = x_4;
goto _start;
}
else
{
obj* x_6; 
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_0);
return x_6;
}
}
}
obj* l_Lean_IR_flattenAux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_flattenAux___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_FnBody_flatten(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_IR_flattenAux___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_reshapeAux___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = lean::nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_8; uint8 x_9; 
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_sub(x_1, x_5);
lean::dec(x_1);
x_8 = lean::array_get_size(x_0);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::box(12);
x_12 = l_Lean_IR_FnBody_setBody___main(x_11, x_2);
x_1 = x_6;
x_2 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::array_fget(x_0, x_6);
x_15 = lean::box(12);
x_16 = lean::array_fset(x_0, x_6, x_15);
x_17 = l_Lean_IR_FnBody_setBody___main(x_14, x_2);
x_0 = x_16;
x_1 = x_6;
x_2 = x_17;
goto _start;
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
}
}
obj* l_Lean_IR_reshapeAux(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_reshapeAux___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_reshape(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::array_get_size(x_0);
x_3 = l_Lean_IR_reshapeAux___main(x_0, x_2, x_1);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_modifyJPs___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::array_fget(x_2, x_1);
x_9 = lean::box(12);
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_1, x_11);
switch (lean::obj_tag(x_8)) {
case 1:
{
obj* x_13; obj* x_15; uint8 x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*4);
x_18 = lean::cnstr_get(x_8, 2);
x_20 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_22 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_8);
 x_22 = lean::box(0);
}
lean::inc(x_0);
x_24 = lean::apply_1(x_0, x_18);
if (lean::is_scalar(x_22)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_22;
}
lean::cnstr_set(x_25, 0, x_13);
lean::cnstr_set(x_25, 1, x_15);
lean::cnstr_set(x_25, 2, x_24);
lean::cnstr_set(x_25, 3, x_20);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_17);
x_26 = x_25;
x_27 = lean::array_fset(x_10, x_1, x_26);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_27;
goto _start;
}
default:
{
obj* x_30; 
x_30 = lean::array_fset(x_10, x_1, x_8);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_30;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_modifyJPs(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_hmmapAux___main___at_Lean_IR_modifyJPs___spec__1(x_1, x_2, x_0);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::nat_add(x_0, x_5);
x_7 = lean::array_fset(x_1, x_0, x_4);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(x_2, x_3, x_6, x_7);
return x_8;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_2);
lean::cnstr_set(x_12, 2, x_5);
lean::cnstr_set(x_12, 3, x_4);
lean::cnstr_set_scalar(x_12, sizeof(void*)*4, x_3);
x_13 = x_12;
x_14 = lean::apply_2(x_9, lean::box(0), x_13);
return x_14;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_3);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_9; obj* x_12; obj* x_15; 
lean::dec(x_1);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::apply_2(x_12, lean::box(0), x_3);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_23; obj* x_24; 
x_16 = lean::array_fget(x_3, x_2);
x_17 = lean::box(12);
x_18 = lean::array_fset(x_3, x_2, x_17);
x_19 = lean::cnstr_get(x_0, 1);
lean::inc(x_19);
lean::inc(x_1);
lean::inc(x_0);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed), 5, 4);
lean::closure_set(x_23, 0, x_2);
lean::closure_set(x_23, 1, x_18);
lean::closure_set(x_23, 2, x_0);
lean::closure_set(x_23, 3, x_1);
switch (lean::obj_tag(x_16)) {
case 1:
{
obj* x_26; obj* x_28; uint8 x_30; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; 
x_26 = lean::cnstr_get(x_16, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_16, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*4);
x_31 = lean::cnstr_get(x_16, 2);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_16, 3);
lean::inc(x_33);
lean::dec(x_16);
x_36 = lean::apply_1(x_1, x_31);
x_37 = lean::box(x_30);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2___boxed), 6, 5);
lean::closure_set(x_38, 0, x_0);
lean::closure_set(x_38, 1, x_26);
lean::closure_set(x_38, 2, x_28);
lean::closure_set(x_38, 3, x_37);
lean::closure_set(x_38, 4, x_33);
lean::inc(x_19);
x_40 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_36, x_38);
x_41 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_40, x_23);
return x_41;
}
default:
{
obj* x_43; 
lean::dec(x_1);
x_43 = lean::box(0);
x_24 = x_43;
goto lbl_25;
}
}
lbl_25:
{
obj* x_45; obj* x_48; obj* x_51; obj* x_52; 
lean::dec(x_24);
x_45 = lean::cnstr_get(x_0, 0);
lean::inc(x_45);
lean::dec(x_0);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_51 = lean::apply_2(x_48, lean::box(0), x_16);
x_52 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_51, x_23);
return x_52;
}
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg), 4, 0);
return x_1;
}
}
obj* l_Lean_IR_mmodifyJPs___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(x_0, x_2, x_3, x_1);
return x_4;
}
}
obj* l_Lean_IR_mmodifyJPs(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_mmodifyJPs___rarg), 3, 0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_3);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(x_0, x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_mmodifyJPs___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_mmodifyJPs(x_0);
lean::dec(x_0);
return x_1;
}
}
namespace lean {
namespace ir {
obj* mk_alt_core(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
lean::cnstr_set(x_6, 4, x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
return x_7;
}
}
}}
namespace lean {
namespace ir {
obj* mk_decl_core(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*3, x_2);
x_5 = x_4;
return x_5;
}
}
}}
obj* l_Lean_IR_mkDecl___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = lean::ir::mk_decl_core(x_0, x_1, x_4, x_3);
return x_5;
}
}
uint8 l_Lean_IR_Expr_isPure___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 2:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 9:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
case 10:
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
case 12:
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
case 13:
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
default:
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_Lean_IR_Expr_isPure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Expr_isPure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_Expr_isPure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_Expr_isPure___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Expr_isPure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Expr_isPure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Array_anyAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_0);
x_3 = lean::nat_dec_lt(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
uint8 x_6; 
lean::dec(x_1);
x_6 = 0;
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::array_fget(x_0, x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; uint8 x_11; 
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = l_Lean_IR_FnBody_isPure___main(x_8);
lean::dec(x_8);
if (x_11 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_1, x_13);
lean::dec(x_1);
x_1 = x_14;
goto _start;
}
else
{
uint8 x_18; 
lean::dec(x_1);
x_18 = 1;
return x_18;
}
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_7);
x_20 = lean::mk_nat_obj(1ul);
x_21 = lean::nat_add(x_1, x_20);
lean::dec(x_1);
x_1 = x_21;
goto _start;
}
}
}
}
uint8 l_Lean_IR_FnBody_isPure___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::cnstr_get(x_0, 2);
x_3 = l_Lean_IR_Expr_isPure___main(x_1);
if (x_3 == 0)
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
else
{
x_0 = x_2;
goto _start;
}
}
case 1:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::cnstr_get(x_0, 2);
x_7 = lean::cnstr_get(x_0, 3);
x_8 = l_Lean_IR_FnBody_isPure___main(x_6);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
else
{
x_0 = x_7;
goto _start;
}
}
case 3:
{
obj* x_11; 
x_11 = lean::cnstr_get(x_0, 3);
x_0 = x_11;
goto _start;
}
case 4:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_0, 4);
x_0 = x_13;
goto _start;
}
case 8:
{
obj* x_15; 
x_15 = lean::cnstr_get(x_0, 1);
x_0 = x_15;
goto _start;
}
case 9:
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_0, 2);
x_18 = lean::mk_nat_obj(0ul);
x_19 = l_Array_anyAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(x_17, x_18);
return x_19;
}
case 10:
{
uint8 x_20; 
x_20 = 1;
return x_20;
}
case 11:
{
uint8 x_21; 
x_21 = 1;
return x_21;
}
case 12:
{
uint8 x_22; 
x_22 = 1;
return x_22;
}
default:
{
uint8 x_23; 
x_23 = 0;
return x_23;
}
}
}
}
obj* l_Array_anyAux___main___at_Lean_IR_FnBody_isPure___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Array_anyAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_FnBody_isPure___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_FnBody_isPure___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_FnBody_isPure(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_FnBody_isPure___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_FnBody_isPure___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_FnBody_isPure(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::nat_dec_lt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = lean::nat_dec_lt(x_5, x_1);
lean::dec(x_5);
if (x_14 == 0)
{
obj* x_17; 
lean::dec(x_9);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_7);
return x_17;
}
else
{
lean::dec(x_7);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
uint8 l_Lean_IR_VarId_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = lean::nat_dec_eq(x_1, x_2);
return x_4;
}
else
{
obj* x_5; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::nat_dec_eq(x_5, x_2);
lean::dec(x_5);
return x_8;
}
}
}
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_VarId_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_VarId_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_VarId_hasAeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_VarId_alphaEqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_Lean_IR_Arg_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = l_Lean_IR_VarId_alphaEqv(x_0, x_3, x_4);
return x_5;
}
else
{
uint8 x_7; 
lean::dec(x_0);
x_7 = 0;
return x_7;
}
}
else
{
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
}
}
obj* l_Lean_IR_Arg_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Arg_alphaEqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Lean_IR_Arg_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_Arg_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Arg_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Arg_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_Arg_hasAeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Arg_alphaEqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Arg_alphaEqv___main___boxed), 3, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::array_get_size(x_1);
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
if (x_6 == 0)
{
uint8 x_10; 
lean::dec(x_3);
x_10 = 0;
return x_10;
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(0ul);
x_12 = l_Array_isEqvAux___main___rarg(x_1, x_2, lean::box(0), x_3, x_11);
return x_12;
}
}
}
uint8 l_Lean_IR_args_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_args_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_args_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_args_hasAeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_args_alphaEqv___boxed), 3, 0);
return x_0;
}
}
uint8 l_Lean_IR_Expr_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
x_7 = l_Lean_IR_CtorInfo_beq___main(x_3, x_5);
if (x_7 == 0)
{
uint8 x_9; 
lean::dec(x_0);
x_9 = 0;
return x_9;
}
else
{
uint8 x_10; 
x_10 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_4, x_6);
return x_10;
}
}
default:
{
uint8 x_12; 
lean::dec(x_0);
x_12 = 0;
return x_12;
}
}
}
case 1:
{
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_2, 0);
x_15 = l_Lean_IR_VarId_alphaEqv(x_0, x_13, x_14);
return x_15;
}
default:
{
uint8 x_17; 
lean::dec(x_0);
x_17 = 0;
return x_17;
}
}
}
case 2:
{
uint8 x_18; 
x_18 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; obj* x_25; uint8 x_27; 
x_19 = lean::cnstr_get(x_1, 0);
x_20 = lean::cnstr_get(x_1, 1);
x_21 = lean::cnstr_get(x_1, 2);
x_22 = lean::cnstr_get(x_2, 0);
x_23 = lean::cnstr_get(x_2, 1);
x_24 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_25 = lean::cnstr_get(x_2, 2);
lean::inc(x_0);
x_27 = l_Lean_IR_VarId_alphaEqv(x_0, x_19, x_22);
if (x_27 == 0)
{
uint8 x_29; 
lean::dec(x_0);
x_29 = 0;
return x_29;
}
else
{
uint8 x_30; 
x_30 = l_Lean_IR_CtorInfo_beq___main(x_20, x_23);
if (x_30 == 0)
{
uint8 x_32; 
lean::dec(x_0);
x_32 = 0;
return x_32;
}
else
{
if (x_18 == 0)
{
if (x_24 == 0)
{
uint8 x_33; 
x_33 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_21, x_25);
return x_33;
}
else
{
uint8 x_35; 
lean::dec(x_0);
x_35 = 0;
return x_35;
}
}
else
{
if (x_24 == 0)
{
uint8 x_37; 
lean::dec(x_0);
x_37 = 0;
return x_37;
}
else
{
uint8 x_38; 
x_38 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_21, x_25);
return x_38;
}
}
}
}
}
default:
{
uint8 x_40; 
lean::dec(x_0);
x_40 = 0;
return x_40;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; uint8 x_45; 
x_41 = lean::cnstr_get(x_1, 0);
x_42 = lean::cnstr_get(x_1, 1);
x_43 = lean::cnstr_get(x_2, 0);
x_44 = lean::cnstr_get(x_2, 1);
x_45 = lean::nat_dec_eq(x_41, x_43);
if (x_45 == 0)
{
uint8 x_47; 
lean::dec(x_0);
x_47 = 0;
return x_47;
}
else
{
uint8 x_48; 
x_48 = l_Lean_IR_VarId_alphaEqv(x_0, x_42, x_44);
return x_48;
}
}
default:
{
uint8 x_50; 
lean::dec(x_0);
x_50 = 0;
return x_50;
}
}
}
case 4:
{
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; uint8 x_55; 
x_51 = lean::cnstr_get(x_1, 0);
x_52 = lean::cnstr_get(x_1, 1);
x_53 = lean::cnstr_get(x_2, 0);
x_54 = lean::cnstr_get(x_2, 1);
x_55 = lean::nat_dec_eq(x_51, x_53);
if (x_55 == 0)
{
uint8 x_57; 
lean::dec(x_0);
x_57 = 0;
return x_57;
}
else
{
uint8 x_58; 
x_58 = l_Lean_IR_VarId_alphaEqv(x_0, x_52, x_54);
return x_58;
}
}
default:
{
uint8 x_60; 
lean::dec(x_0);
x_60 = 0;
return x_60;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; uint8 x_67; 
x_61 = lean::cnstr_get(x_1, 0);
x_62 = lean::cnstr_get(x_1, 1);
x_63 = lean::cnstr_get(x_1, 2);
x_64 = lean::cnstr_get(x_2, 0);
x_65 = lean::cnstr_get(x_2, 1);
x_66 = lean::cnstr_get(x_2, 2);
x_67 = lean::nat_dec_eq(x_61, x_64);
if (x_67 == 0)
{
uint8 x_69; 
lean::dec(x_0);
x_69 = 0;
return x_69;
}
else
{
uint8 x_70; 
x_70 = lean::nat_dec_eq(x_62, x_65);
if (x_70 == 0)
{
uint8 x_72; 
lean::dec(x_0);
x_72 = 0;
return x_72;
}
else
{
uint8 x_73; 
x_73 = l_Lean_IR_VarId_alphaEqv(x_0, x_63, x_66);
return x_73;
}
}
}
default:
{
uint8 x_75; 
lean::dec(x_0);
x_75 = 0;
return x_75;
}
}
}
case 6:
{
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; uint8 x_80; 
x_76 = lean::cnstr_get(x_1, 0);
x_77 = lean::cnstr_get(x_1, 1);
x_78 = lean::cnstr_get(x_2, 0);
x_79 = lean::cnstr_get(x_2, 1);
x_80 = lean_name_dec_eq(x_76, x_78);
if (x_80 == 0)
{
uint8 x_82; 
lean::dec(x_0);
x_82 = 0;
return x_82;
}
else
{
uint8 x_83; 
x_83 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_77, x_79);
return x_83;
}
}
default:
{
uint8 x_85; 
lean::dec(x_0);
x_85 = 0;
return x_85;
}
}
}
case 7:
{
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_86; obj* x_87; obj* x_88; uint8 x_89; 
x_86 = lean::cnstr_get(x_1, 0);
x_87 = lean::cnstr_get(x_2, 0);
x_88 = lean::cnstr_get(x_2, 1);
x_89 = lean_name_dec_eq(x_86, x_87);
if (x_89 == 0)
{
uint8 x_91; 
lean::dec(x_0);
x_91 = 0;
return x_91;
}
else
{
uint8 x_92; 
x_92 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_88, x_88);
return x_92;
}
}
default:
{
uint8 x_94; 
lean::dec(x_0);
x_94 = 0;
return x_94;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; uint8 x_100; 
x_95 = lean::cnstr_get(x_1, 0);
x_96 = lean::cnstr_get(x_1, 1);
x_97 = lean::cnstr_get(x_2, 0);
x_98 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_100 = l_Lean_IR_VarId_alphaEqv(x_0, x_95, x_97);
if (x_100 == 0)
{
uint8 x_102; 
lean::dec(x_0);
x_102 = 0;
return x_102;
}
else
{
uint8 x_103; 
x_103 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_96, x_98);
return x_103;
}
}
default:
{
uint8 x_105; 
lean::dec(x_0);
x_105 = 0;
return x_105;
}
}
}
case 9:
{
uint8 x_106; 
x_106 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_107; uint8 x_108; obj* x_109; uint8 x_110; 
x_107 = lean::cnstr_get(x_1, 0);
x_108 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_109 = lean::cnstr_get(x_2, 0);
x_110 = l_Lean_IR_IRType_beq___main(x_106, x_108);
if (x_110 == 0)
{
uint8 x_112; 
lean::dec(x_0);
x_112 = 0;
return x_112;
}
else
{
uint8 x_113; 
x_113 = l_Lean_IR_VarId_alphaEqv(x_0, x_107, x_109);
return x_113;
}
}
default:
{
uint8 x_115; 
lean::dec(x_0);
x_115 = 0;
return x_115;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_116; obj* x_117; uint8 x_118; 
x_116 = lean::cnstr_get(x_1, 0);
x_117 = lean::cnstr_get(x_2, 0);
x_118 = l_Lean_IR_VarId_alphaEqv(x_0, x_116, x_117);
return x_118;
}
default:
{
uint8 x_120; 
lean::dec(x_0);
x_120 = 0;
return x_120;
}
}
}
case 11:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_122; obj* x_123; uint8 x_124; 
x_122 = lean::cnstr_get(x_1, 0);
x_123 = lean::cnstr_get(x_2, 0);
x_124 = l_Lean_IR_LitVal_beq___main(x_122, x_123);
return x_124;
}
default:
{
uint8 x_125; 
x_125 = 0;
return x_125;
}
}
}
case 12:
{
switch (lean::obj_tag(x_2)) {
case 12:
{
obj* x_126; obj* x_127; uint8 x_128; 
x_126 = lean::cnstr_get(x_1, 0);
x_127 = lean::cnstr_get(x_2, 0);
x_128 = l_Lean_IR_VarId_alphaEqv(x_0, x_126, x_127);
return x_128;
}
default:
{
uint8 x_130; 
lean::dec(x_0);
x_130 = 0;
return x_130;
}
}
}
default:
{
switch (lean::obj_tag(x_2)) {
case 13:
{
obj* x_131; obj* x_132; uint8 x_133; 
x_131 = lean::cnstr_get(x_1, 0);
x_132 = lean::cnstr_get(x_2, 0);
x_133 = l_Lean_IR_VarId_alphaEqv(x_0, x_131, x_132);
return x_133;
}
default:
{
uint8 x_135; 
lean::dec(x_0);
x_135 = 0;
return x_135;
}
}
}
}
}
}
obj* l_Lean_IR_Expr_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Expr_alphaEqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
uint8 l_Lean_IR_Expr_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_Expr_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Expr_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_Expr_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_IR_Expr_hasAeqv() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Expr_alphaEqv___boxed), 3, 0);
return x_0;
}
}
obj* l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = lean::nat_dec_lt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = lean::nat_dec_lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = lean::nat_dec_lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = lean::nat_dec_lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; 
x_47 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_34, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_28);
return x_47;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_47, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_47, 1);
x_58 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_60 = x_47;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
x_61 = 0;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_58);
lean::cnstr_set(x_62, 3, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = 1;
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_36;
}
lean::cnstr_set(x_65, 0, x_28);
lean::cnstr_set(x_65, 1, x_30);
lean::cnstr_set(x_65, 2, x_32);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
return x_66;
}
else
{
uint8 x_67; 
x_67 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_67 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_47, 1);
x_70 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_72 = x_47;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_47);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_54, 0);
x_75 = lean::cnstr_get(x_54, 1);
x_77 = lean::cnstr_get(x_54, 2);
x_79 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_81 = x_54;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_54);
 x_81 = lean::box(0);
}
x_82 = 1;
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_28);
lean::cnstr_set(x_83, 1, x_30);
lean::cnstr_set(x_83, 2, x_32);
lean::cnstr_set(x_83, 3, x_52);
lean::cnstr_set_scalar(x_83, sizeof(void*)*4, x_82);
x_84 = x_83;
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_72;
}
lean::cnstr_set(x_85, 0, x_73);
lean::cnstr_set(x_85, 1, x_75);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_79);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_82);
x_86 = x_85;
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_67);
x_88 = x_87;
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_47, 1);
x_91 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_93 = x_47;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_47);
 x_93 = lean::box(0);
}
x_94 = 0;
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_52);
lean::cnstr_set(x_95, 1, x_89);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_54);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_94);
x_96 = x_95;
if (lean::is_scalar(x_36)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_36;
}
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_67);
x_98 = x_97;
return x_98;
}
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*4);
if (x_99 == 0)
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_100 = lean::cnstr_get(x_47, 1);
x_102 = lean::cnstr_get(x_47, 2);
x_104 = lean::cnstr_get(x_47, 3);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_106 = x_47;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_47);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_52, 0);
x_109 = lean::cnstr_get(x_52, 1);
x_111 = lean::cnstr_get(x_52, 2);
x_113 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_115 = x_52;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_52);
 x_115 = lean::box(0);
}
x_116 = 1;
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_28);
lean::cnstr_set(x_117, 1, x_30);
lean::cnstr_set(x_117, 2, x_32);
lean::cnstr_set(x_117, 3, x_107);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_116);
x_118 = x_117;
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_106;
}
lean::cnstr_set(x_119, 0, x_113);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set(x_119, 2, x_102);
lean::cnstr_set(x_119, 3, x_104);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_116);
x_120 = x_119;
if (lean::is_scalar(x_36)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_36;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_109);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_99);
x_122 = x_121;
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_47, 3);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_47, 1);
x_127 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_129 = x_47;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_47);
 x_129 = lean::box(0);
}
x_130 = 0;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_127);
lean::cnstr_set(x_131, 3, x_123);
lean::cnstr_set_scalar(x_131, sizeof(void*)*4, x_130);
x_132 = x_131;
if (lean::is_scalar(x_36)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_36;
}
lean::cnstr_set(x_133, 0, x_28);
lean::cnstr_set(x_133, 1, x_30);
lean::cnstr_set(x_133, 2, x_32);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_99);
x_134 = x_133;
return x_134;
}
else
{
uint8 x_135; 
x_135 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*4);
if (x_135 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_36);
x_137 = lean::cnstr_get(x_47, 1);
x_139 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_141 = x_47;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_47);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_123, 0);
x_144 = lean::cnstr_get(x_123, 1);
x_146 = lean::cnstr_get(x_123, 2);
x_148 = lean::cnstr_get(x_123, 3);
if (lean::is_exclusive(x_123)) {
 x_150 = x_123;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_123);
 x_150 = lean::box(0);
}
lean::inc(x_52);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_28);
lean::cnstr_set(x_152, 1, x_30);
lean::cnstr_set(x_152, 2, x_32);
lean::cnstr_set(x_152, 3, x_52);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_153 = x_52;
} else {
 lean::dec(x_52);
 x_153 = lean::box(0);
}
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_99);
x_154 = x_152;
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_142);
lean::cnstr_set(x_155, 1, x_144);
lean::cnstr_set(x_155, 2, x_146);
lean::cnstr_set(x_155, 3, x_148);
lean::cnstr_set_scalar(x_155, sizeof(void*)*4, x_99);
x_156 = x_155;
if (lean::is_scalar(x_141)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_141;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_137);
lean::cnstr_set(x_157, 2, x_139);
lean::cnstr_set(x_157, 3, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_135);
x_158 = x_157;
return x_158;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_159 = lean::cnstr_get(x_47, 1);
x_161 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_163 = x_47;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_47);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_52, 0);
x_166 = lean::cnstr_get(x_52, 1);
x_168 = lean::cnstr_get(x_52, 2);
x_170 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_172 = x_52;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_52);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_135);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_123);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_36)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_36;
}
lean::cnstr_set(x_178, 0, x_28);
lean::cnstr_set(x_178, 1, x_30);
lean::cnstr_set(x_178, 2, x_32);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_135);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
else
{
uint8 x_180; 
x_180 = l_RBNode_isRed___main___rarg(x_28);
if (x_180 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_182 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_182 = x_36;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_30);
lean::cnstr_set(x_182, 2, x_32);
lean::cnstr_set(x_182, 3, x_34);
lean::cnstr_set_scalar(x_182, sizeof(void*)*4, x_6);
x_183 = x_182;
return x_183;
}
else
{
obj* x_184; 
x_184 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_28, x_1, x_2);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_34);
return x_184;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; 
x_191 = lean::cnstr_get(x_184, 3);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_197; uint8 x_198; obj* x_199; obj* x_200; uint8 x_201; obj* x_202; obj* x_203; 
x_193 = lean::cnstr_get(x_184, 1);
x_195 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_197 = x_184;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_184);
 x_197 = lean::box(0);
}
x_198 = 0;
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_191);
lean::cnstr_set(x_199, 1, x_193);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_191);
lean::cnstr_set_scalar(x_199, sizeof(void*)*4, x_198);
x_200 = x_199;
x_201 = 1;
if (lean::is_scalar(x_36)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_36;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_30);
lean::cnstr_set(x_202, 2, x_32);
lean::cnstr_set(x_202, 3, x_34);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_201);
x_203 = x_202;
return x_203;
}
else
{
uint8 x_204; 
x_204 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*4);
if (x_204 == 0)
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_216; obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_205 = lean::cnstr_get(x_184, 1);
x_207 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_209 = x_184;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_184);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_191, 0);
x_212 = lean::cnstr_get(x_191, 1);
x_214 = lean::cnstr_get(x_191, 2);
x_216 = lean::cnstr_get(x_191, 3);
if (lean::is_exclusive(x_191)) {
 x_218 = x_191;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::inc(x_214);
 lean::inc(x_216);
 lean::dec(x_191);
 x_218 = lean::box(0);
}
x_219 = 1;
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_189);
lean::cnstr_set(x_220, 1, x_205);
lean::cnstr_set(x_220, 2, x_207);
lean::cnstr_set(x_220, 3, x_210);
lean::cnstr_set_scalar(x_220, sizeof(void*)*4, x_219);
x_221 = x_220;
if (lean::is_scalar(x_209)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_209;
}
lean::cnstr_set(x_222, 0, x_216);
lean::cnstr_set(x_222, 1, x_30);
lean::cnstr_set(x_222, 2, x_32);
lean::cnstr_set(x_222, 3, x_34);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_219);
x_223 = x_222;
if (lean::is_scalar(x_36)) {
 x_224 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_224 = x_36;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set(x_224, 1, x_212);
lean::cnstr_set(x_224, 2, x_214);
lean::cnstr_set(x_224, 3, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_204);
x_225 = x_224;
return x_225;
}
else
{
obj* x_226; obj* x_228; obj* x_230; uint8 x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_184, 1);
x_228 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_230 = x_184;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_184);
 x_230 = lean::box(0);
}
x_231 = 0;
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_189);
lean::cnstr_set(x_232, 1, x_226);
lean::cnstr_set(x_232, 2, x_228);
lean::cnstr_set(x_232, 3, x_191);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_231);
x_233 = x_232;
if (lean::is_scalar(x_36)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_36;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_30);
lean::cnstr_set(x_234, 2, x_32);
lean::cnstr_set(x_234, 3, x_34);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_204);
x_235 = x_234;
return x_235;
}
}
}
else
{
uint8 x_236; 
x_236 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*4);
if (x_236 == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_252; uint8 x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_237 = lean::cnstr_get(x_184, 1);
x_239 = lean::cnstr_get(x_184, 2);
x_241 = lean::cnstr_get(x_184, 3);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_243 = x_184;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_184);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_189, 0);
x_246 = lean::cnstr_get(x_189, 1);
x_248 = lean::cnstr_get(x_189, 2);
x_250 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_252 = x_189;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_189);
 x_252 = lean::box(0);
}
x_253 = 1;
if (lean::is_scalar(x_252)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_252;
}
lean::cnstr_set(x_254, 0, x_244);
lean::cnstr_set(x_254, 1, x_246);
lean::cnstr_set(x_254, 2, x_248);
lean::cnstr_set(x_254, 3, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_253);
x_255 = x_254;
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_241);
lean::cnstr_set(x_256, 1, x_30);
lean::cnstr_set(x_256, 2, x_32);
lean::cnstr_set(x_256, 3, x_34);
lean::cnstr_set_scalar(x_256, sizeof(void*)*4, x_253);
x_257 = x_256;
if (lean::is_scalar(x_36)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_36;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_237);
lean::cnstr_set(x_258, 2, x_239);
lean::cnstr_set(x_258, 3, x_257);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_236);
x_259 = x_258;
return x_259;
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_184, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_266; uint8 x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_262 = lean::cnstr_get(x_184, 1);
x_264 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_266 = x_184;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_184);
 x_266 = lean::box(0);
}
x_267 = 0;
if (lean::is_scalar(x_266)) {
 x_268 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_268 = x_266;
}
lean::cnstr_set(x_268, 0, x_189);
lean::cnstr_set(x_268, 1, x_262);
lean::cnstr_set(x_268, 2, x_264);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
x_269 = x_268;
if (lean::is_scalar(x_36)) {
 x_270 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_270 = x_36;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_30);
lean::cnstr_set(x_270, 2, x_32);
lean::cnstr_set(x_270, 3, x_34);
lean::cnstr_set_scalar(x_270, sizeof(void*)*4, x_236);
x_271 = x_270;
return x_271;
}
else
{
uint8 x_272; 
x_272 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_272 == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_36);
x_274 = lean::cnstr_get(x_184, 1);
x_276 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_278 = x_184;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_184);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_260, 0);
x_281 = lean::cnstr_get(x_260, 1);
x_283 = lean::cnstr_get(x_260, 2);
x_285 = lean::cnstr_get(x_260, 3);
if (lean::is_exclusive(x_260)) {
 x_287 = x_260;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_260);
 x_287 = lean::box(0);
}
lean::inc(x_189);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_189);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_276);
lean::cnstr_set(x_289, 3, x_279);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 lean::cnstr_release(x_189, 2);
 lean::cnstr_release(x_189, 3);
 x_290 = x_189;
} else {
 lean::dec(x_189);
 x_290 = lean::box(0);
}
lean::cnstr_set_scalar(x_289, sizeof(void*)*4, x_236);
x_291 = x_289;
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_285);
lean::cnstr_set(x_292, 1, x_30);
lean::cnstr_set(x_292, 2, x_32);
lean::cnstr_set(x_292, 3, x_34);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_236);
x_293 = x_292;
if (lean::is_scalar(x_278)) {
 x_294 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_294 = x_278;
}
lean::cnstr_set(x_294, 0, x_291);
lean::cnstr_set(x_294, 1, x_281);
lean::cnstr_set(x_294, 2, x_283);
lean::cnstr_set(x_294, 3, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*4, x_272);
x_295 = x_294;
return x_295;
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_296 = lean::cnstr_get(x_184, 1);
x_298 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_300 = x_184;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_184);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_189, 0);
x_303 = lean::cnstr_get(x_189, 1);
x_305 = lean::cnstr_get(x_189, 2);
x_307 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_309 = x_189;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_189);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_301);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_305);
lean::cnstr_set(x_310, 3, x_307);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_272);
x_311 = x_310;
x_312 = 0;
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_313 = x_300;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_296);
lean::cnstr_set(x_313, 2, x_298);
lean::cnstr_set(x_313, 3, x_260);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_312);
x_314 = x_313;
if (lean::is_scalar(x_36)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_36;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_30);
lean::cnstr_set(x_315, 2, x_32);
lean::cnstr_set(x_315, 3, x_34);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_272);
x_316 = x_315;
return x_316;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_Lean_IR_addVarRename(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_0, x_1, x_2);
return x_4;
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_0;
}
}
}
obj* l_Lean_IR_addParamRename(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; uint8 x_4; uint8 x_5; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1 + 1);
x_4 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1 + 1);
x_5 = l_Lean_IR_IRType_beq___main(x_3, x_4);
if (x_5 == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_9 = lean::box(0);
return x_9;
}
else
{
uint8 x_10; uint8 x_11; uint8 x_12; 
x_10 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
x_11 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_10 == 0)
{
if (x_11 == 0)
{
uint8 x_14; 
x_14 = 1;
x_12 = x_14;
goto lbl_13;
}
else
{
uint8 x_15; 
x_15 = 0;
x_12 = x_15;
goto lbl_13;
}
}
else
{
if (x_11 == 0)
{
uint8 x_16; 
x_16 = 0;
x_12 = x_16;
goto lbl_13;
}
else
{
uint8 x_17; 
x_17 = 1;
x_12 = x_17;
goto lbl_13;
}
}
lbl_13:
{
if (x_12 == 0)
{
obj* x_21; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_21 = lean::box(0);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
lean::dec(x_1);
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
lean::dec(x_2);
x_28 = l_Lean_IR_addVarRename(x_0, x_22, x_25);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_9; uint8 x_10; 
x_9 = lean::array_get_size(x_2);
x_10 = lean::nat_dec_lt(x_3, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::array_fget(x_1, x_3);
x_14 = lean::array_fget(x_2, x_3);
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_3, x_15);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_20; 
lean::dec(x_13);
lean::dec(x_14);
x_20 = lean::box(0);
x_3 = x_16;
x_4 = x_20;
goto _start;
}
else
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_4, 0);
lean::inc(x_22);
lean::dec(x_4);
x_25 = l_Lean_IR_addParamRename(x_22, x_13, x_14);
x_3 = x_16;
x_4 = x_25;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_addParamsRename(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::array_get_size(x_2);
x_5 = lean::nat_dec_eq(x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
if (x_5 == 0)
{
obj* x_9; 
lean::dec(x_0);
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_0);
x_11 = lean::mk_nat_obj(0ul);
x_12 = l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1(x_1, x_1, x_2, x_11, x_10);
return x_12;
}
}
}
obj* l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_IR_addParamsRename___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_addParamsRename(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
uint8 l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; uint8 x_13; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::dec(x_2);
x_13 = l_Lean_IR_CtorInfo_beq___main(x_3, x_8);
lean::dec(x_8);
lean::dec(x_3);
if (x_13 == 0)
{
uint8 x_19; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_10);
x_19 = 0;
return x_19;
}
else
{
uint8 x_20; 
x_20 = l_Lean_IR_FnBody_alphaEqv___main(x_0, x_5, x_10);
return x_20;
}
}
else
{
uint8 x_24; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_24 = 0;
return x_24;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_28; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_28 = 0;
return x_28;
}
else
{
obj* x_29; obj* x_32; uint8 x_35; 
x_29 = lean::cnstr_get(x_1, 0);
lean::inc(x_29);
lean::dec(x_1);
x_32 = lean::cnstr_get(x_2, 0);
lean::inc(x_32);
lean::dec(x_2);
x_35 = l_Lean_IR_FnBody_alphaEqv___main(x_0, x_29, x_32);
return x_35;
}
}
}
}
uint8 l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1___boxed), 3, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::array_get_size(x_1);
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
if (x_6 == 0)
{
uint8 x_10; 
lean::dec(x_3);
x_10 = 0;
return x_10;
}
else
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(0ul);
x_12 = l_Array_isEqvAux___main___rarg(x_1, x_2, lean::box(0), x_3, x_11);
return x_12;
}
}
}
uint8 l_Lean_IR_FnBody_alphaEqv___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
uint8 x_3; 
x_3 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; uint8 x_13; obj* x_14; obj* x_16; uint8 x_19; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
lean::dec(x_2);
x_19 = l_Lean_IR_IRType_beq___main(x_3, x_13);
if (x_19 == 0)
{
uint8 x_27; 
lean::dec(x_8);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_14);
lean::dec(x_16);
x_27 = 0;
return x_27;
}
else
{
uint8 x_29; 
lean::inc(x_0);
x_29 = l_Lean_IR_Expr_alphaEqv___main(x_0, x_6, x_14);
lean::dec(x_14);
lean::dec(x_6);
if (x_29 == 0)
{
uint8 x_37; 
lean::dec(x_8);
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_4);
lean::dec(x_16);
x_37 = 0;
return x_37;
}
else
{
obj* x_38; 
x_38 = l_Lean_IR_addVarRename(x_0, x_4, x_11);
x_0 = x_38;
x_1 = x_8;
x_2 = x_16;
goto _start;
}
}
}
case 12:
{
uint8 x_42; 
lean::dec(x_1);
lean::dec(x_0);
x_42 = 0;
return x_42;
}
default:
{
uint8 x_46; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_46 = 0;
return x_46;
}
}
}
case 1:
{
uint8 x_47; 
x_47 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_48; obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_59; uint8 x_61; obj* x_62; obj* x_64; obj* x_68; 
x_48 = lean::cnstr_get(x_1, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_1, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_1, 2);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_1, 3);
lean::inc(x_54);
lean::dec(x_1);
x_57 = lean::cnstr_get(x_2, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_2, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*4);
x_62 = lean::cnstr_get(x_2, 2);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_2, 3);
lean::inc(x_64);
lean::dec(x_2);
lean::inc(x_0);
x_68 = l_Lean_IR_addParamsRename(x_0, x_50, x_59);
lean::dec(x_59);
lean::dec(x_50);
if (lean::obj_tag(x_68) == 0)
{
uint8 x_78; 
lean::dec(x_0);
lean::dec(x_52);
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_62);
lean::dec(x_48);
lean::dec(x_57);
x_78 = 0;
return x_78;
}
else
{
obj* x_79; uint8 x_82; 
x_79 = lean::cnstr_get(x_68, 0);
lean::inc(x_79);
lean::dec(x_68);
x_82 = l_Lean_IR_IRType_beq___main(x_47, x_61);
if (x_82 == 0)
{
uint8 x_91; 
lean::dec(x_0);
lean::dec(x_79);
lean::dec(x_52);
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_62);
lean::dec(x_48);
lean::dec(x_57);
x_91 = 0;
return x_91;
}
else
{
uint8 x_92; 
x_92 = l_Lean_IR_FnBody_alphaEqv___main(x_79, x_52, x_62);
if (x_92 == 0)
{
uint8 x_98; 
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_48);
lean::dec(x_57);
x_98 = 0;
return x_98;
}
else
{
obj* x_99; 
x_99 = l_Lean_IR_addVarRename(x_0, x_48, x_57);
x_0 = x_99;
x_1 = x_54;
x_2 = x_64;
goto _start;
}
}
}
}
case 12:
{
uint8 x_103; 
lean::dec(x_1);
lean::dec(x_0);
x_103 = 0;
return x_103;
}
default:
{
uint8 x_107; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_107 = 0;
return x_107;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_108; obj* x_110; obj* x_112; obj* x_114; obj* x_117; obj* x_119; obj* x_121; obj* x_123; uint8 x_127; 
x_108 = lean::cnstr_get(x_1, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_1, 1);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_1, 2);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_1, 3);
lean::inc(x_114);
lean::dec(x_1);
x_117 = lean::cnstr_get(x_2, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_2, 1);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_2, 2);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_2, 3);
lean::inc(x_123);
lean::dec(x_2);
lean::inc(x_0);
x_127 = l_Lean_IR_VarId_alphaEqv(x_0, x_108, x_117);
lean::dec(x_117);
lean::dec(x_108);
if (x_127 == 0)
{
uint8 x_137; 
lean::dec(x_119);
lean::dec(x_121);
lean::dec(x_114);
lean::dec(x_110);
lean::dec(x_112);
lean::dec(x_0);
lean::dec(x_123);
x_137 = 0;
return x_137;
}
else
{
uint8 x_138; 
x_138 = lean::nat_dec_eq(x_110, x_119);
lean::dec(x_119);
lean::dec(x_110);
if (x_138 == 0)
{
uint8 x_146; 
lean::dec(x_121);
lean::dec(x_114);
lean::dec(x_112);
lean::dec(x_0);
lean::dec(x_123);
x_146 = 0;
return x_146;
}
else
{
uint8 x_148; 
lean::inc(x_0);
x_148 = l_Lean_IR_VarId_alphaEqv(x_0, x_112, x_121);
lean::dec(x_121);
lean::dec(x_112);
if (x_148 == 0)
{
uint8 x_154; 
lean::dec(x_114);
lean::dec(x_0);
lean::dec(x_123);
x_154 = 0;
return x_154;
}
else
{
x_1 = x_114;
x_2 = x_123;
goto _start;
}
}
}
}
case 12:
{
uint8 x_158; 
lean::dec(x_1);
lean::dec(x_0);
x_158 = 0;
return x_158;
}
default:
{
uint8 x_162; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_162 = 0;
return x_162;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_163; obj* x_165; obj* x_167; obj* x_169; obj* x_172; obj* x_174; obj* x_176; obj* x_178; uint8 x_182; 
x_163 = lean::cnstr_get(x_1, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_1, 1);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_1, 2);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_1, 3);
lean::inc(x_169);
lean::dec(x_1);
x_172 = lean::cnstr_get(x_2, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_2, 1);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_2, 2);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_2, 3);
lean::inc(x_178);
lean::dec(x_2);
lean::inc(x_0);
x_182 = l_Lean_IR_VarId_alphaEqv(x_0, x_163, x_172);
lean::dec(x_172);
lean::dec(x_163);
if (x_182 == 0)
{
uint8 x_192; 
lean::dec(x_0);
lean::dec(x_178);
lean::dec(x_176);
lean::dec(x_165);
lean::dec(x_174);
lean::dec(x_169);
lean::dec(x_167);
x_192 = 0;
return x_192;
}
else
{
uint8 x_193; 
x_193 = lean::nat_dec_eq(x_165, x_174);
lean::dec(x_174);
lean::dec(x_165);
if (x_193 == 0)
{
uint8 x_201; 
lean::dec(x_0);
lean::dec(x_178);
lean::dec(x_176);
lean::dec(x_169);
lean::dec(x_167);
x_201 = 0;
return x_201;
}
else
{
uint8 x_203; 
lean::inc(x_0);
x_203 = l_Lean_IR_VarId_alphaEqv(x_0, x_167, x_176);
lean::dec(x_176);
lean::dec(x_167);
if (x_203 == 0)
{
uint8 x_209; 
lean::dec(x_0);
lean::dec(x_178);
lean::dec(x_169);
x_209 = 0;
return x_209;
}
else
{
x_1 = x_169;
x_2 = x_178;
goto _start;
}
}
}
}
case 12:
{
uint8 x_213; 
lean::dec(x_1);
lean::dec(x_0);
x_213 = 0;
return x_213;
}
default:
{
uint8 x_217; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_217 = 0;
return x_217;
}
}
}
case 4:
{
uint8 x_218; 
x_218 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_219; obj* x_221; obj* x_223; obj* x_225; obj* x_227; obj* x_230; obj* x_232; obj* x_234; obj* x_236; uint8 x_238; obj* x_239; uint8 x_243; 
x_219 = lean::cnstr_get(x_1, 0);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_1, 1);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_1, 2);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_1, 3);
lean::inc(x_225);
x_227 = lean::cnstr_get(x_1, 4);
lean::inc(x_227);
lean::dec(x_1);
x_230 = lean::cnstr_get(x_2, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get(x_2, 1);
lean::inc(x_232);
x_234 = lean::cnstr_get(x_2, 2);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_2, 3);
lean::inc(x_236);
x_238 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_239 = lean::cnstr_get(x_2, 4);
lean::inc(x_239);
lean::dec(x_2);
lean::inc(x_0);
x_243 = l_Lean_IR_VarId_alphaEqv(x_0, x_219, x_230);
lean::dec(x_230);
lean::dec(x_219);
if (x_243 == 0)
{
uint8 x_255; 
lean::dec(x_239);
lean::dec(x_234);
lean::dec(x_232);
lean::dec(x_225);
lean::dec(x_236);
lean::dec(x_0);
lean::dec(x_223);
lean::dec(x_221);
lean::dec(x_227);
x_255 = 0;
return x_255;
}
else
{
uint8 x_256; 
x_256 = lean::nat_dec_eq(x_221, x_232);
lean::dec(x_232);
lean::dec(x_221);
if (x_256 == 0)
{
uint8 x_266; 
lean::dec(x_239);
lean::dec(x_234);
lean::dec(x_225);
lean::dec(x_236);
lean::dec(x_0);
lean::dec(x_223);
lean::dec(x_227);
x_266 = 0;
return x_266;
}
else
{
uint8 x_267; 
x_267 = lean::nat_dec_eq(x_223, x_234);
lean::dec(x_234);
lean::dec(x_223);
if (x_267 == 0)
{
uint8 x_275; 
lean::dec(x_239);
lean::dec(x_225);
lean::dec(x_236);
lean::dec(x_0);
lean::dec(x_227);
x_275 = 0;
return x_275;
}
else
{
uint8 x_277; 
lean::inc(x_0);
x_277 = l_Lean_IR_VarId_alphaEqv(x_0, x_225, x_236);
lean::dec(x_236);
lean::dec(x_225);
if (x_277 == 0)
{
uint8 x_283; 
lean::dec(x_239);
lean::dec(x_0);
lean::dec(x_227);
x_283 = 0;
return x_283;
}
else
{
uint8 x_284; 
x_284 = l_Lean_IR_IRType_beq___main(x_218, x_238);
if (x_284 == 0)
{
uint8 x_288; 
lean::dec(x_239);
lean::dec(x_0);
lean::dec(x_227);
x_288 = 0;
return x_288;
}
else
{
x_1 = x_227;
x_2 = x_239;
goto _start;
}
}
}
}
}
}
case 12:
{
uint8 x_292; 
lean::dec(x_1);
lean::dec(x_0);
x_292 = 0;
return x_292;
}
default:
{
uint8 x_296; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_296 = 0;
return x_296;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_297; obj* x_299; obj* x_301; obj* x_304; obj* x_306; obj* x_308; uint8 x_312; 
x_297 = lean::cnstr_get(x_1, 0);
lean::inc(x_297);
x_299 = lean::cnstr_get(x_1, 1);
lean::inc(x_299);
x_301 = lean::cnstr_get(x_1, 2);
lean::inc(x_301);
lean::dec(x_1);
x_304 = lean::cnstr_get(x_2, 0);
lean::inc(x_304);
x_306 = lean::cnstr_get(x_2, 1);
lean::inc(x_306);
x_308 = lean::cnstr_get(x_2, 2);
lean::inc(x_308);
lean::dec(x_2);
lean::inc(x_0);
x_312 = l_Lean_IR_VarId_alphaEqv(x_0, x_297, x_304);
lean::dec(x_304);
lean::dec(x_297);
if (x_312 == 0)
{
uint8 x_320; 
lean::dec(x_308);
lean::dec(x_299);
lean::dec(x_301);
lean::dec(x_306);
lean::dec(x_0);
x_320 = 0;
return x_320;
}
else
{
uint8 x_321; 
x_321 = lean::nat_dec_eq(x_299, x_306);
lean::dec(x_306);
lean::dec(x_299);
if (x_321 == 0)
{
uint8 x_327; 
lean::dec(x_308);
lean::dec(x_301);
lean::dec(x_0);
x_327 = 0;
return x_327;
}
else
{
x_1 = x_301;
x_2 = x_308;
goto _start;
}
}
}
case 12:
{
uint8 x_331; 
lean::dec(x_1);
lean::dec(x_0);
x_331 = 0;
return x_331;
}
default:
{
uint8 x_335; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_335 = 0;
return x_335;
}
}
}
case 6:
{
uint8 x_336; 
x_336 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_337; obj* x_339; obj* x_341; obj* x_344; obj* x_346; uint8 x_348; obj* x_349; uint8 x_353; 
x_337 = lean::cnstr_get(x_1, 0);
lean::inc(x_337);
x_339 = lean::cnstr_get(x_1, 1);
lean::inc(x_339);
x_341 = lean::cnstr_get(x_1, 2);
lean::inc(x_341);
lean::dec(x_1);
x_344 = lean::cnstr_get(x_2, 0);
lean::inc(x_344);
x_346 = lean::cnstr_get(x_2, 1);
lean::inc(x_346);
x_348 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_349 = lean::cnstr_get(x_2, 2);
lean::inc(x_349);
lean::dec(x_2);
lean::inc(x_0);
x_353 = l_Lean_IR_VarId_alphaEqv(x_0, x_337, x_344);
lean::dec(x_344);
lean::dec(x_337);
if (x_353 == 0)
{
uint8 x_361; 
lean::dec(x_0);
lean::dec(x_341);
lean::dec(x_346);
lean::dec(x_339);
lean::dec(x_349);
x_361 = 0;
return x_361;
}
else
{
uint8 x_362; 
x_362 = lean::nat_dec_eq(x_339, x_346);
lean::dec(x_346);
lean::dec(x_339);
if (x_362 == 0)
{
uint8 x_368; 
lean::dec(x_0);
lean::dec(x_341);
lean::dec(x_349);
x_368 = 0;
return x_368;
}
else
{
if (x_336 == 0)
{
if (x_348 == 0)
{
x_1 = x_341;
x_2 = x_349;
goto _start;
}
else
{
uint8 x_373; 
lean::dec(x_0);
lean::dec(x_341);
lean::dec(x_349);
x_373 = 0;
return x_373;
}
}
else
{
if (x_348 == 0)
{
uint8 x_377; 
lean::dec(x_0);
lean::dec(x_341);
lean::dec(x_349);
x_377 = 0;
return x_377;
}
else
{
x_1 = x_341;
x_2 = x_349;
goto _start;
}
}
}
}
}
case 12:
{
uint8 x_381; 
lean::dec(x_1);
lean::dec(x_0);
x_381 = 0;
return x_381;
}
default:
{
uint8 x_385; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_385 = 0;
return x_385;
}
}
}
case 7:
{
uint8 x_386; 
x_386 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_387; obj* x_389; obj* x_391; obj* x_394; obj* x_396; uint8 x_398; obj* x_399; uint8 x_403; 
x_387 = lean::cnstr_get(x_1, 0);
lean::inc(x_387);
x_389 = lean::cnstr_get(x_1, 1);
lean::inc(x_389);
x_391 = lean::cnstr_get(x_1, 2);
lean::inc(x_391);
lean::dec(x_1);
x_394 = lean::cnstr_get(x_2, 0);
lean::inc(x_394);
x_396 = lean::cnstr_get(x_2, 1);
lean::inc(x_396);
x_398 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_399 = lean::cnstr_get(x_2, 2);
lean::inc(x_399);
lean::dec(x_2);
lean::inc(x_0);
x_403 = l_Lean_IR_VarId_alphaEqv(x_0, x_387, x_394);
lean::dec(x_394);
lean::dec(x_387);
if (x_403 == 0)
{
uint8 x_411; 
lean::dec(x_391);
lean::dec(x_389);
lean::dec(x_396);
lean::dec(x_0);
lean::dec(x_399);
x_411 = 0;
return x_411;
}
else
{
uint8 x_412; 
x_412 = lean::nat_dec_eq(x_389, x_396);
lean::dec(x_396);
lean::dec(x_389);
if (x_412 == 0)
{
uint8 x_418; 
lean::dec(x_391);
lean::dec(x_0);
lean::dec(x_399);
x_418 = 0;
return x_418;
}
else
{
if (x_386 == 0)
{
if (x_398 == 0)
{
x_1 = x_391;
x_2 = x_399;
goto _start;
}
else
{
uint8 x_423; 
lean::dec(x_391);
lean::dec(x_0);
lean::dec(x_399);
x_423 = 0;
return x_423;
}
}
else
{
if (x_398 == 0)
{
uint8 x_427; 
lean::dec(x_391);
lean::dec(x_0);
lean::dec(x_399);
x_427 = 0;
return x_427;
}
else
{
x_1 = x_391;
x_2 = x_399;
goto _start;
}
}
}
}
}
case 12:
{
uint8 x_431; 
lean::dec(x_1);
lean::dec(x_0);
x_431 = 0;
return x_431;
}
default:
{
uint8 x_435; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_435 = 0;
return x_435;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_436; obj* x_438; obj* x_441; obj* x_443; uint8 x_446; 
x_436 = lean::cnstr_get(x_1, 0);
lean::inc(x_436);
x_438 = lean::cnstr_get(x_1, 1);
lean::inc(x_438);
lean::dec(x_1);
x_441 = lean::cnstr_get(x_2, 0);
lean::inc(x_441);
x_443 = lean::cnstr_get(x_2, 1);
lean::inc(x_443);
lean::dec(x_2);
x_446 = l_Lean_KVMap_eqv(x_436, x_441);
if (x_446 == 0)
{
uint8 x_450; 
lean::dec(x_443);
lean::dec(x_0);
lean::dec(x_438);
x_450 = 0;
return x_450;
}
else
{
x_1 = x_438;
x_2 = x_443;
goto _start;
}
}
case 12:
{
uint8 x_454; 
lean::dec(x_1);
lean::dec(x_0);
x_454 = 0;
return x_454;
}
default:
{
uint8 x_458; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_458 = 0;
return x_458;
}
}
}
case 9:
{
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_459; obj* x_461; obj* x_463; obj* x_466; obj* x_468; obj* x_470; uint8 x_473; 
x_459 = lean::cnstr_get(x_1, 0);
lean::inc(x_459);
x_461 = lean::cnstr_get(x_1, 1);
lean::inc(x_461);
x_463 = lean::cnstr_get(x_1, 2);
lean::inc(x_463);
lean::dec(x_1);
x_466 = lean::cnstr_get(x_2, 0);
lean::inc(x_466);
x_468 = lean::cnstr_get(x_2, 1);
lean::inc(x_468);
x_470 = lean::cnstr_get(x_2, 2);
lean::inc(x_470);
lean::dec(x_2);
x_473 = lean_name_dec_eq(x_459, x_466);
lean::dec(x_466);
lean::dec(x_459);
if (x_473 == 0)
{
uint8 x_481; 
lean::dec(x_0);
lean::dec(x_461);
lean::dec(x_463);
lean::dec(x_470);
lean::dec(x_468);
x_481 = 0;
return x_481;
}
else
{
uint8 x_483; 
lean::inc(x_0);
x_483 = l_Lean_IR_VarId_alphaEqv(x_0, x_461, x_468);
lean::dec(x_468);
lean::dec(x_461);
if (x_483 == 0)
{
uint8 x_489; 
lean::dec(x_0);
lean::dec(x_463);
lean::dec(x_470);
x_489 = 0;
return x_489;
}
else
{
uint8 x_490; 
x_490 = l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(x_0, x_463, x_470);
lean::dec(x_470);
lean::dec(x_463);
return x_490;
}
}
}
case 12:
{
uint8 x_495; 
lean::dec(x_1);
lean::dec(x_0);
x_495 = 0;
return x_495;
}
default:
{
uint8 x_499; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_499 = 0;
return x_499;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_500; obj* x_503; uint8 x_506; 
x_500 = lean::cnstr_get(x_1, 0);
lean::inc(x_500);
lean::dec(x_1);
x_503 = lean::cnstr_get(x_2, 0);
lean::inc(x_503);
lean::dec(x_2);
x_506 = l_Lean_IR_Arg_alphaEqv___main(x_0, x_500, x_503);
lean::dec(x_503);
lean::dec(x_500);
return x_506;
}
case 12:
{
uint8 x_511; 
lean::dec(x_1);
lean::dec(x_0);
x_511 = 0;
return x_511;
}
default:
{
uint8 x_515; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_515 = 0;
return x_515;
}
}
}
case 11:
{
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_516; obj* x_518; obj* x_521; obj* x_523; uint8 x_526; 
x_516 = lean::cnstr_get(x_1, 0);
lean::inc(x_516);
x_518 = lean::cnstr_get(x_1, 1);
lean::inc(x_518);
lean::dec(x_1);
x_521 = lean::cnstr_get(x_2, 0);
lean::inc(x_521);
x_523 = lean::cnstr_get(x_2, 1);
lean::inc(x_523);
lean::dec(x_2);
x_526 = lean::nat_dec_eq(x_516, x_521);
lean::dec(x_521);
lean::dec(x_516);
if (x_526 == 0)
{
uint8 x_532; 
lean::dec(x_0);
lean::dec(x_518);
lean::dec(x_523);
x_532 = 0;
return x_532;
}
else
{
uint8 x_533; 
x_533 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_518, x_523);
lean::dec(x_523);
lean::dec(x_518);
return x_533;
}
}
case 12:
{
uint8 x_538; 
lean::dec(x_1);
lean::dec(x_0);
x_538 = 0;
return x_538;
}
default:
{
uint8 x_542; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_542 = 0;
return x_542;
}
}
}
default:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 12:
{
uint8 x_544; 
x_544 = 1;
return x_544;
}
default:
{
uint8 x_546; 
lean::dec(x_2);
x_546 = 0;
return x_546;
}
}
}
}
}
}
obj* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
obj* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_FnBody_alphaEqv___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_FnBody_alphaEqv___main(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_FnBody_alphaEqv(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_IR_FnBody_alphaEqv___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_FnBody_alphaEqv___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Lean_IR_FnBody_alphaEqv(x_0, x_1, x_2);
x_4 = lean::box(x_3);
return x_4;
}
}
uint8 l_Lean_IR_FnBody_beq(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::box(0);
x_3 = l_Lean_IR_FnBody_alphaEqv___main(x_2, x_0, x_1);
return x_3;
}
}
obj* l_Lean_IR_FnBody_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_FnBody_beq(x_0, x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init_l_Lean_IR_FnBody_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_FnBody_beq___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_IR_vsetInh() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_basic_1__skip___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_basic_1__skip(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_basic_1__skip___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_basic_1__skip___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_basic_1__skip___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_basic_1__skip___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_basic_1__skip(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 3);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::nat_dec_lt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = lean::nat_dec_lt(x_5, x_1);
if (x_14 == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_9);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_7);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
else
{
lean::dec(x_7);
lean::dec(x_5);
x_0 = x_9;
goto _start;
}
}
else
{
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_5);
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = lean::nat_dec_lt(x_1, x_9);
if (x_16 == 0)
{
uint8 x_17; 
x_17 = lean::nat_dec_lt(x_9, x_1);
if (x_17 == 0)
{
obj* x_20; obj* x_21; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_7);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_2);
lean::cnstr_set(x_20, 3, x_13);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_6);
x_21 = x_20;
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_7);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_11);
lean::cnstr_set(x_23, 3, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*4, x_6);
x_24 = x_23;
return x_24;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; 
x_25 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_15;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
lean::cnstr_set(x_26, 2, x_11);
lean::cnstr_set(x_26, 3, x_13);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_6);
x_27 = x_26;
return x_27;
}
}
else
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint8 x_37; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
x_37 = lean::nat_dec_lt(x_1, x_30);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = lean::nat_dec_lt(x_30, x_1);
if (x_38 == 0)
{
obj* x_41; obj* x_42; 
lean::dec(x_32);
lean::dec(x_30);
if (lean::is_scalar(x_36)) {
 x_41 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_41 = x_36;
}
lean::cnstr_set(x_41, 0, x_28);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_2);
lean::cnstr_set(x_41, 3, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*4, x_6);
x_42 = x_41;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_RBNode_isRed___main___rarg(x_34);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_36;
}
lean::cnstr_set(x_45, 0, x_28);
lean::cnstr_set(x_45, 1, x_30);
lean::cnstr_set(x_45, 2, x_32);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
obj* x_47; 
x_47 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(x_34, x_1, x_2);
if (lean::obj_tag(x_47) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_28);
return x_47;
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; 
x_54 = lean::cnstr_get(x_47, 3);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_58; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; uint8 x_64; obj* x_65; obj* x_66; 
x_56 = lean::cnstr_get(x_47, 1);
x_58 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_60 = x_47;
} else {
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
x_61 = 0;
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_54);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_58);
lean::cnstr_set(x_62, 3, x_54);
lean::cnstr_set_scalar(x_62, sizeof(void*)*4, x_61);
x_63 = x_62;
x_64 = 1;
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_65 = x_36;
}
lean::cnstr_set(x_65, 0, x_28);
lean::cnstr_set(x_65, 1, x_30);
lean::cnstr_set(x_65, 2, x_32);
lean::cnstr_set(x_65, 3, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*4, x_64);
x_66 = x_65;
return x_66;
}
else
{
uint8 x_67; 
x_67 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*4);
if (x_67 == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_68 = lean::cnstr_get(x_47, 1);
x_70 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_72 = x_47;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_47);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_54, 0);
x_75 = lean::cnstr_get(x_54, 1);
x_77 = lean::cnstr_get(x_54, 2);
x_79 = lean::cnstr_get(x_54, 3);
if (lean::is_exclusive(x_54)) {
 x_81 = x_54;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_54);
 x_81 = lean::box(0);
}
x_82 = 1;
if (lean::is_scalar(x_81)) {
 x_83 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_83 = x_81;
}
lean::cnstr_set(x_83, 0, x_28);
lean::cnstr_set(x_83, 1, x_30);
lean::cnstr_set(x_83, 2, x_32);
lean::cnstr_set(x_83, 3, x_52);
lean::cnstr_set_scalar(x_83, sizeof(void*)*4, x_82);
x_84 = x_83;
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_85 = x_72;
}
lean::cnstr_set(x_85, 0, x_73);
lean::cnstr_set(x_85, 1, x_75);
lean::cnstr_set(x_85, 2, x_77);
lean::cnstr_set(x_85, 3, x_79);
lean::cnstr_set_scalar(x_85, sizeof(void*)*4, x_82);
x_86 = x_85;
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_70);
lean::cnstr_set(x_87, 3, x_86);
lean::cnstr_set_scalar(x_87, sizeof(void*)*4, x_67);
x_88 = x_87;
return x_88;
}
else
{
obj* x_89; obj* x_91; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
x_89 = lean::cnstr_get(x_47, 1);
x_91 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_93 = x_47;
} else {
 lean::inc(x_89);
 lean::inc(x_91);
 lean::dec(x_47);
 x_93 = lean::box(0);
}
x_94 = 0;
if (lean::is_scalar(x_93)) {
 x_95 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_95 = x_93;
}
lean::cnstr_set(x_95, 0, x_52);
lean::cnstr_set(x_95, 1, x_89);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_54);
lean::cnstr_set_scalar(x_95, sizeof(void*)*4, x_94);
x_96 = x_95;
if (lean::is_scalar(x_36)) {
 x_97 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_97 = x_36;
}
lean::cnstr_set(x_97, 0, x_28);
lean::cnstr_set(x_97, 1, x_30);
lean::cnstr_set(x_97, 2, x_32);
lean::cnstr_set(x_97, 3, x_96);
lean::cnstr_set_scalar(x_97, sizeof(void*)*4, x_67);
x_98 = x_97;
return x_98;
}
}
}
else
{
uint8 x_99; 
x_99 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*4);
if (x_99 == 0)
{
obj* x_100; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_113; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_100 = lean::cnstr_get(x_47, 1);
x_102 = lean::cnstr_get(x_47, 2);
x_104 = lean::cnstr_get(x_47, 3);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_106 = x_47;
} else {
 lean::inc(x_100);
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_47);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_52, 0);
x_109 = lean::cnstr_get(x_52, 1);
x_111 = lean::cnstr_get(x_52, 2);
x_113 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_115 = x_52;
} else {
 lean::inc(x_107);
 lean::inc(x_109);
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_52);
 x_115 = lean::box(0);
}
x_116 = 1;
if (lean::is_scalar(x_115)) {
 x_117 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_117 = x_115;
}
lean::cnstr_set(x_117, 0, x_28);
lean::cnstr_set(x_117, 1, x_30);
lean::cnstr_set(x_117, 2, x_32);
lean::cnstr_set(x_117, 3, x_107);
lean::cnstr_set_scalar(x_117, sizeof(void*)*4, x_116);
x_118 = x_117;
if (lean::is_scalar(x_106)) {
 x_119 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_119 = x_106;
}
lean::cnstr_set(x_119, 0, x_113);
lean::cnstr_set(x_119, 1, x_100);
lean::cnstr_set(x_119, 2, x_102);
lean::cnstr_set(x_119, 3, x_104);
lean::cnstr_set_scalar(x_119, sizeof(void*)*4, x_116);
x_120 = x_119;
if (lean::is_scalar(x_36)) {
 x_121 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_121 = x_36;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set(x_121, 1, x_109);
lean::cnstr_set(x_121, 2, x_111);
lean::cnstr_set(x_121, 3, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*4, x_99);
x_122 = x_121;
return x_122;
}
else
{
obj* x_123; 
x_123 = lean::cnstr_get(x_47, 3);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_125; obj* x_127; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_125 = lean::cnstr_get(x_47, 1);
x_127 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_129 = x_47;
} else {
 lean::inc(x_125);
 lean::inc(x_127);
 lean::dec(x_47);
 x_129 = lean::box(0);
}
x_130 = 0;
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_52);
lean::cnstr_set(x_131, 1, x_125);
lean::cnstr_set(x_131, 2, x_127);
lean::cnstr_set(x_131, 3, x_123);
lean::cnstr_set_scalar(x_131, sizeof(void*)*4, x_130);
x_132 = x_131;
if (lean::is_scalar(x_36)) {
 x_133 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_133 = x_36;
}
lean::cnstr_set(x_133, 0, x_28);
lean::cnstr_set(x_133, 1, x_30);
lean::cnstr_set(x_133, 2, x_32);
lean::cnstr_set(x_133, 3, x_132);
lean::cnstr_set_scalar(x_133, sizeof(void*)*4, x_99);
x_134 = x_133;
return x_134;
}
else
{
uint8 x_135; 
x_135 = lean::cnstr_get_scalar<uint8>(x_123, sizeof(void*)*4);
if (x_135 == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; obj* x_150; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_36);
x_137 = lean::cnstr_get(x_47, 1);
x_139 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_141 = x_47;
} else {
 lean::inc(x_137);
 lean::inc(x_139);
 lean::dec(x_47);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_123, 0);
x_144 = lean::cnstr_get(x_123, 1);
x_146 = lean::cnstr_get(x_123, 2);
x_148 = lean::cnstr_get(x_123, 3);
if (lean::is_exclusive(x_123)) {
 x_150 = x_123;
} else {
 lean::inc(x_142);
 lean::inc(x_144);
 lean::inc(x_146);
 lean::inc(x_148);
 lean::dec(x_123);
 x_150 = lean::box(0);
}
lean::inc(x_52);
if (lean::is_scalar(x_150)) {
 x_152 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_152 = x_150;
}
lean::cnstr_set(x_152, 0, x_28);
lean::cnstr_set(x_152, 1, x_30);
lean::cnstr_set(x_152, 2, x_32);
lean::cnstr_set(x_152, 3, x_52);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 lean::cnstr_release(x_52, 2);
 lean::cnstr_release(x_52, 3);
 x_153 = x_52;
} else {
 lean::dec(x_52);
 x_153 = lean::box(0);
}
lean::cnstr_set_scalar(x_152, sizeof(void*)*4, x_99);
x_154 = x_152;
if (lean::is_scalar(x_153)) {
 x_155 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_155 = x_153;
}
lean::cnstr_set(x_155, 0, x_142);
lean::cnstr_set(x_155, 1, x_144);
lean::cnstr_set(x_155, 2, x_146);
lean::cnstr_set(x_155, 3, x_148);
lean::cnstr_set_scalar(x_155, sizeof(void*)*4, x_99);
x_156 = x_155;
if (lean::is_scalar(x_141)) {
 x_157 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_157 = x_141;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_137);
lean::cnstr_set(x_157, 2, x_139);
lean::cnstr_set(x_157, 3, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*4, x_135);
x_158 = x_157;
return x_158;
}
else
{
obj* x_159; obj* x_161; obj* x_163; obj* x_164; obj* x_166; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_159 = lean::cnstr_get(x_47, 1);
x_161 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 3);
 x_163 = x_47;
} else {
 lean::inc(x_159);
 lean::inc(x_161);
 lean::dec(x_47);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_52, 0);
x_166 = lean::cnstr_get(x_52, 1);
x_168 = lean::cnstr_get(x_52, 2);
x_170 = lean::cnstr_get(x_52, 3);
if (lean::is_exclusive(x_52)) {
 x_172 = x_52;
} else {
 lean::inc(x_164);
 lean::inc(x_166);
 lean::inc(x_168);
 lean::inc(x_170);
 lean::dec(x_52);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_164);
lean::cnstr_set(x_173, 1, x_166);
lean::cnstr_set(x_173, 2, x_168);
lean::cnstr_set(x_173, 3, x_170);
lean::cnstr_set_scalar(x_173, sizeof(void*)*4, x_135);
x_174 = x_173;
x_175 = 0;
if (lean::is_scalar(x_163)) {
 x_176 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_176 = x_163;
}
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set(x_176, 1, x_159);
lean::cnstr_set(x_176, 2, x_161);
lean::cnstr_set(x_176, 3, x_123);
lean::cnstr_set_scalar(x_176, sizeof(void*)*4, x_175);
x_177 = x_176;
if (lean::is_scalar(x_36)) {
 x_178 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_178 = x_36;
}
lean::cnstr_set(x_178, 0, x_28);
lean::cnstr_set(x_178, 1, x_30);
lean::cnstr_set(x_178, 2, x_32);
lean::cnstr_set(x_178, 3, x_177);
lean::cnstr_set_scalar(x_178, sizeof(void*)*4, x_135);
x_179 = x_178;
return x_179;
}
}
}
}
}
}
}
}
else
{
uint8 x_180; 
x_180 = l_RBNode_isRed___main___rarg(x_28);
if (x_180 == 0)
{
obj* x_181; obj* x_182; obj* x_183; 
x_181 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_182 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_182 = x_36;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_30);
lean::cnstr_set(x_182, 2, x_32);
lean::cnstr_set(x_182, 3, x_34);
lean::cnstr_set_scalar(x_182, sizeof(void*)*4, x_6);
x_183 = x_182;
return x_183;
}
else
{
obj* x_184; 
x_184 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(x_28, x_1, x_2);
if (lean::obj_tag(x_184) == 0)
{
lean::dec(x_32);
lean::dec(x_36);
lean::dec(x_30);
lean::dec(x_34);
return x_184;
}
else
{
obj* x_189; 
x_189 = lean::cnstr_get(x_184, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; 
x_191 = lean::cnstr_get(x_184, 3);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_193; obj* x_195; obj* x_197; uint8 x_198; obj* x_199; obj* x_200; uint8 x_201; obj* x_202; obj* x_203; 
x_193 = lean::cnstr_get(x_184, 1);
x_195 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_197 = x_184;
} else {
 lean::inc(x_193);
 lean::inc(x_195);
 lean::dec(x_184);
 x_197 = lean::box(0);
}
x_198 = 0;
if (lean::is_scalar(x_197)) {
 x_199 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_199 = x_197;
}
lean::cnstr_set(x_199, 0, x_191);
lean::cnstr_set(x_199, 1, x_193);
lean::cnstr_set(x_199, 2, x_195);
lean::cnstr_set(x_199, 3, x_191);
lean::cnstr_set_scalar(x_199, sizeof(void*)*4, x_198);
x_200 = x_199;
x_201 = 1;
if (lean::is_scalar(x_36)) {
 x_202 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_202 = x_36;
}
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_30);
lean::cnstr_set(x_202, 2, x_32);
lean::cnstr_set(x_202, 3, x_34);
lean::cnstr_set_scalar(x_202, sizeof(void*)*4, x_201);
x_203 = x_202;
return x_203;
}
else
{
uint8 x_204; 
x_204 = lean::cnstr_get_scalar<uint8>(x_191, sizeof(void*)*4);
if (x_204 == 0)
{
obj* x_205; obj* x_207; obj* x_209; obj* x_210; obj* x_212; obj* x_214; obj* x_216; obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_205 = lean::cnstr_get(x_184, 1);
x_207 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_209 = x_184;
} else {
 lean::inc(x_205);
 lean::inc(x_207);
 lean::dec(x_184);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_191, 0);
x_212 = lean::cnstr_get(x_191, 1);
x_214 = lean::cnstr_get(x_191, 2);
x_216 = lean::cnstr_get(x_191, 3);
if (lean::is_exclusive(x_191)) {
 x_218 = x_191;
} else {
 lean::inc(x_210);
 lean::inc(x_212);
 lean::inc(x_214);
 lean::inc(x_216);
 lean::dec(x_191);
 x_218 = lean::box(0);
}
x_219 = 1;
if (lean::is_scalar(x_218)) {
 x_220 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_220 = x_218;
}
lean::cnstr_set(x_220, 0, x_189);
lean::cnstr_set(x_220, 1, x_205);
lean::cnstr_set(x_220, 2, x_207);
lean::cnstr_set(x_220, 3, x_210);
lean::cnstr_set_scalar(x_220, sizeof(void*)*4, x_219);
x_221 = x_220;
if (lean::is_scalar(x_209)) {
 x_222 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_222 = x_209;
}
lean::cnstr_set(x_222, 0, x_216);
lean::cnstr_set(x_222, 1, x_30);
lean::cnstr_set(x_222, 2, x_32);
lean::cnstr_set(x_222, 3, x_34);
lean::cnstr_set_scalar(x_222, sizeof(void*)*4, x_219);
x_223 = x_222;
if (lean::is_scalar(x_36)) {
 x_224 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_224 = x_36;
}
lean::cnstr_set(x_224, 0, x_221);
lean::cnstr_set(x_224, 1, x_212);
lean::cnstr_set(x_224, 2, x_214);
lean::cnstr_set(x_224, 3, x_223);
lean::cnstr_set_scalar(x_224, sizeof(void*)*4, x_204);
x_225 = x_224;
return x_225;
}
else
{
obj* x_226; obj* x_228; obj* x_230; uint8 x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_184, 1);
x_228 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_230 = x_184;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::dec(x_184);
 x_230 = lean::box(0);
}
x_231 = 0;
if (lean::is_scalar(x_230)) {
 x_232 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_232 = x_230;
}
lean::cnstr_set(x_232, 0, x_189);
lean::cnstr_set(x_232, 1, x_226);
lean::cnstr_set(x_232, 2, x_228);
lean::cnstr_set(x_232, 3, x_191);
lean::cnstr_set_scalar(x_232, sizeof(void*)*4, x_231);
x_233 = x_232;
if (lean::is_scalar(x_36)) {
 x_234 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_234 = x_36;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_30);
lean::cnstr_set(x_234, 2, x_32);
lean::cnstr_set(x_234, 3, x_34);
lean::cnstr_set_scalar(x_234, sizeof(void*)*4, x_204);
x_235 = x_234;
return x_235;
}
}
}
else
{
uint8 x_236; 
x_236 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*4);
if (x_236 == 0)
{
obj* x_237; obj* x_239; obj* x_241; obj* x_243; obj* x_244; obj* x_246; obj* x_248; obj* x_250; obj* x_252; uint8 x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
x_237 = lean::cnstr_get(x_184, 1);
x_239 = lean::cnstr_get(x_184, 2);
x_241 = lean::cnstr_get(x_184, 3);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 x_243 = x_184;
} else {
 lean::inc(x_237);
 lean::inc(x_239);
 lean::inc(x_241);
 lean::dec(x_184);
 x_243 = lean::box(0);
}
x_244 = lean::cnstr_get(x_189, 0);
x_246 = lean::cnstr_get(x_189, 1);
x_248 = lean::cnstr_get(x_189, 2);
x_250 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_252 = x_189;
} else {
 lean::inc(x_244);
 lean::inc(x_246);
 lean::inc(x_248);
 lean::inc(x_250);
 lean::dec(x_189);
 x_252 = lean::box(0);
}
x_253 = 1;
if (lean::is_scalar(x_252)) {
 x_254 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_254 = x_252;
}
lean::cnstr_set(x_254, 0, x_244);
lean::cnstr_set(x_254, 1, x_246);
lean::cnstr_set(x_254, 2, x_248);
lean::cnstr_set(x_254, 3, x_250);
lean::cnstr_set_scalar(x_254, sizeof(void*)*4, x_253);
x_255 = x_254;
if (lean::is_scalar(x_243)) {
 x_256 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_256 = x_243;
}
lean::cnstr_set(x_256, 0, x_241);
lean::cnstr_set(x_256, 1, x_30);
lean::cnstr_set(x_256, 2, x_32);
lean::cnstr_set(x_256, 3, x_34);
lean::cnstr_set_scalar(x_256, sizeof(void*)*4, x_253);
x_257 = x_256;
if (lean::is_scalar(x_36)) {
 x_258 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_258 = x_36;
}
lean::cnstr_set(x_258, 0, x_255);
lean::cnstr_set(x_258, 1, x_237);
lean::cnstr_set(x_258, 2, x_239);
lean::cnstr_set(x_258, 3, x_257);
lean::cnstr_set_scalar(x_258, sizeof(void*)*4, x_236);
x_259 = x_258;
return x_259;
}
else
{
obj* x_260; 
x_260 = lean::cnstr_get(x_184, 3);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_266; uint8 x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; 
x_262 = lean::cnstr_get(x_184, 1);
x_264 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_266 = x_184;
} else {
 lean::inc(x_262);
 lean::inc(x_264);
 lean::dec(x_184);
 x_266 = lean::box(0);
}
x_267 = 0;
if (lean::is_scalar(x_266)) {
 x_268 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_268 = x_266;
}
lean::cnstr_set(x_268, 0, x_189);
lean::cnstr_set(x_268, 1, x_262);
lean::cnstr_set(x_268, 2, x_264);
lean::cnstr_set(x_268, 3, x_260);
lean::cnstr_set_scalar(x_268, sizeof(void*)*4, x_267);
x_269 = x_268;
if (lean::is_scalar(x_36)) {
 x_270 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_270 = x_36;
}
lean::cnstr_set(x_270, 0, x_269);
lean::cnstr_set(x_270, 1, x_30);
lean::cnstr_set(x_270, 2, x_32);
lean::cnstr_set(x_270, 3, x_34);
lean::cnstr_set_scalar(x_270, sizeof(void*)*4, x_236);
x_271 = x_270;
return x_271;
}
else
{
uint8 x_272; 
x_272 = lean::cnstr_get_scalar<uint8>(x_260, sizeof(void*)*4);
if (x_272 == 0)
{
obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_281; obj* x_283; obj* x_285; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
lean::dec(x_36);
x_274 = lean::cnstr_get(x_184, 1);
x_276 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_278 = x_184;
} else {
 lean::inc(x_274);
 lean::inc(x_276);
 lean::dec(x_184);
 x_278 = lean::box(0);
}
x_279 = lean::cnstr_get(x_260, 0);
x_281 = lean::cnstr_get(x_260, 1);
x_283 = lean::cnstr_get(x_260, 2);
x_285 = lean::cnstr_get(x_260, 3);
if (lean::is_exclusive(x_260)) {
 x_287 = x_260;
} else {
 lean::inc(x_279);
 lean::inc(x_281);
 lean::inc(x_283);
 lean::inc(x_285);
 lean::dec(x_260);
 x_287 = lean::box(0);
}
lean::inc(x_189);
if (lean::is_scalar(x_287)) {
 x_289 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_289 = x_287;
}
lean::cnstr_set(x_289, 0, x_189);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_276);
lean::cnstr_set(x_289, 3, x_279);
if (lean::is_exclusive(x_189)) {
 lean::cnstr_release(x_189, 0);
 lean::cnstr_release(x_189, 1);
 lean::cnstr_release(x_189, 2);
 lean::cnstr_release(x_189, 3);
 x_290 = x_189;
} else {
 lean::dec(x_189);
 x_290 = lean::box(0);
}
lean::cnstr_set_scalar(x_289, sizeof(void*)*4, x_236);
x_291 = x_289;
if (lean::is_scalar(x_290)) {
 x_292 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_292 = x_290;
}
lean::cnstr_set(x_292, 0, x_285);
lean::cnstr_set(x_292, 1, x_30);
lean::cnstr_set(x_292, 2, x_32);
lean::cnstr_set(x_292, 3, x_34);
lean::cnstr_set_scalar(x_292, sizeof(void*)*4, x_236);
x_293 = x_292;
if (lean::is_scalar(x_278)) {
 x_294 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_294 = x_278;
}
lean::cnstr_set(x_294, 0, x_291);
lean::cnstr_set(x_294, 1, x_281);
lean::cnstr_set(x_294, 2, x_283);
lean::cnstr_set(x_294, 3, x_293);
lean::cnstr_set_scalar(x_294, sizeof(void*)*4, x_272);
x_295 = x_294;
return x_295;
}
else
{
obj* x_296; obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_307; obj* x_309; obj* x_310; obj* x_311; uint8 x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_296 = lean::cnstr_get(x_184, 1);
x_298 = lean::cnstr_get(x_184, 2);
if (lean::is_exclusive(x_184)) {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 3);
 x_300 = x_184;
} else {
 lean::inc(x_296);
 lean::inc(x_298);
 lean::dec(x_184);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_189, 0);
x_303 = lean::cnstr_get(x_189, 1);
x_305 = lean::cnstr_get(x_189, 2);
x_307 = lean::cnstr_get(x_189, 3);
if (lean::is_exclusive(x_189)) {
 x_309 = x_189;
} else {
 lean::inc(x_301);
 lean::inc(x_303);
 lean::inc(x_305);
 lean::inc(x_307);
 lean::dec(x_189);
 x_309 = lean::box(0);
}
if (lean::is_scalar(x_309)) {
 x_310 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_310 = x_309;
}
lean::cnstr_set(x_310, 0, x_301);
lean::cnstr_set(x_310, 1, x_303);
lean::cnstr_set(x_310, 2, x_305);
lean::cnstr_set(x_310, 3, x_307);
lean::cnstr_set_scalar(x_310, sizeof(void*)*4, x_272);
x_311 = x_310;
x_312 = 0;
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_313 = x_300;
}
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_296);
lean::cnstr_set(x_313, 2, x_298);
lean::cnstr_set(x_313, 3, x_260);
lean::cnstr_set_scalar(x_313, sizeof(void*)*4, x_312);
x_314 = x_313;
if (lean::is_scalar(x_36)) {
 x_315 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_315 = x_36;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_30);
lean::cnstr_set(x_315, 2, x_32);
lean::cnstr_set(x_315, 3, x_34);
lean::cnstr_set_scalar(x_315, sizeof(void*)*4, x_272);
x_316 = x_315;
return x_316;
}
}
}
}
}
}
}
}
}
}
}
obj* l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__3(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_2__collectIndex(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_0, x_4);
return x_5;
}
else
{
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
}
}
obj* l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_3__collectVar(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_0, x_4);
return x_5;
}
else
{
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_4__collectJP(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_0, x_4);
return x_5;
}
else
{
lean::dec(x_3);
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_5__withIndex(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_0, x_4);
x_6 = lean::apply_2(x_1, x_5, x_3);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_basic_6__withVar(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_0, x_4);
x_6 = lean::apply_2(x_1, x_5, x_3);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_basic_7__withJP(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::box(0);
x_5 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_0, x_4);
x_6 = lean::apply_2(x_1, x_5, x_3);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_FreeVariables_insertParams___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_15 = lean::box(0);
x_16 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_3, x_9, x_15);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
}
}
obj* l_Lean_IR_FreeVariables_insertParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at_Lean_IR_FreeVariables_insertParams___spec__1(x_1, x_1, x_2, x_0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_FreeVariables_insertParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_FreeVariables_insertParams___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_FreeVariables_insertParams___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_FreeVariables_insertParams(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_8__withParams(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at_Lean_IR_FreeVariables_insertParams___spec__1(x_0, x_0, x_4, x_2);
x_6 = lean::apply_2(x_1, x_5, x_3);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_basic_8__withParams___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_basic_8__withParams(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_basic_9__seq(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::apply_2(x_1, x_2, x_5);
return x_6;
}
}
obj* _init_l_Lean_IR_FreeVariables_HasAndthen() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_basic_9__seq), 4, 0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_basic_10__collectArg___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_3, x_7);
return x_8;
}
else
{
lean::dec(x_6);
lean::dec(x_3);
return x_2;
}
}
else
{
lean::dec(x_1);
return x_2;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_10__collectArg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_basic_10__collectArg___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
else
{
obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::array_fget(x_3, x_4);
lean::inc(x_2);
lean::inc(x_1);
x_15 = lean::apply_3(x_1, x_12, x_2, x_5);
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_4, x_16);
lean::dec(x_4);
x_4 = x_17;
x_5 = x_15;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___rarg(x_0, x_1, x_2, x_0, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_basic_11__collectArray___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_3);
return x_6;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_11__collectArray___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_basic_11__collectArray___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_basic_11__collectArray(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_fget(x_2, x_3);
lean::inc(x_1);
x_12 = l___private_init_lean_compiler_ir_basic_10__collectArg___main(x_10, x_1, x_4);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_0, x_1, x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_basic_12__collectArgs(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_0, x_1, x_0, x_3, x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_basic_12__collectArgs___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_basic_12__collectArgs(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_basic_13__collectExpr___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_3, x_7);
return x_8;
}
else
{
lean::dec(x_3);
lean::dec(x_6);
return x_2;
}
}
case 2:
{
obj* x_11; obj* x_13; obj* x_17; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 2);
lean::inc(x_13);
lean::dec(x_0);
lean::inc(x_1);
x_17 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_11);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_18 = lean::box(0);
x_19 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_11, x_18);
x_20 = lean::mk_nat_obj(0ul);
x_21 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_13, x_1, x_13, x_20, x_19);
lean::dec(x_13);
return x_21;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_11);
lean::dec(x_17);
x_25 = lean::mk_nat_obj(0ul);
x_26 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_13, x_1, x_13, x_25, x_2);
lean::dec(x_13);
return x_26;
}
}
case 3:
{
obj* x_28; obj* x_31; 
x_28 = lean::cnstr_get(x_0, 1);
lean::inc(x_28);
lean::dec(x_0);
x_31 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_28);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; obj* x_33; 
x_32 = lean::box(0);
x_33 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_28, x_32);
return x_33;
}
else
{
lean::dec(x_28);
lean::dec(x_31);
return x_2;
}
}
case 4:
{
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_0, 1);
lean::inc(x_36);
lean::dec(x_0);
x_39 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_36);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_41; 
x_40 = lean::box(0);
x_41 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_36, x_40);
return x_41;
}
else
{
lean::dec(x_36);
lean::dec(x_39);
return x_2;
}
}
case 5:
{
obj* x_44; obj* x_47; 
x_44 = lean::cnstr_get(x_0, 2);
lean::inc(x_44);
lean::dec(x_0);
x_47 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_44);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; 
x_48 = lean::box(0);
x_49 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_44, x_48);
return x_49;
}
else
{
lean::dec(x_47);
lean::dec(x_44);
return x_2;
}
}
case 8:
{
obj* x_52; obj* x_54; obj* x_58; 
x_52 = lean::cnstr_get(x_0, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_0, 1);
lean::inc(x_54);
lean::dec(x_0);
lean::inc(x_1);
x_58 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_52);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_59 = lean::box(0);
x_60 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_52, x_59);
x_61 = lean::mk_nat_obj(0ul);
x_62 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_54, x_1, x_54, x_61, x_60);
lean::dec(x_54);
return x_62;
}
else
{
obj* x_66; obj* x_67; 
lean::dec(x_52);
lean::dec(x_58);
x_66 = lean::mk_nat_obj(0ul);
x_67 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_54, x_1, x_54, x_66, x_2);
lean::dec(x_54);
return x_67;
}
}
case 9:
{
obj* x_69; obj* x_72; 
x_69 = lean::cnstr_get(x_0, 0);
lean::inc(x_69);
lean::dec(x_0);
x_72 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_69);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_74; 
x_73 = lean::box(0);
x_74 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_69, x_73);
return x_74;
}
else
{
lean::dec(x_69);
lean::dec(x_72);
return x_2;
}
}
case 10:
{
obj* x_77; obj* x_80; 
x_77 = lean::cnstr_get(x_0, 0);
lean::inc(x_77);
lean::dec(x_0);
x_80 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_77);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; obj* x_82; 
x_81 = lean::box(0);
x_82 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_77, x_81);
return x_82;
}
else
{
lean::dec(x_80);
lean::dec(x_77);
return x_2;
}
}
case 11:
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
case 12:
{
obj* x_87; obj* x_90; 
x_87 = lean::cnstr_get(x_0, 0);
lean::inc(x_87);
lean::dec(x_0);
x_90 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_87);
if (lean::obj_tag(x_90) == 0)
{
obj* x_91; obj* x_92; 
x_91 = lean::box(0);
x_92 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_87, x_91);
return x_92;
}
else
{
lean::dec(x_90);
lean::dec(x_87);
return x_2;
}
}
case 13:
{
obj* x_95; obj* x_98; 
x_95 = lean::cnstr_get(x_0, 0);
lean::inc(x_95);
lean::dec(x_0);
x_98 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_95);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; obj* x_100; 
x_99 = lean::box(0);
x_100 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_95, x_99);
return x_100;
}
else
{
lean::dec(x_98);
lean::dec(x_95);
return x_2;
}
}
default:
{
obj* x_103; obj* x_106; obj* x_107; 
x_103 = lean::cnstr_get(x_0, 1);
lean::inc(x_103);
lean::dec(x_0);
x_106 = lean::mk_nat_obj(0ul);
x_107 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_103, x_1, x_103, x_106, x_2);
lean::dec(x_103);
return x_107;
}
}
}
}
obj* l___private_init_lean_compiler_ir_basic_13__collectExpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_basic_13__collectExpr___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
else
{
obj* x_12; obj* x_13; obj* x_17; obj* x_18; obj* x_19; 
x_12 = lean::array_fget(x_3, x_4);
x_13 = l_Lean_IR_AltCore_body___main(x_12);
lean::dec(x_12);
lean::inc(x_2);
lean::inc(x_0);
x_17 = lean::apply_3(x_0, x_13, x_2, x_5);
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_4, x_18);
lean::dec(x_4);
x_4 = x_19;
x_5 = x_17;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2(x_0, x_1, x_2, x_1, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_basic_14__collectAlts(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2(x_0, x_1, x_2, x_1, x_4, x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_3);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_basic_11__collectArray___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_basic_14__collectAlts___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_basic_14__collectAlts(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_IR_FreeVariables_collectFnBody___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_FreeVariables_collectFnBody___main), 3, 0);
return x_0;
}
}
obj* l_Lean_IR_FreeVariables_collectFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
lean::inc(x_1);
x_11 = l___private_init_lean_compiler_ir_basic_13__collectExpr___main(x_5, x_1, x_2);
x_12 = lean::box(0);
x_13 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_1, x_3, x_12);
x_0 = x_7;
x_1 = x_13;
x_2 = x_11;
goto _start;
}
case 1:
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_0, 2);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 3);
lean::inc(x_21);
lean::dec(x_0);
x_24 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_26 = l_Array_miterateAux___main___at_Lean_IR_FreeVariables_insertParams___spec__1(x_17, x_17, x_24, x_1);
lean::dec(x_17);
x_28 = l_Lean_IR_FreeVariables_collectFnBody___main(x_19, x_26, x_2);
x_29 = lean::box(0);
x_30 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_1, x_15, x_29);
x_0 = x_21;
x_1 = x_30;
x_2 = x_28;
goto _start;
}
case 2:
{
obj* x_32; obj* x_34; obj* x_36; obj* x_40; obj* x_42; 
x_32 = lean::cnstr_get(x_0, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
lean::dec(x_0);
lean::inc(x_1);
x_40 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_32);
lean::inc(x_1);
x_42 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_34);
if (lean::obj_tag(x_40) == 0)
{
obj* x_43; obj* x_44; 
x_43 = lean::box(0);
x_44 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_32, x_43);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; 
x_45 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_44, x_34, x_43);
x_0 = x_36;
x_2 = x_45;
goto _start;
}
else
{
lean::dec(x_42);
lean::dec(x_34);
x_0 = x_36;
x_2 = x_44;
goto _start;
}
}
else
{
lean::dec(x_40);
lean::dec(x_32);
if (lean::obj_tag(x_42) == 0)
{
obj* x_52; obj* x_53; 
x_52 = lean::box(0);
x_53 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_34, x_52);
x_0 = x_36;
x_2 = x_53;
goto _start;
}
else
{
lean::dec(x_42);
lean::dec(x_34);
x_0 = x_36;
goto _start;
}
}
}
case 3:
{
obj* x_58; obj* x_60; obj* x_62; obj* x_66; obj* x_68; 
x_58 = lean::cnstr_get(x_0, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_0, 2);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_0, 3);
lean::inc(x_62);
lean::dec(x_0);
lean::inc(x_1);
x_66 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_58);
lean::inc(x_1);
x_68 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_60);
if (lean::obj_tag(x_66) == 0)
{
obj* x_69; obj* x_70; 
x_69 = lean::box(0);
x_70 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_58, x_69);
if (lean::obj_tag(x_68) == 0)
{
obj* x_71; 
x_71 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_70, x_60, x_69);
x_0 = x_62;
x_2 = x_71;
goto _start;
}
else
{
lean::dec(x_60);
lean::dec(x_68);
x_0 = x_62;
x_2 = x_70;
goto _start;
}
}
else
{
lean::dec(x_58);
lean::dec(x_66);
if (lean::obj_tag(x_68) == 0)
{
obj* x_78; obj* x_79; 
x_78 = lean::box(0);
x_79 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_60, x_78);
x_0 = x_62;
x_2 = x_79;
goto _start;
}
else
{
lean::dec(x_60);
lean::dec(x_68);
x_0 = x_62;
goto _start;
}
}
}
case 4:
{
obj* x_84; obj* x_86; obj* x_88; obj* x_92; obj* x_94; 
x_84 = lean::cnstr_get(x_0, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_0, 3);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_0, 4);
lean::inc(x_88);
lean::dec(x_0);
lean::inc(x_1);
x_92 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_84);
lean::inc(x_1);
x_94 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_86);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_96; 
x_95 = lean::box(0);
x_96 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_84, x_95);
if (lean::obj_tag(x_94) == 0)
{
obj* x_97; 
x_97 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_96, x_86, x_95);
x_0 = x_88;
x_2 = x_97;
goto _start;
}
else
{
lean::dec(x_94);
lean::dec(x_86);
x_0 = x_88;
x_2 = x_96;
goto _start;
}
}
else
{
lean::dec(x_84);
lean::dec(x_92);
if (lean::obj_tag(x_94) == 0)
{
obj* x_104; obj* x_105; 
x_104 = lean::box(0);
x_105 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_86, x_104);
x_0 = x_88;
x_2 = x_105;
goto _start;
}
else
{
lean::dec(x_94);
lean::dec(x_86);
x_0 = x_88;
goto _start;
}
}
}
case 8:
{
obj* x_110; 
x_110 = lean::cnstr_get(x_0, 1);
lean::inc(x_110);
lean::dec(x_0);
x_0 = x_110;
goto _start;
}
case 9:
{
obj* x_114; obj* x_116; obj* x_120; 
x_114 = lean::cnstr_get(x_0, 1);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_0, 2);
lean::inc(x_116);
lean::dec(x_0);
lean::inc(x_1);
x_120 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_114);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_121 = lean::box(0);
x_122 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_114, x_121);
x_123 = l_Lean_IR_FreeVariables_collectFnBody___main___closed__1;
x_124 = lean::mk_nat_obj(0ul);
x_125 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2(x_123, x_116, x_1, x_116, x_124, x_122);
lean::dec(x_116);
return x_125;
}
else
{
obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_120);
lean::dec(x_114);
x_129 = l_Lean_IR_FreeVariables_collectFnBody___main___closed__1;
x_130 = lean::mk_nat_obj(0ul);
x_131 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_14__collectAlts___spec__2(x_129, x_116, x_1, x_116, x_130, x_2);
lean::dec(x_116);
return x_131;
}
}
case 10:
{
obj* x_133; obj* x_136; 
x_133 = lean::cnstr_get(x_0, 0);
lean::inc(x_133);
lean::dec(x_0);
x_136 = l___private_init_lean_compiler_ir_basic_10__collectArg___main(x_133, x_1, x_2);
return x_136;
}
case 11:
{
obj* x_137; obj* x_139; obj* x_143; 
x_137 = lean::cnstr_get(x_0, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_0, 1);
lean::inc(x_139);
lean::dec(x_0);
lean::inc(x_1);
x_143 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_137);
if (lean::obj_tag(x_143) == 0)
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_144 = lean::box(0);
x_145 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_137, x_144);
x_146 = lean::mk_nat_obj(0ul);
x_147 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_139, x_1, x_139, x_146, x_145);
lean::dec(x_139);
return x_147;
}
else
{
obj* x_151; obj* x_152; 
lean::dec(x_137);
lean::dec(x_143);
x_151 = lean::mk_nat_obj(0ul);
x_152 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_12__collectArgs___spec__2(x_139, x_1, x_139, x_151, x_2);
lean::dec(x_139);
return x_152;
}
}
case 12:
{
lean::dec(x_1);
return x_2;
}
default:
{
obj* x_155; obj* x_157; obj* x_161; 
x_155 = lean::cnstr_get(x_0, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_0, 2);
lean::inc(x_157);
lean::dec(x_0);
lean::inc(x_1);
x_161 = l_RBNode_findCore___main___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__1(x_1, x_155);
if (lean::obj_tag(x_161) == 0)
{
obj* x_162; obj* x_163; 
x_162 = lean::box(0);
x_163 = l_RBNode_insert___at___private_init_lean_compiler_ir_basic_2__collectIndex___spec__2(x_2, x_155, x_162);
x_0 = x_157;
x_2 = x_163;
goto _start;
}
else
{
lean::dec(x_155);
lean::dec(x_161);
x_0 = x_157;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_FreeVariables_collectFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_FreeVariables_collectFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_FnBody_collectFreeVars(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_Lean_IR_FreeVariables_collectFnBody___main(x_0, x_2, x_1);
return x_3;
}
}
obj* l_Lean_IR_FnBody_freeVars(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l_Lean_IR_FnBody_collectFreeVars(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_15__skip(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_basic_15__skip___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_basic_15__skip(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_basic_16__collect(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_lt(x_1, x_0);
if (x_2 == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_16__collect___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_16__collect(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_17__collectVar(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_lt(x_1, x_0);
if (x_2 == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_17__collectVar___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_17__collectVar(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_18__collectJP(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_lt(x_1, x_0);
if (x_2 == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_0);
return x_0;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_18__collectJP___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_18__collectJP(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_19__seq(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
}
}
obj* _init_l_Lean_IR_MaxVar_HasAndthen() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_basic_19__seq), 3, 0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_basic_20__collectArg___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; uint8 x_3; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_2);
return x_2;
}
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_20__collectArg___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_20__collectArg___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_20__collectArg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_20__collectArg___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_20__collectArg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_20__collectArg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_1);
lean::dec(x_3);
return x_4;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_fget(x_2, x_3);
lean::inc(x_1);
x_12 = lean::apply_2(x_1, x_10, x_4);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___rarg(x_0, x_1, x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_basic_21__collectArray___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_21__collectArray___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_basic_21__collectArray___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_basic_21__collectArray(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l___private_init_lean_compiler_ir_basic_20__collectArg___main(x_8, x_3);
lean::dec(x_3);
lean::dec(x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_9;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_0, x_0, x_2, x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_basic_22__collectArgs(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_0, x_0, x_2, x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_22__collectArgs___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_22__collectArgs(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_23__collectParam(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
lean::inc(x_2);
return x_2;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_23__collectParam___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_23__collectParam(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l___private_init_lean_compiler_ir_basic_23__collectParam(x_8, x_3);
lean::dec(x_3);
lean::dec(x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_2 = x_13;
x_3 = x_9;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2(x_0, x_0, x_2, x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_basic_24__collectParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2(x_0, x_0, x_2, x_1);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_24__collectParams___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_24__collectParams(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_basic_25__collectExpr___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::mk_nat_obj(0ul);
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_2, x_2, x_5, x_1);
lean::dec(x_2);
return x_6;
}
case 2:
{
obj* x_8; obj* x_10; uint8 x_13; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 2);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::nat_dec_lt(x_1, x_8);
if (x_13 == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_8);
x_15 = lean::mk_nat_obj(0ul);
x_16 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_10, x_10, x_15, x_1);
lean::dec(x_10);
return x_16;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_1);
x_19 = lean::mk_nat_obj(0ul);
x_20 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_10, x_10, x_19, x_8);
lean::dec(x_10);
return x_20;
}
}
case 3:
{
obj* x_22; uint8 x_25; 
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::nat_dec_lt(x_1, x_22);
if (x_25 == 0)
{
lean::dec(x_22);
return x_1;
}
else
{
lean::dec(x_1);
return x_22;
}
}
case 4:
{
obj* x_28; uint8 x_31; 
x_28 = lean::cnstr_get(x_0, 1);
lean::inc(x_28);
lean::dec(x_0);
x_31 = lean::nat_dec_lt(x_1, x_28);
if (x_31 == 0)
{
lean::dec(x_28);
return x_1;
}
else
{
lean::dec(x_1);
return x_28;
}
}
case 5:
{
obj* x_34; uint8 x_37; 
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
lean::dec(x_0);
x_37 = lean::nat_dec_lt(x_1, x_34);
if (x_37 == 0)
{
lean::dec(x_34);
return x_1;
}
else
{
lean::dec(x_1);
return x_34;
}
}
case 6:
{
obj* x_40; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_0, 1);
lean::inc(x_40);
lean::dec(x_0);
x_43 = lean::mk_nat_obj(0ul);
x_44 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_40, x_40, x_43, x_1);
lean::dec(x_40);
return x_44;
}
case 7:
{
obj* x_46; obj* x_49; obj* x_50; 
x_46 = lean::cnstr_get(x_0, 1);
lean::inc(x_46);
lean::dec(x_0);
x_49 = lean::mk_nat_obj(0ul);
x_50 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_46, x_46, x_49, x_1);
lean::dec(x_46);
return x_50;
}
case 8:
{
obj* x_52; obj* x_54; uint8 x_57; 
x_52 = lean::cnstr_get(x_0, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_0, 1);
lean::inc(x_54);
lean::dec(x_0);
x_57 = lean::nat_dec_lt(x_1, x_52);
if (x_57 == 0)
{
obj* x_59; obj* x_60; 
lean::dec(x_52);
x_59 = lean::mk_nat_obj(0ul);
x_60 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_54, x_54, x_59, x_1);
lean::dec(x_54);
return x_60;
}
else
{
obj* x_63; obj* x_64; 
lean::dec(x_1);
x_63 = lean::mk_nat_obj(0ul);
x_64 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_54, x_54, x_63, x_52);
lean::dec(x_54);
return x_64;
}
}
case 11:
{
lean::dec(x_0);
return x_1;
}
default:
{
obj* x_67; uint8 x_70; 
x_67 = lean::cnstr_get(x_0, 0);
lean::inc(x_67);
lean::dec(x_0);
x_70 = lean::nat_dec_lt(x_1, x_67);
if (x_70 == 0)
{
lean::dec(x_67);
return x_1;
}
else
{
lean::dec(x_1);
return x_67;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_basic_25__collectExpr(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_basic_25__collectExpr___main(x_0, x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
lean::dec(x_0);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::array_fget(x_2, x_3);
x_11 = l_Lean_IR_AltCore_body___main(x_10);
lean::dec(x_10);
lean::inc(x_0);
x_14 = lean::apply_2(x_0, x_11, x_4);
x_15 = lean::mk_nat_obj(1ul);
x_16 = lean::nat_add(x_3, x_15);
lean::dec(x_3);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2(x_0, x_1, x_1, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_basic_26__collectAlts(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2(x_0, x_1, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_basic_21__collectArray___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_basic_26__collectAlts___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_basic_26__collectAlts(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_MaxVar_collectFnBody___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_MaxVar_collectFnBody___main), 2, 0);
return x_0;
}
}
obj* l_Lean_IR_MaxVar_collectFnBody___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_4; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = l___private_init_lean_compiler_ir_basic_25__collectExpr___main(x_2, x_1);
x_0 = x_4;
x_1 = x_7;
goto _start;
}
case 1:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 3);
lean::inc(x_13);
lean::dec(x_0);
x_16 = l_Lean_IR_MaxVar_collectFnBody___main(x_11, x_1);
x_17 = lean::mk_nat_obj(0ul);
x_18 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2(x_9, x_9, x_17, x_16);
lean::dec(x_9);
x_0 = x_13;
x_1 = x_18;
goto _start;
}
case 2:
{
obj* x_21; obj* x_23; obj* x_25; uint8 x_28; 
x_21 = lean::cnstr_get(x_0, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 2);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_0, 3);
lean::inc(x_25);
lean::dec(x_0);
x_28 = lean::nat_dec_lt(x_1, x_21);
if (x_28 == 0)
{
uint8 x_30; 
lean::dec(x_21);
x_30 = lean::nat_dec_lt(x_1, x_23);
if (x_30 == 0)
{
lean::dec(x_23);
x_0 = x_25;
goto _start;
}
else
{
lean::dec(x_1);
x_0 = x_25;
x_1 = x_23;
goto _start;
}
}
else
{
uint8 x_36; 
lean::dec(x_1);
x_36 = lean::nat_dec_lt(x_21, x_23);
if (x_36 == 0)
{
lean::dec(x_23);
x_0 = x_25;
x_1 = x_21;
goto _start;
}
else
{
lean::dec(x_21);
x_0 = x_25;
x_1 = x_23;
goto _start;
}
}
}
case 3:
{
obj* x_41; obj* x_43; obj* x_45; uint8 x_48; 
x_41 = lean::cnstr_get(x_0, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_0, 2);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_0, 3);
lean::inc(x_45);
lean::dec(x_0);
x_48 = lean::nat_dec_lt(x_1, x_41);
if (x_48 == 0)
{
uint8 x_50; 
lean::dec(x_41);
x_50 = lean::nat_dec_lt(x_1, x_43);
if (x_50 == 0)
{
lean::dec(x_43);
x_0 = x_45;
goto _start;
}
else
{
lean::dec(x_1);
x_0 = x_45;
x_1 = x_43;
goto _start;
}
}
else
{
uint8 x_56; 
lean::dec(x_1);
x_56 = lean::nat_dec_lt(x_41, x_43);
if (x_56 == 0)
{
lean::dec(x_43);
x_0 = x_45;
x_1 = x_41;
goto _start;
}
else
{
lean::dec(x_41);
x_0 = x_45;
x_1 = x_43;
goto _start;
}
}
}
case 4:
{
obj* x_61; obj* x_63; obj* x_65; uint8 x_68; 
x_61 = lean::cnstr_get(x_0, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_0, 3);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_0, 4);
lean::inc(x_65);
lean::dec(x_0);
x_68 = lean::nat_dec_lt(x_1, x_61);
if (x_68 == 0)
{
uint8 x_70; 
lean::dec(x_61);
x_70 = lean::nat_dec_lt(x_1, x_63);
if (x_70 == 0)
{
lean::dec(x_63);
x_0 = x_65;
goto _start;
}
else
{
lean::dec(x_1);
x_0 = x_65;
x_1 = x_63;
goto _start;
}
}
else
{
uint8 x_76; 
lean::dec(x_1);
x_76 = lean::nat_dec_lt(x_61, x_63);
if (x_76 == 0)
{
lean::dec(x_63);
x_0 = x_65;
x_1 = x_61;
goto _start;
}
else
{
lean::dec(x_61);
x_0 = x_65;
x_1 = x_63;
goto _start;
}
}
}
case 8:
{
obj* x_81; 
x_81 = lean::cnstr_get(x_0, 1);
lean::inc(x_81);
lean::dec(x_0);
x_0 = x_81;
goto _start;
}
case 9:
{
obj* x_85; obj* x_87; uint8 x_90; 
x_85 = lean::cnstr_get(x_0, 1);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_0, 2);
lean::inc(x_87);
lean::dec(x_0);
x_90 = lean::nat_dec_lt(x_1, x_85);
if (x_90 == 0)
{
obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_85);
x_92 = l_Lean_IR_MaxVar_collectFnBody___main___closed__1;
x_93 = lean::mk_nat_obj(0ul);
x_94 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2(x_92, x_87, x_87, x_93, x_1);
lean::dec(x_87);
return x_94;
}
else
{
obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_1);
x_97 = l_Lean_IR_MaxVar_collectFnBody___main___closed__1;
x_98 = lean::mk_nat_obj(0ul);
x_99 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_26__collectAlts___spec__2(x_97, x_87, x_87, x_98, x_85);
lean::dec(x_87);
return x_99;
}
}
case 10:
{
obj* x_101; obj* x_104; 
x_101 = lean::cnstr_get(x_0, 0);
lean::inc(x_101);
lean::dec(x_0);
x_104 = l___private_init_lean_compiler_ir_basic_20__collectArg___main(x_101, x_1);
lean::dec(x_1);
lean::dec(x_101);
return x_104;
}
case 11:
{
obj* x_107; obj* x_109; uint8 x_112; 
x_107 = lean::cnstr_get(x_0, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_0, 1);
lean::inc(x_109);
lean::dec(x_0);
x_112 = lean::nat_dec_lt(x_1, x_107);
if (x_112 == 0)
{
obj* x_114; obj* x_115; 
lean::dec(x_107);
x_114 = lean::mk_nat_obj(0ul);
x_115 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_109, x_109, x_114, x_1);
lean::dec(x_109);
return x_115;
}
else
{
obj* x_118; obj* x_119; 
lean::dec(x_1);
x_118 = lean::mk_nat_obj(0ul);
x_119 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_22__collectArgs___spec__2(x_109, x_109, x_118, x_107);
lean::dec(x_109);
return x_119;
}
}
case 12:
{
return x_1;
}
default:
{
obj* x_121; obj* x_123; uint8 x_126; 
x_121 = lean::cnstr_get(x_0, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_0, 2);
lean::inc(x_123);
lean::dec(x_0);
x_126 = lean::nat_dec_lt(x_1, x_121);
if (x_126 == 0)
{
lean::dec(x_121);
x_0 = x_123;
goto _start;
}
else
{
lean::dec(x_1);
x_0 = x_123;
x_1 = x_121;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_MaxVar_collectFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_MaxVar_collectFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_MaxVar_collectDecl___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_4; obj* x_7; obj* x_8; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::mk_nat_obj(0ul);
x_8 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2(x_2, x_2, x_7, x_1);
lean::dec(x_2);
x_10 = l_Lean_IR_MaxVar_collectFnBody___main(x_4, x_8);
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::mk_nat_obj(0ul);
x_15 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_basic_24__collectParams___spec__2(x_11, x_11, x_14, x_1);
lean::dec(x_11);
return x_15;
}
}
}
obj* l_Lean_IR_MaxVar_collectDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_MaxVar_collectDecl___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_FnBody_maxVar(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_IR_MaxVar_collectFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Decl_maxVar(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Lean_IR_MaxVar_collectDecl___main(x_0, x_1);
return x_2;
}
}
uint8 l_Lean_IR_HasIndex_visitVar(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_eq(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_HasIndex_visitVar___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitVar(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_HasIndex_visitJP(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_eq(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_HasIndex_visitJP___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitJP(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_HasIndex_visitArg___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; uint8 x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::nat_dec_eq(x_0, x_2);
return x_3;
}
else
{
uint8 x_4; 
x_4 = 0;
return x_4;
}
}
}
obj* l_Lean_IR_HasIndex_visitArg___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitArg___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_HasIndex_visitArg(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_HasIndex_visitArg___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_HasIndex_visitArg___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitArg(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_HasIndex_visitArg___main(x_0, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
uint8 x_16; 
lean::dec(x_2);
x_16 = 1;
return x_16;
}
}
}
}
uint8 l_Lean_IR_HasIndex_visitArgs(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_HasIndex_visitArgs___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitArgs(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Array_anyAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_12; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::nat_dec_eq(x_0, x_9);
lean::dec(x_9);
if (x_12 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::mk_nat_obj(1ul);
x_15 = lean::nat_add(x_2, x_14);
lean::dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
uint8 x_19; 
lean::dec(x_2);
x_19 = 1;
return x_19;
}
}
}
}
uint8 l_Lean_IR_HasIndex_visitParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_anyAux___main___at_Lean_IR_HasIndex_visitParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_HasIndex_visitParams___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitParams(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_HasIndex_visitExpr___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_2, x_3);
return x_4;
}
case 2:
{
obj* x_5; obj* x_6; uint8 x_7; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::nat_dec_eq(x_0, x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_6, x_8);
return x_9;
}
else
{
uint8 x_10; 
x_10 = 1;
return x_10;
}
}
case 3:
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_1, 1);
x_12 = lean::nat_dec_eq(x_0, x_11);
return x_12;
}
case 4:
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_1, 1);
x_14 = lean::nat_dec_eq(x_0, x_13);
return x_14;
}
case 5:
{
obj* x_15; uint8 x_16; 
x_15 = lean::cnstr_get(x_1, 2);
x_16 = lean::nat_dec_eq(x_0, x_15);
return x_16;
}
case 6:
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_1, 1);
x_18 = lean::mk_nat_obj(0ul);
x_19 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_17, x_18);
return x_19;
}
case 7:
{
obj* x_20; obj* x_21; uint8 x_22; 
x_20 = lean::cnstr_get(x_1, 1);
x_21 = lean::mk_nat_obj(0ul);
x_22 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_20, x_21);
return x_22;
}
case 8:
{
obj* x_23; obj* x_24; uint8 x_25; 
x_23 = lean::cnstr_get(x_1, 0);
x_24 = lean::cnstr_get(x_1, 1);
x_25 = lean::nat_dec_eq(x_0, x_23);
if (x_25 == 0)
{
obj* x_26; uint8 x_27; 
x_26 = lean::mk_nat_obj(0ul);
x_27 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_24, x_26);
return x_27;
}
else
{
uint8 x_28; 
x_28 = 1;
return x_28;
}
}
case 11:
{
uint8 x_29; 
x_29 = 0;
return x_29;
}
default:
{
obj* x_30; uint8 x_31; 
x_30 = lean::cnstr_get(x_1, 0);
x_31 = lean::nat_dec_eq(x_0, x_30);
return x_31;
}
}
}
}
obj* l_Lean_IR_HasIndex_visitExpr___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitExpr___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_HasIndex_visitExpr(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_HasIndex_visitExpr___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_HasIndex_visitExpr___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitExpr(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Array_anyAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_7; 
lean::dec(x_2);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_11; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_AltCore_body___main(x_8);
lean::dec(x_8);
x_11 = l_Lean_IR_HasIndex_visitFnBody___main(x_0, x_9);
lean::dec(x_9);
if (x_11 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
goto _start;
}
else
{
uint8 x_18; 
lean::dec(x_2);
x_18 = 1;
return x_18;
}
}
}
}
uint8 l_Lean_IR_HasIndex_visitFnBody___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = l_Lean_IR_HasIndex_visitExpr___main(x_0, x_3);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = lean::nat_dec_eq(x_0, x_2);
if (x_6 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
return x_5;
}
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
case 1:
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = lean::cnstr_get(x_1, 2);
x_12 = lean::cnstr_get(x_1, 3);
x_13 = lean::mk_nat_obj(0ul);
x_14 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitParams___spec__1(x_0, x_10, x_13);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = l_Lean_IR_HasIndex_visitFnBody___main(x_0, x_11);
if (x_15 == 0)
{
uint8 x_16; 
x_16 = lean::nat_dec_eq(x_0, x_9);
if (x_16 == 0)
{
x_1 = x_12;
goto _start;
}
else
{
return x_15;
}
}
else
{
uint8 x_18; 
x_18 = 1;
return x_18;
}
}
else
{
uint8 x_19; 
x_19 = lean::nat_dec_eq(x_0, x_9);
if (x_19 == 0)
{
x_1 = x_12;
goto _start;
}
else
{
uint8 x_21; 
x_21 = 0;
return x_21;
}
}
}
case 2:
{
obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_22 = lean::cnstr_get(x_1, 0);
x_23 = lean::cnstr_get(x_1, 2);
x_24 = lean::cnstr_get(x_1, 3);
x_25 = lean::nat_dec_eq(x_0, x_22);
if (x_25 == 0)
{
uint8 x_26; 
x_26 = lean::nat_dec_eq(x_0, x_23);
if (x_26 == 0)
{
x_1 = x_24;
goto _start;
}
else
{
uint8 x_28; 
x_28 = 1;
return x_28;
}
}
else
{
uint8 x_29; 
x_29 = 1;
return x_29;
}
}
case 3:
{
obj* x_30; obj* x_31; obj* x_32; uint8 x_33; 
x_30 = lean::cnstr_get(x_1, 0);
x_31 = lean::cnstr_get(x_1, 2);
x_32 = lean::cnstr_get(x_1, 3);
x_33 = lean::nat_dec_eq(x_0, x_30);
if (x_33 == 0)
{
uint8 x_34; 
x_34 = lean::nat_dec_eq(x_0, x_31);
if (x_34 == 0)
{
x_1 = x_32;
goto _start;
}
else
{
uint8 x_36; 
x_36 = 1;
return x_36;
}
}
else
{
uint8 x_37; 
x_37 = 1;
return x_37;
}
}
case 4:
{
obj* x_38; obj* x_39; obj* x_40; uint8 x_41; 
x_38 = lean::cnstr_get(x_1, 0);
x_39 = lean::cnstr_get(x_1, 3);
x_40 = lean::cnstr_get(x_1, 4);
x_41 = lean::nat_dec_eq(x_0, x_38);
if (x_41 == 0)
{
uint8 x_42; 
x_42 = lean::nat_dec_eq(x_0, x_39);
if (x_42 == 0)
{
x_1 = x_40;
goto _start;
}
else
{
uint8 x_44; 
x_44 = 1;
return x_44;
}
}
else
{
uint8 x_45; 
x_45 = 1;
return x_45;
}
}
case 8:
{
obj* x_46; 
x_46 = lean::cnstr_get(x_1, 1);
x_1 = x_46;
goto _start;
}
case 9:
{
obj* x_48; obj* x_49; uint8 x_50; 
x_48 = lean::cnstr_get(x_1, 1);
x_49 = lean::cnstr_get(x_1, 2);
x_50 = lean::nat_dec_eq(x_0, x_48);
if (x_50 == 0)
{
obj* x_51; uint8 x_52; 
x_51 = lean::mk_nat_obj(0ul);
x_52 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1(x_0, x_49, x_51);
return x_52;
}
else
{
uint8 x_53; 
x_53 = 1;
return x_53;
}
}
case 10:
{
obj* x_54; uint8 x_55; 
x_54 = lean::cnstr_get(x_1, 0);
x_55 = l_Lean_IR_HasIndex_visitArg___main(x_0, x_54);
return x_55;
}
case 11:
{
obj* x_56; obj* x_57; uint8 x_58; 
x_56 = lean::cnstr_get(x_1, 0);
x_57 = lean::cnstr_get(x_1, 1);
x_58 = lean::nat_dec_eq(x_0, x_56);
if (x_58 == 0)
{
obj* x_59; uint8 x_60; 
x_59 = lean::mk_nat_obj(0ul);
x_60 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitArgs___spec__1(x_0, x_57, x_59);
return x_60;
}
else
{
uint8 x_61; 
x_61 = 1;
return x_61;
}
}
case 12:
{
uint8 x_62; 
x_62 = 0;
return x_62;
}
default:
{
obj* x_63; obj* x_64; uint8 x_65; 
x_63 = lean::cnstr_get(x_1, 0);
x_64 = lean::cnstr_get(x_1, 2);
x_65 = lean::nat_dec_eq(x_0, x_63);
if (x_65 == 0)
{
x_1 = x_64;
goto _start;
}
else
{
uint8 x_67; 
x_67 = 1;
return x_67;
}
}
}
}
}
obj* l_Array_anyAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = l_Array_anyAux___main___at_Lean_IR_HasIndex_visitFnBody___main___spec__1(x_0, x_1, x_2);
x_4 = lean::box(x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_HasIndex_visitFnBody___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitFnBody___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_HasIndex_visitFnBody(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_HasIndex_visitFnBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_HasIndex_visitFnBody___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_HasIndex_visitFnBody(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_Arg_hasFreeVar(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_HasIndex_visitArg___main(x_1, x_0);
return x_2;
}
}
obj* l_Lean_IR_Arg_hasFreeVar___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Arg_hasFreeVar(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_Expr_hasFreeVar(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_HasIndex_visitExpr___main(x_1, x_0);
return x_2;
}
}
obj* l_Lean_IR_Expr_hasFreeVar___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Expr_hasFreeVar(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_FnBody_hasFreeVar(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_HasIndex_visitFnBody___main(x_1, x_0);
return x_2;
}
}
obj* l_Lean_IR_FnBody_hasFreeVar___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_FnBody_hasFreeVar(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_kvmap(obj*);
obj* initialize_init_lean_format(obj*);
obj* initialize_init_data_array_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_kvmap(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_VarId_HasToString___closed__1 = _init_l_Lean_IR_VarId_HasToString___closed__1();
lean::mark_persistent(l_Lean_IR_VarId_HasToString___closed__1);
 l_Lean_IR_JoinPointId_HasToString___closed__1 = _init_l_Lean_IR_JoinPointId_HasToString___closed__1();
lean::mark_persistent(l_Lean_IR_JoinPointId_HasToString___closed__1);
 l_Lean_IR_MData_empty = _init_l_Lean_IR_MData_empty();
lean::mark_persistent(l_Lean_IR_MData_empty);
 l_Lean_IR_MData_HasEmptyc = _init_l_Lean_IR_MData_HasEmptyc();
lean::mark_persistent(l_Lean_IR_MData_HasEmptyc);
 l_Lean_IR_IRType_HasBeq = _init_l_Lean_IR_IRType_HasBeq();
lean::mark_persistent(l_Lean_IR_IRType_HasBeq);
 l_Lean_IR_argInh = _init_l_Lean_IR_argInh();
lean::mark_persistent(l_Lean_IR_argInh);
 lean::ir::mk_irrelevant_arg_core = lean::ir::_init_mk_irrelevant_arg_core();
lean::mark_persistent(lean::ir::mk_irrelevant_arg_core);
 l_Lean_IR_LitVal_HasBeq = _init_l_Lean_IR_LitVal_HasBeq();
lean::mark_persistent(l_Lean_IR_LitVal_HasBeq);
 l_Lean_IR_CtorInfo_HasBeq = _init_l_Lean_IR_CtorInfo_HasBeq();
lean::mark_persistent(l_Lean_IR_CtorInfo_HasBeq);
 l_Lean_IR_paramInh = _init_l_Lean_IR_paramInh();
lean::mark_persistent(l_Lean_IR_paramInh);
 l_Lean_IR_Inhabited = _init_l_Lean_IR_Inhabited();
lean::mark_persistent(l_Lean_IR_Inhabited);
 l_Lean_IR_FnBody_nil = _init_l_Lean_IR_FnBody_nil();
lean::mark_persistent(l_Lean_IR_FnBody_nil);
 lean::ir::mk_unreachable_core = lean::ir::_init_mk_unreachable_core();
lean::mark_persistent(lean::ir::mk_unreachable_core);
 l_Lean_IR_altInh = _init_l_Lean_IR_altInh();
lean::mark_persistent(l_Lean_IR_altInh);
 l_Lean_IR_AltCore_mmodifyBody___main___rarg___closed__1 = _init_l_Lean_IR_AltCore_mmodifyBody___main___rarg___closed__1();
lean::mark_persistent(l_Lean_IR_AltCore_mmodifyBody___main___rarg___closed__1);
 l_Lean_IR_VarId_hasAeqv = _init_l_Lean_IR_VarId_hasAeqv();
lean::mark_persistent(l_Lean_IR_VarId_hasAeqv);
 l_Lean_IR_Arg_hasAeqv = _init_l_Lean_IR_Arg_hasAeqv();
lean::mark_persistent(l_Lean_IR_Arg_hasAeqv);
 l_Lean_IR_args_hasAeqv = _init_l_Lean_IR_args_hasAeqv();
lean::mark_persistent(l_Lean_IR_args_hasAeqv);
 l_Lean_IR_Expr_hasAeqv = _init_l_Lean_IR_Expr_hasAeqv();
lean::mark_persistent(l_Lean_IR_Expr_hasAeqv);
 l_Lean_IR_FnBody_HasBeq = _init_l_Lean_IR_FnBody_HasBeq();
lean::mark_persistent(l_Lean_IR_FnBody_HasBeq);
 l_Lean_IR_vsetInh = _init_l_Lean_IR_vsetInh();
lean::mark_persistent(l_Lean_IR_vsetInh);
 l_Lean_IR_FreeVariables_HasAndthen = _init_l_Lean_IR_FreeVariables_HasAndthen();
lean::mark_persistent(l_Lean_IR_FreeVariables_HasAndthen);
 l_Lean_IR_FreeVariables_collectFnBody___main___closed__1 = _init_l_Lean_IR_FreeVariables_collectFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_FreeVariables_collectFnBody___main___closed__1);
 l_Lean_IR_MaxVar_HasAndthen = _init_l_Lean_IR_MaxVar_HasAndthen();
lean::mark_persistent(l_Lean_IR_MaxVar_HasAndthen);
 l_Lean_IR_MaxVar_collectFnBody___main___closed__1 = _init_l_Lean_IR_MaxVar_collectFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_MaxVar_collectFnBody___main___closed__1);
return w;
}
