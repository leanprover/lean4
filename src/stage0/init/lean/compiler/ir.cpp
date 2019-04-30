// Lean compiler output
// Module: init.lean.compiler.ir
// Imports: init.default init.lean.name init.lean.kvmap init.lean.format init.data.array.default
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
obj* l_Lean_IR_formatDecl(obj*, obj*);
obj* l_Lean_IR_FnBody_beq___boxed(obj*, obj*);
obj* l_Lean_IR_mkJDecl___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatAlt(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_10__collectAlts___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__1;
namespace lean {
namespace ir {
obj* mk_sset_core(obj*, obj*, obj*, obj*, uint8, obj*);
}}
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__9;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_IR_mkVDecl___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_formatKVMap(obj*);
uint8 l_Lean_IR_IRType_beq(uint8, uint8);
uint8 l_Lean_IR_Arg_alphaEqv(obj*, obj*, obj*);
extern obj* l_Lean_Format_paren___closed__2;
namespace lean {
namespace ir {
obj* mk_jdecl_core(obj*, obj*, uint8, obj*, obj*);
}}
namespace lean {
namespace ir {
obj* mk_var_arg_core(obj*);
}}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatDecl___main(obj*, obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_addParamsRename___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_18__formatParam___main___closed__1;
namespace lean {
namespace ir {
obj* mk_fapp_expr_core(obj*, obj*);
}}
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__5;
obj* l___private_init_lean_compiler_ir_4__withParams___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_addParamRename(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_alt_core(obj*, obj*);
}}
uint8 l_Lean_IR_LitVal_beq___main(obj*, obj*);
obj* l_Lean_IR_mkParam___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__6;
obj* l_Lean_IR_CtorInfo_HasBeq;
obj* l___private_init_lean_compiler_ir_16__formatExpr___main(obj*);
obj* l___private_init_lean_compiler_ir_3__withBv(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__3;
obj* l___private_init_lean_compiler_ir_10__collectAlts(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_13__formatArgs___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_13__formatArgs___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_alphaEqv___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_VarId_alphaEqv(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_10__collectAlts___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_insertParams(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_jmp_core(obj*, obj*);
}}
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__12;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__17;
obj* l___private_init_lean_compiler_ir_7__collectArray(obj*);
obj* l___private_init_lean_compiler_ir_7__collectArray___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___boxed(obj*);
obj* l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_8__collectArgs___spec__1___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_alphaEqv(obj*, obj*, obj*);
extern obj* l_Lean_Format_sbracket___closed__1;
namespace lean {
namespace ir {
obj* mk_str_expr_core(obj*);
}}
namespace lean {
namespace ir {
obj* mk_proj_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_formatAlt___main___closed__1;
uint8 l_Lean_IR_CtorInfo_beq(obj*, obj*);
obj* l_Lean_IR_argsHasFormat;
obj* l___private_init_lean_compiler_ir_11__collectFnBody___main(obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__13;
obj* l_Lean_IR_declHasFormat;
obj* l_Lean_IR_Alt_default(obj*);
obj* l___private_init_lean_compiler_ir_16__formatExpr(obj*);
namespace lean {
namespace ir {
obj* mk_num_expr_core(obj*);
}}
extern obj* l_Lean_Format_join___closed__1;
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__11;
uint8 l_Lean_IR_FnBody_isPure(obj*);
obj* l_Lean_IR_VarId_hasAeqv;
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__11;
namespace lean {
namespace ir {
obj* mk_sproj_expr_core(obj*, obj*);
}}
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___closed__6;
uint8 l_Lean_IR_LitVal_beq(obj*, obj*);
obj* l_Lean_IR_mkSSet___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_NameSet_contains(obj*, obj*);
uint8 l_Lean_IR_Expr_isPure___main(obj*);
obj* l___private_init_lean_compiler_ir_1__skip___boxed(obj*);
obj* l_Lean_IR_formatAlt___main(obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_FnBody_alphaEqv___main___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__12;
extern obj* l_Lean_Format_sbracket___closed__2;
obj* l_Lean_IR_formatFnBody___main___closed__15;
obj* l_Lean_IR_Arg_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_insertParams___boxed(obj*, obj*);
obj* l_Lean_IR_argHasFormat;
uint8 l_Array_anyAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_2__collectVar(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip(obj*);
obj* l___private_init_lean_compiler_ir_6__collectArg___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_6__collectArg(obj*, obj*, obj*);
obj* l_Lean_IR_freeVars(obj*);
obj* l_Lean_IR_typeHasFormat;
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__2;
obj* l_Array_miterateAux___main___at_Lean_IR_insertParams___spec__1(obj*, obj*, obj*, obj*);
uint8 l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___closed__7;
obj* l___private_init_lean_compiler_ir_8__collectArgs___boxed(obj*, obj*, obj*);
uint8 l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_case_core(obj*, obj*, obj*);
}}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_addParamsRename(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__8;
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__8;
obj* l___private_init_lean_compiler_ir_18__formatParam___main___closed__2;
obj* l_Lean_IR_fnBodyHasFormat;
extern obj* l_Lean_Format_paren___closed__1;
obj* l_Lean_IR_args_hasAeqv;
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__3;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_args_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_HasBeq;
uint8 l_Lean_IR_Expr_alphaEqv(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_7__collectArray___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1(obj*);
obj* l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__1;
obj* l_Lean_IR_formatFnBody___main___closed__9;
obj* l_Lean_IR_LitVal_beq___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___closed__2;
obj* l___private_init_lean_compiler_ir_14__formatLitVal(obj*);
namespace lean {
namespace ir {
obj* mk_ret_core(obj*);
}}
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_formatDecl___main___closed__1;
obj* l_Lean_Format_joinArraySep___at___private_init_lean_compiler_ir_13__formatArgs___spec__1___boxed(obj*, obj*);
obj* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
namespace lean {
namespace ir {
obj* mk_param_core(obj*, uint8, uint8);
}}
extern obj* l_Lean_formatEntry___main___closed__1;
obj* l_Lean_IR_formatFnBody___main___closed__14;
obj* l___private_init_lean_compiler_ir_9__collectExpr(obj*, obj*, obj*);
obj* l_Lean_Format_joinArraySep___at_Lean_IR_formatFnBody___main___spec__1(obj*, obj*);
uint8 l_Lean_KVMap_eqv(obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__2;
obj* l___private_init_lean_compiler_ir_15__formatCtorInfo___main(obj*);
obj* l_Lean_IR_Expr_hasAeqv;
namespace lean {
namespace ir {
obj* mk_uset_core(obj*, obj*, obj*, obj*);
}}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Format_flatten___main___closed__1;
obj* l_Lean_IR_IRType_HasBeq;
obj* l_Lean_NameMap_insert___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__4;
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Expr_isPure___boxed(obj*);
obj* l_Array_anyAux___main___at_Lean_IR_FnBody_isPure___main___spec__1___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_10__collectAlts___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__19;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_Format_joinArraySep___at_Lean_IR_formatFnBody___main___spec__1___boxed(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_irrelevant_arg_core;
}}
obj* l_Lean_IR_HasAndthen;
obj* l_Lean_IR_Arg_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_LitVal_beq___main___boxed(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_app_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_Expr_isPure___main___boxed(obj*);
obj* l___private_init_lean_compiler_ir_5__seq(obj*, obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_unreachable_core;
}}
obj* l___private_init_lean_compiler_ir_11__collectFnBody___main___closed__1;
obj* l_Lean_IR_addVarRename(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___boxed(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__10;
uint8 l_Lean_IR_FnBody_isPure___main(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__5;
obj* l_Lean_IR_formatFnBody(obj*, obj*);
uint8 l_Lean_IR_Arg_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_VarId_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_ctorInfoHasFormat;
obj* l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__2;
extern obj* l_Lean_formatKVMap___closed__1;
obj* l_Lean_IR_formatDecl___main___closed__2;
obj* l_Lean_IR_mkDecl___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_formatFnBody___main___closed__16;
obj* l___private_init_lean_compiler_ir_18__formatParam___main(obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__7;
uint8 l_Lean_IR_CtorInfo_beq___main(obj*, obj*);
uint8 l_Lean_IR_FnBody_beq(obj*, obj*);
uint8 l_Lean_IR_args_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_beq___main___boxed(obj*, obj*);
uint8 l_Lean_IR_Expr_alphaEqv___main(obj*, obj*, obj*);
uint8 l_Lean_IR_Expr_isPure(obj*);
obj* l___private_init_lean_compiler_ir_7__collectArray___boxed(obj*);
namespace lean {
namespace ir {
obj* mk_decl_core(obj*, obj*, uint8, obj*);
}}
namespace lean {
namespace ir {
obj* mk_uproj_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_Arg_hasAeqv;
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___closed__8;
obj* l_Lean_IR_exprHasFormat;
obj* l_Lean_IR_FnBody_isPure___boxed(obj*);
obj* l_Lean_IR_formatFnBody___main___closed__18;
obj* l_Lean_IR_Alt_ctor(obj*, obj*);
obj* l___private_init_lean_compiler_ir_18__formatParam(obj*);
obj* l_Lean_IR_MData_HasEmptyc;
obj* l___private_init_lean_compiler_ir_8__collectArgs(obj*, obj*, obj*);
uint8 l_Array_isEqvAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___closed__4;
obj* l_Lean_IR_FnBody_isPure___main___boxed(obj*);
obj* l_Lean_IR_litValHasFormat;
extern obj* l_Lean_Name_toString___closed__1;
namespace lean {
namespace ir {
obj* mk_papp_expr_core(obj*, obj*);
}}
obj* l___private_init_lean_compiler_ir_15__formatCtorInfo(obj*);
obj* l___private_init_lean_compiler_ir_13__formatArgs(obj*);
namespace lean {
namespace ir {
obj* mk_ctor_info_core(obj*, obj*, obj*, obj*);
}}
namespace lean {
namespace ir {
obj* mk_ctor_expr_core(obj*, obj*);
}}
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__10;
namespace lean {
namespace ir {
obj* mk_vdecl_core(obj*, uint8, obj*, obj*);
}}
obj* l_Lean_IR_formatAlt___main___closed__2;
obj* l___private_init_lean_compiler_ir_12__formatArg___main(obj*);
obj* l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_8__collectArgs___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType(uint8);
obj* l_String_quote(obj*);
obj* l_Lean_IR_IRType_beq___boxed(obj*, obj*);
obj* l_Lean_NameSet_insert(obj*, obj*);
obj* l_Lean_IR_LitVal_HasBeq;
obj* l_Lean_IR_paramHasFormat;
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___boxed(obj*);
obj* l___private_init_lean_compiler_ir_13__formatArgs___boxed(obj*);
obj* l___private_init_lean_compiler_ir_1__skip___rarg___boxed(obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___closed__3;
obj* l___private_init_lean_compiler_ir_11__collectFnBody(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_insertParams___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___main(uint8);
obj* l___private_init_lean_compiler_ir_14__formatLitVal___main(obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___closed__5;
obj* l_Lean_IR_formatFnBody___main___closed__7;
obj* l___private_init_lean_compiler_ir_4__withParams(obj*, obj*, obj*, obj*);
obj* l_Lean_Format_joinArraySep___at___private_init_lean_compiler_ir_13__formatArgs___spec__1(obj*, obj*);
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__1;
obj* l_Lean_IR_CtorInfo_beq___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___closed__1;
obj* l_Lean_IR_formatFnBody___main___closed__4;
obj* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_MData_empty;
obj* l___private_init_lean_compiler_ir_9__collectExpr___main(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_12__formatArg___main___closed__1;
obj* l___private_init_lean_compiler_ir_16__formatExpr___main___closed__6;
uint8 l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_compiler_ir_12__formatArg(obj*);
obj* l_Lean_IR_IRType_beq___main___boxed(obj*, obj*);
obj* l___private_init_lean_compiler_ir_1__skip___rarg(obj*);
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj*, obj*);
obj* l_Lean_IR_formatFnBody___main(obj*, obj*);
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
namespace lean {
namespace ir {
obj* mk_ctor_info_core(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_3);
return x_4;
}
}
}}
uint8 l_Lean_IR_CtorInfo_beq___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_0, 2);
x_5 = lean::cnstr_get(x_0, 3);
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::cnstr_get(x_1, 2);
x_9 = lean::cnstr_get(x_1, 3);
x_10 = lean_name_dec_eq(x_2, x_6);
if (x_10 == 0)
{
uint8 x_11; 
x_11 = 0;
return x_11;
}
else
{
uint8 x_12; 
x_12 = lean::nat_dec_eq(x_3, x_7);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8 x_14; 
x_14 = lean::nat_dec_eq(x_4, x_8);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = 0;
return x_15;
}
else
{
uint8 x_16; 
x_16 = lean::nat_dec_eq(x_5, x_9);
return x_16;
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
obj* mk_ctor_expr_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
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
obj* mk_sproj_expr_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(5, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
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
namespace lean {
namespace ir {
obj* mk_alt_core(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
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
x_7 = lean::array_index(x_0, x_1);
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
x_12 = l_Lean_Name_quickLt(x_1, x_5);
if (x_12 == 0)
{
uint8 x_14; 
lean::dec(x_3);
x_14 = l_Lean_Name_quickLt(x_5, x_1);
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
x_4 = lean_name_dec_eq(x_1, x_2);
return x_4;
}
else
{
obj* x_5; uint8 x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean_name_dec_eq(x_5, x_2);
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
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_25; 
x_18 = lean::cnstr_get(x_1, 0);
x_19 = lean::cnstr_get(x_1, 1);
x_20 = lean::cnstr_get(x_1, 2);
x_21 = lean::cnstr_get(x_2, 0);
x_22 = lean::cnstr_get(x_2, 1);
x_23 = lean::cnstr_get(x_2, 2);
lean::inc(x_0);
x_25 = l_Lean_IR_VarId_alphaEqv(x_0, x_18, x_21);
if (x_25 == 0)
{
uint8 x_27; 
lean::dec(x_0);
x_27 = 0;
return x_27;
}
else
{
uint8 x_28; 
x_28 = l_Lean_IR_CtorInfo_beq___main(x_19, x_22);
if (x_28 == 0)
{
uint8 x_30; 
lean::dec(x_0);
x_30 = 0;
return x_30;
}
else
{
uint8 x_31; 
x_31 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_20, x_23);
return x_31;
}
}
}
default:
{
uint8 x_33; 
lean::dec(x_0);
x_33 = 0;
return x_33;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; uint8 x_38; 
x_34 = lean::cnstr_get(x_1, 0);
x_35 = lean::cnstr_get(x_1, 1);
x_36 = lean::cnstr_get(x_2, 0);
x_37 = lean::cnstr_get(x_2, 1);
x_38 = lean::nat_dec_eq(x_34, x_36);
if (x_38 == 0)
{
uint8 x_40; 
lean::dec(x_0);
x_40 = 0;
return x_40;
}
else
{
uint8 x_41; 
x_41 = l_Lean_IR_VarId_alphaEqv(x_0, x_35, x_37);
return x_41;
}
}
default:
{
uint8 x_43; 
lean::dec(x_0);
x_43 = 0;
return x_43;
}
}
}
case 4:
{
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; uint8 x_48; 
x_44 = lean::cnstr_get(x_1, 0);
x_45 = lean::cnstr_get(x_1, 1);
x_46 = lean::cnstr_get(x_2, 0);
x_47 = lean::cnstr_get(x_2, 1);
x_48 = lean::nat_dec_eq(x_44, x_46);
if (x_48 == 0)
{
uint8 x_50; 
lean::dec(x_0);
x_50 = 0;
return x_50;
}
else
{
uint8 x_51; 
x_51 = l_Lean_IR_VarId_alphaEqv(x_0, x_45, x_47);
return x_51;
}
}
default:
{
uint8 x_53; 
lean::dec(x_0);
x_53 = 0;
return x_53;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; uint8 x_58; 
x_54 = lean::cnstr_get(x_1, 0);
x_55 = lean::cnstr_get(x_1, 1);
x_56 = lean::cnstr_get(x_2, 0);
x_57 = lean::cnstr_get(x_2, 1);
x_58 = lean::nat_dec_eq(x_54, x_56);
if (x_58 == 0)
{
uint8 x_60; 
lean::dec(x_0);
x_60 = 0;
return x_60;
}
else
{
uint8 x_61; 
x_61 = l_Lean_IR_VarId_alphaEqv(x_0, x_55, x_57);
return x_61;
}
}
default:
{
uint8 x_63; 
lean::dec(x_0);
x_63 = 0;
return x_63;
}
}
}
case 6:
{
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; uint8 x_68; 
x_64 = lean::cnstr_get(x_1, 0);
x_65 = lean::cnstr_get(x_1, 1);
x_66 = lean::cnstr_get(x_2, 0);
x_67 = lean::cnstr_get(x_2, 1);
x_68 = lean_name_dec_eq(x_64, x_66);
if (x_68 == 0)
{
uint8 x_70; 
lean::dec(x_0);
x_70 = 0;
return x_70;
}
else
{
uint8 x_71; 
x_71 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_65, x_67);
return x_71;
}
}
default:
{
uint8 x_73; 
lean::dec(x_0);
x_73 = 0;
return x_73;
}
}
}
case 7:
{
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_74; obj* x_75; obj* x_76; uint8 x_77; 
x_74 = lean::cnstr_get(x_1, 0);
x_75 = lean::cnstr_get(x_2, 0);
x_76 = lean::cnstr_get(x_2, 1);
x_77 = lean_name_dec_eq(x_74, x_75);
if (x_77 == 0)
{
uint8 x_79; 
lean::dec(x_0);
x_79 = 0;
return x_79;
}
else
{
uint8 x_80; 
x_80 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_76, x_76);
return x_80;
}
}
default:
{
uint8 x_82; 
lean::dec(x_0);
x_82 = 0;
return x_82;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; uint8 x_88; 
x_83 = lean::cnstr_get(x_1, 0);
x_84 = lean::cnstr_get(x_1, 1);
x_85 = lean::cnstr_get(x_2, 0);
x_86 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_88 = l_Lean_IR_VarId_alphaEqv(x_0, x_83, x_85);
if (x_88 == 0)
{
uint8 x_90; 
lean::dec(x_0);
x_90 = 0;
return x_90;
}
else
{
uint8 x_91; 
x_91 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_84, x_86);
return x_91;
}
}
default:
{
uint8 x_93; 
lean::dec(x_0);
x_93 = 0;
return x_93;
}
}
}
case 9:
{
uint8 x_94; 
x_94 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_95; uint8 x_96; obj* x_97; uint8 x_98; 
x_95 = lean::cnstr_get(x_1, 0);
x_96 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_97 = lean::cnstr_get(x_2, 0);
x_98 = l_Lean_IR_IRType_beq___main(x_94, x_96);
if (x_98 == 0)
{
uint8 x_100; 
lean::dec(x_0);
x_100 = 0;
return x_100;
}
else
{
uint8 x_101; 
x_101 = l_Lean_IR_VarId_alphaEqv(x_0, x_95, x_97);
return x_101;
}
}
default:
{
uint8 x_103; 
lean::dec(x_0);
x_103 = 0;
return x_103;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_104; obj* x_105; uint8 x_106; 
x_104 = lean::cnstr_get(x_1, 0);
x_105 = lean::cnstr_get(x_2, 0);
x_106 = l_Lean_IR_VarId_alphaEqv(x_0, x_104, x_105);
return x_106;
}
default:
{
uint8 x_108; 
lean::dec(x_0);
x_108 = 0;
return x_108;
}
}
}
case 11:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_110; obj* x_111; uint8 x_112; 
x_110 = lean::cnstr_get(x_1, 0);
x_111 = lean::cnstr_get(x_2, 0);
x_112 = l_Lean_IR_LitVal_beq___main(x_110, x_111);
return x_112;
}
default:
{
uint8 x_113; 
x_113 = 0;
return x_113;
}
}
}
case 12:
{
switch (lean::obj_tag(x_2)) {
case 12:
{
obj* x_114; obj* x_115; uint8 x_116; 
x_114 = lean::cnstr_get(x_1, 0);
x_115 = lean::cnstr_get(x_2, 0);
x_116 = l_Lean_IR_VarId_alphaEqv(x_0, x_114, x_115);
return x_116;
}
default:
{
uint8 x_118; 
lean::dec(x_0);
x_118 = 0;
return x_118;
}
}
}
default:
{
switch (lean::obj_tag(x_2)) {
case 13:
{
obj* x_119; obj* x_120; uint8 x_121; 
x_119 = lean::cnstr_get(x_1, 0);
x_120 = lean::cnstr_get(x_2, 0);
x_121 = l_Lean_IR_VarId_alphaEqv(x_0, x_119, x_120);
return x_121;
}
default:
{
uint8 x_123; 
lean::dec(x_0);
x_123 = 0;
return x_123;
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
obj* l_Lean_IR_addVarRename(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean_name_dec_eq(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_Lean_NameMap_insert___rarg(x_0, x_1, x_2);
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
x_13 = lean::array_index(x_1, x_3);
x_14 = lean::array_index(x_2, x_3);
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
x_506 = l_Lean_IR_VarId_alphaEqv(x_0, x_500, x_503);
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
x_526 = lean_name_dec_eq(x_516, x_521);
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
obj* l___private_init_lean_compiler_ir_1__skip___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_1__skip(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_1__skip___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_1__skip___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_1__skip___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_1__skip___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_1__skip(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_2__collectVar(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_NameSet_contains(x_1, x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_Lean_NameSet_insert(x_2, x_0);
return x_4;
}
else
{
lean::dec(x_0);
return x_2;
}
}
}
obj* l___private_init_lean_compiler_ir_3__withBv(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_NameSet_insert(x_2, x_0);
x_5 = lean::apply_2(x_1, x_4, x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_insertParams___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::array_index(x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_12 = l_Lean_NameSet_insert(x_3, x_9);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
x_2 = x_14;
x_3 = x_12;
goto _start;
}
}
}
obj* l_Lean_IR_insertParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at_Lean_IR_insertParams___spec__1(x_1, x_1, x_2, x_0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_insertParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_insertParams___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_insertParams___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_insertParams(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_4__withParams(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at_Lean_IR_insertParams___spec__1(x_0, x_0, x_4, x_2);
x_6 = lean::apply_2(x_1, x_5, x_3);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_4__withParams___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_4__withParams(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_5__seq(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::apply_2(x_1, x_2, x_5);
return x_6;
}
}
obj* _init_l_Lean_IR_HasAndthen() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_5__seq), 4, 0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_6__collectArg___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; uint8 x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_NameSet_contains(x_1, x_3);
if (x_6 == 0)
{
obj* x_7; 
x_7 = l_Lean_NameSet_insert(x_2, x_3);
return x_7;
}
else
{
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
obj* l___private_init_lean_compiler_ir_6__collectArg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_6__collectArg___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
x_12 = lean::array_index(x_3, x_4);
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
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_7__collectArray___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___rarg(x_0, x_1, x_2, x_0, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_7__collectArray(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_7__collectArray___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_3);
return x_6;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_7__collectArray___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_7__collectArray___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_7__collectArray___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_7__collectArray___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_7__collectArray(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_10 = lean::array_index(x_2, x_3);
lean::inc(x_1);
x_12 = l___private_init_lean_compiler_ir_6__collectArg___main(x_10, x_1, x_4);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
obj* l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_8__collectArgs___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_0, x_1, x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_8__collectArgs(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_0, x_1, x_0, x_3, x_2);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_8__collectArgs___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_8__collectArgs___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_8__collectArgs___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_8__collectArgs(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_compiler_ir_9__collectExpr___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0ul);
x_7 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_3, x_1, x_3, x_6, x_2);
lean::dec(x_3);
return x_7;
}
case 2:
{
obj* x_9; obj* x_11; uint8 x_15; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 2);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_1);
x_15 = l_Lean_NameSet_contains(x_1, x_9);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = l_Lean_NameSet_insert(x_2, x_9);
x_17 = lean::mk_nat_obj(0ul);
x_18 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_11, x_1, x_11, x_17, x_16);
lean::dec(x_11);
return x_18;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_9);
x_21 = lean::mk_nat_obj(0ul);
x_22 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_11, x_1, x_11, x_21, x_2);
lean::dec(x_11);
return x_22;
}
}
case 3:
{
obj* x_24; uint8 x_27; 
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
lean::dec(x_0);
x_27 = l_Lean_NameSet_contains(x_1, x_24);
if (x_27 == 0)
{
obj* x_28; 
x_28 = l_Lean_NameSet_insert(x_2, x_24);
return x_28;
}
else
{
lean::dec(x_24);
return x_2;
}
}
case 4:
{
obj* x_30; uint8 x_33; 
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::dec(x_0);
x_33 = l_Lean_NameSet_contains(x_1, x_30);
if (x_33 == 0)
{
obj* x_34; 
x_34 = l_Lean_NameSet_insert(x_2, x_30);
return x_34;
}
else
{
lean::dec(x_30);
return x_2;
}
}
case 5:
{
obj* x_36; uint8 x_39; 
x_36 = lean::cnstr_get(x_0, 1);
lean::inc(x_36);
lean::dec(x_0);
x_39 = l_Lean_NameSet_contains(x_1, x_36);
if (x_39 == 0)
{
obj* x_40; 
x_40 = l_Lean_NameSet_insert(x_2, x_36);
return x_40;
}
else
{
lean::dec(x_36);
return x_2;
}
}
case 6:
{
obj* x_42; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_0, 1);
lean::inc(x_42);
lean::dec(x_0);
x_45 = lean::mk_nat_obj(0ul);
x_46 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_42, x_1, x_42, x_45, x_2);
lean::dec(x_42);
return x_46;
}
case 7:
{
obj* x_48; obj* x_51; obj* x_52; 
x_48 = lean::cnstr_get(x_0, 1);
lean::inc(x_48);
lean::dec(x_0);
x_51 = lean::mk_nat_obj(0ul);
x_52 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_48, x_1, x_48, x_51, x_2);
lean::dec(x_48);
return x_52;
}
case 8:
{
obj* x_54; obj* x_56; uint8 x_60; 
x_54 = lean::cnstr_get(x_0, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_0, 1);
lean::inc(x_56);
lean::dec(x_0);
lean::inc(x_1);
x_60 = l_Lean_NameSet_contains(x_1, x_54);
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; 
x_61 = l_Lean_NameSet_insert(x_2, x_54);
x_62 = lean::mk_nat_obj(0ul);
x_63 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_56, x_1, x_56, x_62, x_61);
lean::dec(x_56);
return x_63;
}
else
{
obj* x_66; obj* x_67; 
lean::dec(x_54);
x_66 = lean::mk_nat_obj(0ul);
x_67 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_56, x_1, x_56, x_66, x_2);
lean::dec(x_56);
return x_67;
}
}
case 11:
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
default:
{
obj* x_71; uint8 x_74; 
x_71 = lean::cnstr_get(x_0, 0);
lean::inc(x_71);
lean::dec(x_0);
x_74 = l_Lean_NameSet_contains(x_1, x_71);
if (x_74 == 0)
{
obj* x_75; 
x_75 = l_Lean_NameSet_insert(x_2, x_71);
return x_75;
}
else
{
lean::dec(x_71);
return x_2;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_9__collectExpr(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_9__collectExpr___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::array_index(x_3, x_4);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_4, x_13);
lean::dec(x_4);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_21; 
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::dec(x_12);
lean::inc(x_2);
lean::inc(x_0);
x_21 = lean::apply_3(x_0, x_16, x_2, x_5);
x_4 = x_14;
x_5 = x_21;
goto _start;
}
else
{
obj* x_23; obj* x_28; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
lean::dec(x_12);
lean::inc(x_2);
lean::inc(x_0);
x_28 = lean::apply_3(x_0, x_23, x_2, x_5);
x_4 = x_14;
x_5 = x_28;
goto _start;
}
}
}
}
obj* l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_10__collectAlts___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2(x_0, x_1, x_2, x_1, x_4, x_3);
return x_5;
}
}
obj* l___private_init_lean_compiler_ir_10__collectAlts(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0ul);
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2(x_0, x_1, x_2, x_1, x_4, x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
lean::dec(x_3);
return x_6;
}
}
obj* l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_10__collectAlts___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_7__collectArray___at___private_init_lean_compiler_ir_10__collectAlts___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_10__collectAlts___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_10__collectAlts(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l___private_init_lean_compiler_ir_11__collectFnBody___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_11__collectFnBody___main), 3, 0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_11__collectFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
lean::inc(x_1);
x_11 = l___private_init_lean_compiler_ir_9__collectExpr___main(x_5, x_1, x_2);
x_12 = l_Lean_NameSet_insert(x_1, x_3);
x_0 = x_7;
x_1 = x_12;
x_2 = x_11;
goto _start;
}
case 1:
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 2);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 3);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_25 = l_Array_miterateAux___main___at_Lean_IR_insertParams___spec__1(x_16, x_16, x_23, x_1);
lean::dec(x_16);
x_27 = l___private_init_lean_compiler_ir_11__collectFnBody___main(x_18, x_25, x_2);
x_28 = l_Lean_NameSet_insert(x_1, x_14);
x_0 = x_20;
x_1 = x_28;
x_2 = x_27;
goto _start;
}
case 2:
{
obj* x_30; obj* x_32; obj* x_34; uint8 x_38; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 2);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 3);
lean::inc(x_34);
lean::dec(x_0);
lean::inc(x_1);
x_38 = l_Lean_NameSet_contains(x_1, x_30);
lean::inc(x_1);
x_40 = l_Lean_NameSet_contains(x_1, x_32);
if (x_38 == 0)
{
obj* x_41; 
x_41 = l_Lean_NameSet_insert(x_2, x_30);
if (x_40 == 0)
{
obj* x_42; 
x_42 = l_Lean_NameSet_insert(x_41, x_32);
x_0 = x_34;
x_2 = x_42;
goto _start;
}
else
{
lean::dec(x_32);
x_0 = x_34;
x_2 = x_41;
goto _start;
}
}
else
{
lean::dec(x_30);
if (x_40 == 0)
{
obj* x_47; 
x_47 = l_Lean_NameSet_insert(x_2, x_32);
x_0 = x_34;
x_2 = x_47;
goto _start;
}
else
{
lean::dec(x_32);
x_0 = x_34;
goto _start;
}
}
}
case 3:
{
obj* x_51; obj* x_53; obj* x_55; uint8 x_59; uint8 x_61; 
x_51 = lean::cnstr_get(x_0, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_0, 2);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_0, 3);
lean::inc(x_55);
lean::dec(x_0);
lean::inc(x_1);
x_59 = l_Lean_NameSet_contains(x_1, x_51);
lean::inc(x_1);
x_61 = l_Lean_NameSet_contains(x_1, x_53);
if (x_59 == 0)
{
obj* x_62; 
x_62 = l_Lean_NameSet_insert(x_2, x_51);
if (x_61 == 0)
{
obj* x_63; 
x_63 = l_Lean_NameSet_insert(x_62, x_53);
x_0 = x_55;
x_2 = x_63;
goto _start;
}
else
{
lean::dec(x_53);
x_0 = x_55;
x_2 = x_62;
goto _start;
}
}
else
{
lean::dec(x_51);
if (x_61 == 0)
{
obj* x_68; 
x_68 = l_Lean_NameSet_insert(x_2, x_53);
x_0 = x_55;
x_2 = x_68;
goto _start;
}
else
{
lean::dec(x_53);
x_0 = x_55;
goto _start;
}
}
}
case 4:
{
obj* x_72; obj* x_74; obj* x_76; uint8 x_80; uint8 x_82; 
x_72 = lean::cnstr_get(x_0, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_0, 3);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_0, 4);
lean::inc(x_76);
lean::dec(x_0);
lean::inc(x_1);
x_80 = l_Lean_NameSet_contains(x_1, x_72);
lean::inc(x_1);
x_82 = l_Lean_NameSet_contains(x_1, x_74);
if (x_80 == 0)
{
obj* x_83; 
x_83 = l_Lean_NameSet_insert(x_2, x_72);
if (x_82 == 0)
{
obj* x_84; 
x_84 = l_Lean_NameSet_insert(x_83, x_74);
x_0 = x_76;
x_2 = x_84;
goto _start;
}
else
{
lean::dec(x_74);
x_0 = x_76;
x_2 = x_83;
goto _start;
}
}
else
{
lean::dec(x_72);
if (x_82 == 0)
{
obj* x_89; 
x_89 = l_Lean_NameSet_insert(x_2, x_74);
x_0 = x_76;
x_2 = x_89;
goto _start;
}
else
{
lean::dec(x_74);
x_0 = x_76;
goto _start;
}
}
}
case 8:
{
obj* x_93; 
x_93 = lean::cnstr_get(x_0, 1);
lean::inc(x_93);
lean::dec(x_0);
x_0 = x_93;
goto _start;
}
case 9:
{
obj* x_97; obj* x_99; uint8 x_103; 
x_97 = lean::cnstr_get(x_0, 1);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_0, 2);
lean::inc(x_99);
lean::dec(x_0);
lean::inc(x_1);
x_103 = l_Lean_NameSet_contains(x_1, x_97);
if (x_103 == 0)
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_104 = l_Lean_NameSet_insert(x_2, x_97);
x_105 = l___private_init_lean_compiler_ir_11__collectFnBody___main___closed__1;
x_106 = lean::mk_nat_obj(0ul);
x_107 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2(x_105, x_99, x_1, x_99, x_106, x_104);
lean::dec(x_99);
return x_107;
}
else
{
obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_97);
x_110 = l___private_init_lean_compiler_ir_11__collectFnBody___main___closed__1;
x_111 = lean::mk_nat_obj(0ul);
x_112 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_10__collectAlts___spec__2(x_110, x_99, x_1, x_99, x_111, x_2);
lean::dec(x_99);
return x_112;
}
}
case 10:
{
obj* x_114; uint8 x_117; 
x_114 = lean::cnstr_get(x_0, 0);
lean::inc(x_114);
lean::dec(x_0);
x_117 = l_Lean_NameSet_contains(x_1, x_114);
if (x_117 == 0)
{
obj* x_118; 
x_118 = l_Lean_NameSet_insert(x_2, x_114);
return x_118;
}
else
{
lean::dec(x_114);
return x_2;
}
}
case 11:
{
obj* x_120; obj* x_122; uint8 x_126; 
x_120 = lean::cnstr_get(x_0, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_0, 1);
lean::inc(x_122);
lean::dec(x_0);
lean::inc(x_1);
x_126 = l_Lean_NameSet_contains(x_1, x_120);
if (x_126 == 0)
{
obj* x_127; obj* x_128; obj* x_129; 
x_127 = l_Lean_NameSet_insert(x_2, x_120);
x_128 = lean::mk_nat_obj(0ul);
x_129 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_122, x_1, x_122, x_128, x_127);
lean::dec(x_122);
return x_129;
}
else
{
obj* x_132; obj* x_133; 
lean::dec(x_120);
x_132 = lean::mk_nat_obj(0ul);
x_133 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_8__collectArgs___spec__2(x_122, x_1, x_122, x_132, x_2);
lean::dec(x_122);
return x_133;
}
}
case 12:
{
lean::dec(x_1);
return x_2;
}
default:
{
obj* x_136; obj* x_138; uint8 x_142; 
x_136 = lean::cnstr_get(x_0, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_0, 2);
lean::inc(x_138);
lean::dec(x_0);
lean::inc(x_1);
x_142 = l_Lean_NameSet_contains(x_1, x_136);
if (x_142 == 0)
{
obj* x_143; 
x_143 = l_Lean_NameSet_insert(x_2, x_136);
x_0 = x_138;
x_2 = x_143;
goto _start;
}
else
{
lean::dec(x_136);
x_0 = x_138;
goto _start;
}
}
}
}
}
obj* l___private_init_lean_compiler_ir_11__collectFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_11__collectFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_freeVars(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = l___private_init_lean_compiler_ir_11__collectFnBody___main(x_0, x_1, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_compiler_ir_12__formatArg___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("\xe2\x97\xbe");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_12__formatArg___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Lean_Name_toString___closed__1;
x_5 = l_Lean_Name_toStringWithSep___main(x_4, x_1);
x_6 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
else
{
obj* x_7; 
x_7 = l___private_init_lean_compiler_ir_12__formatArg___main___closed__1;
return x_7;
}
}
}
obj* l___private_init_lean_compiler_ir_12__formatArg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_12__formatArg___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_argHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_12__formatArg), 1, 0);
return x_0;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_13__formatArgs___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_index(x_2, x_3);
x_11 = lean::mk_nat_obj(0ul);
x_12 = lean::nat_dec_lt(x_11, x_3);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
if (x_12 == 0)
{
obj* x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_16 = l___private_init_lean_compiler_ir_12__formatArg___main(x_10);
x_17 = 0;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_17);
x_19 = x_18;
x_3 = x_14;
x_4 = x_19;
goto _start;
}
else
{
uint8 x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = 0;
lean::inc(x_1);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_21);
x_24 = x_23;
x_25 = l___private_init_lean_compiler_ir_12__formatArg___main(x_10);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_21);
x_27 = x_26;
x_3 = x_14;
x_4 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_Format_joinArraySep___at___private_init_lean_compiler_ir_13__formatArgs___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::box(0);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_13__formatArgs___spec__2(x_0, x_1, x_0, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_compiler_ir_13__formatArgs(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_Format_flatten___main___closed__1;
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::box(0);
x_4 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_13__formatArgs___spec__2(x_0, x_1, x_0, x_2, x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at___private_init_lean_compiler_ir_13__formatArgs___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at___private_init_lean_compiler_ir_13__formatArgs___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Format_joinArraySep___at___private_init_lean_compiler_ir_13__formatArgs___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_joinArraySep___at___private_init_lean_compiler_ir_13__formatArgs___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_13__formatArgs___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_13__formatArgs(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_argsHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_13__formatArgs___boxed), 1, 0);
return x_0;
}
}
obj* l___private_init_lean_compiler_ir_14__formatLitVal___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; obj* x_4; obj* x_5; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = l_Nat_repr(x_1);
x_5 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = l_String_quote(x_6);
x_10 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
obj* l___private_init_lean_compiler_ir_14__formatLitVal(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_14__formatLitVal___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_litValHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_14__formatLitVal), 1, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("ctor_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(".");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_15__formatCtorInfo___main(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; obj* x_18; uint8 x_19; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_Nat_repr(x_3);
x_11 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = 0;
x_13 = l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__1;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_11);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_12);
x_15 = x_14;
x_16 = lean::mk_nat_obj(0ul);
x_17 = lean::nat_dec_lt(x_16, x_5);
x_18 = lean::box(0);
x_19 = lean_name_dec_eq(x_1, x_18);
if (x_17 == 0)
{
uint8 x_20; 
x_20 = lean::nat_dec_lt(x_16, x_7);
if (x_20 == 0)
{
lean::dec(x_7);
lean::dec(x_5);
if (x_19 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_23 = l_Lean_Format_sbracket___closed__1;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_15);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_12);
x_25 = x_24;
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set(x_29, 1, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_12);
x_30 = x_29;
x_31 = l_Lean_Format_sbracket___closed__2;
x_32 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_31);
lean::cnstr_set_scalar(x_32, sizeof(void*)*2, x_12);
x_33 = x_32;
return x_33;
}
else
{
lean::dec(x_1);
return x_15;
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_35 = l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__2;
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_15);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_12);
x_37 = x_36;
x_38 = l_Nat_repr(x_5);
x_39 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_37);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_12);
x_41 = x_40;
x_42 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_35);
lean::cnstr_set_scalar(x_42, sizeof(void*)*2, x_12);
x_43 = x_42;
x_44 = l_Nat_repr(x_7);
x_45 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
x_46 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set_scalar(x_46, sizeof(void*)*2, x_12);
x_47 = x_46;
if (x_19 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_48 = l_Lean_Format_sbracket___closed__1;
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_12);
x_50 = x_49;
x_51 = l_Lean_Name_toString___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_1);
x_53 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set(x_54, 1, x_53);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_12);
x_55 = x_54;
x_56 = l_Lean_Format_sbracket___closed__2;
x_57 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
lean::cnstr_set_scalar(x_57, sizeof(void*)*2, x_12);
x_58 = x_57;
return x_58;
}
else
{
lean::dec(x_1);
return x_47;
}
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_60 = l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__2;
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_15);
lean::cnstr_set(x_61, 1, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_12);
x_62 = x_61;
x_63 = l_Nat_repr(x_5);
x_64 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_65, 0, x_62);
lean::cnstr_set(x_65, 1, x_64);
lean::cnstr_set_scalar(x_65, sizeof(void*)*2, x_12);
x_66 = x_65;
x_67 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_60);
lean::cnstr_set_scalar(x_67, sizeof(void*)*2, x_12);
x_68 = x_67;
x_69 = l_Nat_repr(x_7);
x_70 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_70);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_12);
x_72 = x_71;
if (x_19 == 0)
{
obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_73 = l_Lean_Format_sbracket___closed__1;
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_73);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_12);
x_75 = x_74;
x_76 = l_Lean_Name_toString___closed__1;
x_77 = l_Lean_Name_toStringWithSep___main(x_76, x_1);
x_78 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_79, 0, x_75);
lean::cnstr_set(x_79, 1, x_78);
lean::cnstr_set_scalar(x_79, sizeof(void*)*2, x_12);
x_80 = x_79;
x_81 = l_Lean_Format_sbracket___closed__2;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_81);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_12);
x_83 = x_82;
return x_83;
}
else
{
lean::dec(x_1);
return x_72;
}
}
}
}
obj* l___private_init_lean_compiler_ir_15__formatCtorInfo(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_15__formatCtorInfo___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_ctorInfoHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_15__formatCtorInfo), 1, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("reset ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("reuse ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" in ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("proj_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("uproj_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("sproj_");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("pap ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("app ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("box ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__10() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unbox ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__11() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("isShared ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__12() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("isTaggedPtr ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_16__formatExpr___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_3; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l___private_init_lean_compiler_ir_15__formatCtorInfo___main(x_1);
x_7 = 0;
x_8 = l_Lean_Format_flatten___main___closed__1;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
x_10 = x_9;
x_11 = l___private_init_lean_compiler_ir_13__formatArgs(x_3);
lean::dec(x_3);
x_13 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set_scalar(x_13, sizeof(void*)*2, x_7);
x_14 = x_13;
return x_14;
}
case 1:
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_15);
x_20 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = 0;
x_22 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__1;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_21);
x_24 = x_23;
return x_24;
}
case 2:
{
obj* x_25; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_34; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_0, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_0, 2);
lean::inc(x_29);
lean::dec(x_0);
x_32 = l_Lean_Name_toString___closed__1;
x_33 = l_Lean_Name_toStringWithSep___main(x_32, x_25);
x_34 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = 0;
x_36 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__2;
x_37 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_34);
lean::cnstr_set_scalar(x_37, sizeof(void*)*2, x_35);
x_38 = x_37;
x_39 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__3;
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_35);
x_41 = x_40;
x_42 = l___private_init_lean_compiler_ir_15__formatCtorInfo___main(x_27);
x_43 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
lean::cnstr_set_scalar(x_43, sizeof(void*)*2, x_35);
x_44 = x_43;
x_45 = l___private_init_lean_compiler_ir_13__formatArgs(x_29);
lean::dec(x_29);
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_45);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_35);
x_48 = x_47;
return x_48;
}
case 3:
{
obj* x_49; obj* x_51; obj* x_54; obj* x_55; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_49 = lean::cnstr_get(x_0, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_0, 1);
lean::inc(x_51);
lean::dec(x_0);
x_54 = l_Nat_repr(x_49);
x_55 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = 0;
x_57 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__4;
x_58 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_55);
lean::cnstr_set_scalar(x_58, sizeof(void*)*2, x_56);
x_59 = x_58;
x_60 = l_Lean_Format_flatten___main___closed__1;
x_61 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set(x_61, 1, x_60);
lean::cnstr_set_scalar(x_61, sizeof(void*)*2, x_56);
x_62 = x_61;
x_63 = l_Lean_Name_toString___closed__1;
x_64 = l_Lean_Name_toStringWithSep___main(x_63, x_51);
x_65 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set(x_66, 1, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_56);
x_67 = x_66;
return x_67;
}
case 4:
{
obj* x_68; obj* x_70; obj* x_73; obj* x_74; uint8 x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_68 = lean::cnstr_get(x_0, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_0, 1);
lean::inc(x_70);
lean::dec(x_0);
x_73 = l_Nat_repr(x_68);
x_74 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
x_75 = 0;
x_76 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__5;
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_74);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_75);
x_78 = x_77;
x_79 = l_Lean_Format_flatten___main___closed__1;
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_75);
x_81 = x_80;
x_82 = l_Lean_Name_toString___closed__1;
x_83 = l_Lean_Name_toStringWithSep___main(x_82, x_70);
x_84 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
x_85 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set(x_85, 1, x_84);
lean::cnstr_set_scalar(x_85, sizeof(void*)*2, x_75);
x_86 = x_85;
return x_86;
}
case 5:
{
obj* x_87; obj* x_89; obj* x_92; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_87 = lean::cnstr_get(x_0, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_0, 1);
lean::inc(x_89);
lean::dec(x_0);
x_92 = l_Nat_repr(x_87);
x_93 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
x_94 = 0;
x_95 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__6;
x_96 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_93);
lean::cnstr_set_scalar(x_96, sizeof(void*)*2, x_94);
x_97 = x_96;
x_98 = l_Lean_Format_flatten___main___closed__1;
x_99 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*2, x_94);
x_100 = x_99;
x_101 = l_Lean_Name_toString___closed__1;
x_102 = l_Lean_Name_toStringWithSep___main(x_101, x_89);
x_103 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_103, 0, x_102);
x_104 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set(x_104, 1, x_103);
lean::cnstr_set_scalar(x_104, sizeof(void*)*2, x_94);
x_105 = x_104;
return x_105;
}
case 6:
{
obj* x_106; obj* x_108; obj* x_111; obj* x_112; obj* x_113; uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_120; obj* x_121; 
x_106 = lean::cnstr_get(x_0, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_0, 1);
lean::inc(x_108);
lean::dec(x_0);
x_111 = l_Lean_Name_toString___closed__1;
x_112 = l_Lean_Name_toStringWithSep___main(x_111, x_106);
x_113 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_113, 0, x_112);
x_114 = 0;
x_115 = l_Lean_Format_flatten___main___closed__1;
x_116 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_116, 0, x_113);
lean::cnstr_set(x_116, 1, x_115);
lean::cnstr_set_scalar(x_116, sizeof(void*)*2, x_114);
x_117 = x_116;
x_118 = l___private_init_lean_compiler_ir_13__formatArgs(x_108);
lean::dec(x_108);
x_120 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_120, 0, x_117);
lean::cnstr_set(x_120, 1, x_118);
lean::cnstr_set_scalar(x_120, sizeof(void*)*2, x_114);
x_121 = x_120;
return x_121;
}
case 7:
{
obj* x_122; obj* x_124; obj* x_127; obj* x_128; obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_139; obj* x_140; 
x_122 = lean::cnstr_get(x_0, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_0, 1);
lean::inc(x_124);
lean::dec(x_0);
x_127 = l_Lean_Name_toString___closed__1;
x_128 = l_Lean_Name_toStringWithSep___main(x_127, x_122);
x_129 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_129, 0, x_128);
x_130 = 0;
x_131 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__7;
x_132 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_129);
lean::cnstr_set_scalar(x_132, sizeof(void*)*2, x_130);
x_133 = x_132;
x_134 = l_Lean_Format_flatten___main___closed__1;
x_135 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set(x_135, 1, x_134);
lean::cnstr_set_scalar(x_135, sizeof(void*)*2, x_130);
x_136 = x_135;
x_137 = l___private_init_lean_compiler_ir_13__formatArgs(x_124);
lean::dec(x_124);
x_139 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_139, 0, x_136);
lean::cnstr_set(x_139, 1, x_137);
lean::cnstr_set_scalar(x_139, sizeof(void*)*2, x_130);
x_140 = x_139;
return x_140;
}
case 8:
{
obj* x_141; obj* x_143; obj* x_146; obj* x_147; obj* x_148; uint8 x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_158; obj* x_159; 
x_141 = lean::cnstr_get(x_0, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_0, 1);
lean::inc(x_143);
lean::dec(x_0);
x_146 = l_Lean_Name_toString___closed__1;
x_147 = l_Lean_Name_toStringWithSep___main(x_146, x_141);
x_148 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_148, 0, x_147);
x_149 = 0;
x_150 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__8;
x_151 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_151, 0, x_150);
lean::cnstr_set(x_151, 1, x_148);
lean::cnstr_set_scalar(x_151, sizeof(void*)*2, x_149);
x_152 = x_151;
x_153 = l_Lean_Format_flatten___main___closed__1;
x_154 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_154, 0, x_152);
lean::cnstr_set(x_154, 1, x_153);
lean::cnstr_set_scalar(x_154, sizeof(void*)*2, x_149);
x_155 = x_154;
x_156 = l___private_init_lean_compiler_ir_13__formatArgs(x_143);
lean::dec(x_143);
x_158 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_158, 0, x_155);
lean::cnstr_set(x_158, 1, x_156);
lean::cnstr_set_scalar(x_158, sizeof(void*)*2, x_149);
x_159 = x_158;
return x_159;
}
case 9:
{
obj* x_160; obj* x_163; obj* x_164; obj* x_165; uint8 x_166; obj* x_167; obj* x_168; obj* x_169; 
x_160 = lean::cnstr_get(x_0, 0);
lean::inc(x_160);
lean::dec(x_0);
x_163 = l_Lean_Name_toString___closed__1;
x_164 = l_Lean_Name_toStringWithSep___main(x_163, x_160);
x_165 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_165, 0, x_164);
x_166 = 0;
x_167 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__9;
x_168 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_165);
lean::cnstr_set_scalar(x_168, sizeof(void*)*2, x_166);
x_169 = x_168;
return x_169;
}
case 10:
{
obj* x_170; obj* x_173; obj* x_174; obj* x_175; uint8 x_176; obj* x_177; obj* x_178; obj* x_179; 
x_170 = lean::cnstr_get(x_0, 0);
lean::inc(x_170);
lean::dec(x_0);
x_173 = l_Lean_Name_toString___closed__1;
x_174 = l_Lean_Name_toStringWithSep___main(x_173, x_170);
x_175 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_175, 0, x_174);
x_176 = 0;
x_177 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__10;
x_178 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_175);
lean::cnstr_set_scalar(x_178, sizeof(void*)*2, x_176);
x_179 = x_178;
return x_179;
}
case 11:
{
obj* x_180; obj* x_183; 
x_180 = lean::cnstr_get(x_0, 0);
lean::inc(x_180);
lean::dec(x_0);
x_183 = l___private_init_lean_compiler_ir_14__formatLitVal___main(x_180);
return x_183;
}
case 12:
{
obj* x_184; obj* x_187; obj* x_188; obj* x_189; uint8 x_190; obj* x_191; obj* x_192; obj* x_193; 
x_184 = lean::cnstr_get(x_0, 0);
lean::inc(x_184);
lean::dec(x_0);
x_187 = l_Lean_Name_toString___closed__1;
x_188 = l_Lean_Name_toStringWithSep___main(x_187, x_184);
x_189 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_189, 0, x_188);
x_190 = 0;
x_191 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__11;
x_192 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_192, 0, x_191);
lean::cnstr_set(x_192, 1, x_189);
lean::cnstr_set_scalar(x_192, sizeof(void*)*2, x_190);
x_193 = x_192;
return x_193;
}
default:
{
obj* x_194; obj* x_197; obj* x_198; obj* x_199; uint8 x_200; obj* x_201; obj* x_202; obj* x_203; 
x_194 = lean::cnstr_get(x_0, 0);
lean::inc(x_194);
lean::dec(x_0);
x_197 = l_Lean_Name_toString___closed__1;
x_198 = l_Lean_Name_toStringWithSep___main(x_197, x_194);
x_199 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_199, 0, x_198);
x_200 = 0;
x_201 = l___private_init_lean_compiler_ir_16__formatExpr___main___closed__12;
x_202 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_202, 0, x_201);
lean::cnstr_set(x_202, 1, x_199);
lean::cnstr_set_scalar(x_202, sizeof(void*)*2, x_200);
x_203 = x_202;
return x_203;
}
}
}
}
obj* l___private_init_lean_compiler_ir_16__formatExpr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_16__formatExpr___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_exprHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_16__formatExpr), 1, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("float");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("u8");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("u16");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("u32");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("u64");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("usize");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("obj");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("tobj");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_17__formatIRType___main(uint8 x_0) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_17__formatIRType___main___closed__1;
return x_1;
}
case 1:
{
obj* x_2; 
x_2 = l___private_init_lean_compiler_ir_17__formatIRType___main___closed__2;
return x_2;
}
case 2:
{
obj* x_3; 
x_3 = l___private_init_lean_compiler_ir_17__formatIRType___main___closed__3;
return x_3;
}
case 3:
{
obj* x_4; 
x_4 = l___private_init_lean_compiler_ir_17__formatIRType___main___closed__4;
return x_4;
}
case 4:
{
obj* x_5; 
x_5 = l___private_init_lean_compiler_ir_17__formatIRType___main___closed__5;
return x_5;
}
case 5:
{
obj* x_6; 
x_6 = l___private_init_lean_compiler_ir_17__formatIRType___main___closed__6;
return x_6;
}
case 6:
{
obj* x_7; 
x_7 = l___private_init_lean_compiler_ir_12__formatArg___main___closed__1;
return x_7;
}
case 7:
{
obj* x_8; 
x_8 = l___private_init_lean_compiler_ir_17__formatIRType___main___closed__7;
return x_8;
}
default:
{
obj* x_9; 
x_9 = l___private_init_lean_compiler_ir_17__formatIRType___main___closed__8;
return x_9;
}
}
}
}
obj* l___private_init_lean_compiler_ir_17__formatIRType___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l___private_init_lean_compiler_ir_17__formatIRType___main(x_1);
return x_2;
}
}
obj* l___private_init_lean_compiler_ir_17__formatIRType(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_17__formatIRType___main(x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_17__formatIRType___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l___private_init_lean_compiler_ir_17__formatIRType(x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_typeHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_17__formatIRType___boxed), 1, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_compiler_ir_18__formatParam___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" : ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l___private_init_lean_compiler_ir_18__formatParam___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("@^ ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l___private_init_lean_compiler_ir_18__formatParam___main(obj* x_0) {
_start:
{
obj* x_1; uint8 x_3; uint8 x_4; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_4 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1 + 1);
lean::dec(x_0);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_8 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = 0;
x_10 = l_Lean_Format_paren___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = l___private_init_lean_compiler_ir_18__formatParam___main___closed__1;
x_14 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_9);
x_15 = x_14;
x_16 = l___private_init_lean_compiler_ir_17__formatIRType___main(x_4);
if (x_3 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_17 = l_Lean_Format_join___closed__1;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_15);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_9);
x_19 = x_18;
x_20 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set_scalar(x_20, sizeof(void*)*2, x_9);
x_21 = x_20;
x_22 = l_Lean_Format_paren___closed__2;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_9);
x_24 = x_23;
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = l___private_init_lean_compiler_ir_18__formatParam___main___closed__2;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_15);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_9);
x_27 = x_26;
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_16);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_9);
x_29 = x_28;
x_30 = l_Lean_Format_paren___closed__2;
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_9);
x_32 = x_31;
return x_32;
}
}
}
obj* l___private_init_lean_compiler_ir_18__formatParam(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_compiler_ir_18__formatParam___main(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_paramHasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_compiler_ir_18__formatParam), 1, 0);
return x_0;
}
}
obj* _init_l_Lean_IR_formatAlt___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" \xe2\x86\x92");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatAlt___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("default \xe2\x86\x92");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_formatAlt___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l___private_init_lean_compiler_ir_15__formatCtorInfo___main(x_3);
x_9 = 0;
x_10 = l_Lean_IR_formatAlt___main___closed__1;
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = lean::apply_1(x_0, x_5);
x_14 = lean::box(1);
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_9);
x_16 = x_15;
x_17 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_9);
x_19 = x_18;
return x_19;
}
else
{
obj* x_20; obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::apply_1(x_0, x_20);
x_24 = 0;
x_25 = lean::box(1);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_24);
x_27 = x_26;
x_28 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_Lean_IR_formatAlt___main___closed__2;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_24);
x_31 = x_30;
return x_31;
}
}
}
obj* l_Lean_IR_formatAlt(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_formatAlt___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; 
x_10 = lean::array_index(x_2, x_3);
x_11 = lean::mk_nat_obj(0ul);
x_12 = lean::nat_dec_lt(x_11, x_3);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
if (x_12 == 0)
{
obj* x_16; uint8 x_17; obj* x_18; obj* x_19; 
x_16 = l___private_init_lean_compiler_ir_18__formatParam___main(x_10);
x_17 = 0;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_17);
x_19 = x_18;
x_3 = x_14;
x_4 = x_19;
goto _start;
}
else
{
uint8 x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = 0;
lean::inc(x_1);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_21);
x_24 = x_23;
x_25 = l___private_init_lean_compiler_ir_18__formatParam___main(x_10);
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_21);
x_27 = x_26;
x_3 = x_14;
x_4 = x_27;
goto _start;
}
}
}
}
obj* l_Lean_Format_joinArraySep___at_Lean_IR_formatFnBody___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::box(0);
x_4 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_0, x_1, x_0, x_2, x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_10; obj* x_12; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::array_index(x_2, x_3);
lean::inc(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatFnBody___main), 2, 1);
lean::closure_set(x_12, 0, x_0);
lean::inc(x_0);
x_14 = l_Lean_IR_formatAlt___main(x_12, x_0, x_10);
x_15 = 0;
x_16 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_16, 0, x_4);
lean::cnstr_set(x_16, 1, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*2, x_15);
x_17 = x_16;
x_18 = lean::mk_nat_obj(1ul);
x_19 = lean::nat_add(x_3, x_18);
lean::dec(x_3);
x_3 = x_19;
x_4 = x_17;
goto _start;
}
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("let ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(";");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("jp ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" :=");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("set ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("] := ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__7() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("uset ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__8() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("sset ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__9() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("] : ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__10() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("release ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__11() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("];");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__12() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("inc ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__13() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("dec ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__14() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("mdata ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__15() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("case ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__16() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" of");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__17() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("ret ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__18() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("jmp ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatFnBody___main___closed__19() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("\xe2\x8a\xa5");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_formatFnBody___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; uint8 x_4; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_2);
x_12 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = 0;
x_14 = l_Lean_IR_formatFnBody___main___closed__1;
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_13);
x_16 = x_15;
x_17 = l___private_init_lean_compiler_ir_18__formatParam___main___closed__1;
x_18 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set_scalar(x_18, sizeof(void*)*2, x_13);
x_19 = x_18;
x_20 = l___private_init_lean_compiler_ir_17__formatIRType___main(x_4);
x_21 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set_scalar(x_21, sizeof(void*)*2, x_13);
x_22 = x_21;
x_23 = l_Lean_formatEntry___main___closed__1;
x_24 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
lean::cnstr_set_scalar(x_24, sizeof(void*)*2, x_13);
x_25 = x_24;
x_26 = l___private_init_lean_compiler_ir_16__formatExpr___main(x_5);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_13);
x_28 = x_27;
x_29 = l_Lean_IR_formatFnBody___main___closed__2;
x_30 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_29);
lean::cnstr_set_scalar(x_30, sizeof(void*)*2, x_13);
x_31 = x_30;
x_32 = lean::box(1);
x_33 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set(x_33, 1, x_32);
lean::cnstr_set_scalar(x_33, sizeof(void*)*2, x_13);
x_34 = x_33;
x_35 = l_Lean_IR_formatFnBody___main(x_0, x_7);
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_13);
x_37 = x_36;
return x_37;
}
case 1:
{
obj* x_38; obj* x_40; uint8 x_42; obj* x_43; obj* x_46; obj* x_47; obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_38 = lean::cnstr_get(x_1, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_1, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*4);
x_43 = lean::cnstr_get(x_1, 2);
lean::inc(x_43);
lean::dec(x_1);
x_46 = l_Lean_Name_toString___closed__1;
x_47 = l_Lean_Name_toStringWithSep___main(x_46, x_38);
x_48 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = 0;
x_50 = l_Lean_IR_formatFnBody___main___closed__3;
x_51 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_48);
lean::cnstr_set_scalar(x_51, sizeof(void*)*2, x_49);
x_52 = x_51;
x_53 = l_Lean_Format_flatten___main___closed__1;
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_53);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_49);
x_55 = x_54;
x_56 = lean::mk_nat_obj(0ul);
x_57 = lean::box(0);
x_58 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_40, x_53, x_40, x_56, x_57);
lean::dec(x_40);
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_55);
lean::cnstr_set(x_60, 1, x_58);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_49);
x_61 = x_60;
x_62 = l___private_init_lean_compiler_ir_18__formatParam___main___closed__1;
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_62);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_49);
x_64 = x_63;
x_65 = l___private_init_lean_compiler_ir_17__formatIRType___main(x_42);
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set(x_66, 1, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_49);
x_67 = x_66;
x_68 = l_Lean_IR_formatFnBody___main___closed__4;
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set(x_69, 1, x_68);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_49);
x_70 = x_69;
lean::inc(x_0);
x_72 = l_Lean_IR_formatFnBody___main(x_0, x_43);
x_73 = lean::box(1);
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_72);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_49);
x_75 = x_74;
x_76 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_76, 0, x_0);
lean::cnstr_set(x_76, 1, x_75);
x_77 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_77, 0, x_70);
lean::cnstr_set(x_77, 1, x_76);
lean::cnstr_set_scalar(x_77, sizeof(void*)*2, x_49);
x_78 = x_77;
x_79 = l_Lean_IR_formatFnBody___main___closed__2;
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_49);
x_81 = x_80;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_73);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_49);
x_83 = x_82;
return x_83;
}
case 2:
{
obj* x_84; obj* x_86; obj* x_88; obj* x_90; obj* x_93; obj* x_94; obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_84 = lean::cnstr_get(x_1, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_1, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_1, 2);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_1, 3);
lean::inc(x_90);
lean::dec(x_1);
x_93 = l_Lean_Name_toString___closed__1;
x_94 = l_Lean_Name_toStringWithSep___main(x_93, x_84);
x_95 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
x_96 = 0;
x_97 = l_Lean_IR_formatFnBody___main___closed__5;
x_98 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_95);
lean::cnstr_set_scalar(x_98, sizeof(void*)*2, x_96);
x_99 = x_98;
x_100 = l_Lean_Format_sbracket___closed__1;
x_101 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set(x_101, 1, x_100);
lean::cnstr_set_scalar(x_101, sizeof(void*)*2, x_96);
x_102 = x_101;
x_103 = l_Nat_repr(x_86);
x_104 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_104, 0, x_103);
x_105 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_105, 0, x_102);
lean::cnstr_set(x_105, 1, x_104);
lean::cnstr_set_scalar(x_105, sizeof(void*)*2, x_96);
x_106 = x_105;
x_107 = l_Lean_IR_formatFnBody___main___closed__6;
x_108 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_107);
lean::cnstr_set_scalar(x_108, sizeof(void*)*2, x_96);
x_109 = x_108;
x_110 = l_Lean_Name_toStringWithSep___main(x_93, x_88);
x_111 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_111, 0, x_110);
x_112 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set(x_112, 1, x_111);
lean::cnstr_set_scalar(x_112, sizeof(void*)*2, x_96);
x_113 = x_112;
x_114 = l_Lean_IR_formatFnBody___main___closed__2;
x_115 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_115, 0, x_113);
lean::cnstr_set(x_115, 1, x_114);
lean::cnstr_set_scalar(x_115, sizeof(void*)*2, x_96);
x_116 = x_115;
x_117 = lean::box(1);
x_118 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set(x_118, 1, x_117);
lean::cnstr_set_scalar(x_118, sizeof(void*)*2, x_96);
x_119 = x_118;
x_120 = l_Lean_IR_formatFnBody___main(x_0, x_90);
x_121 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set(x_121, 1, x_120);
lean::cnstr_set_scalar(x_121, sizeof(void*)*2, x_96);
x_122 = x_121;
return x_122;
}
case 3:
{
obj* x_123; obj* x_125; obj* x_127; obj* x_129; obj* x_132; obj* x_133; obj* x_134; uint8 x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_123 = lean::cnstr_get(x_1, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_1, 1);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_1, 2);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_1, 3);
lean::inc(x_129);
lean::dec(x_1);
x_132 = l_Lean_Name_toString___closed__1;
x_133 = l_Lean_Name_toStringWithSep___main(x_132, x_123);
x_134 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_134, 0, x_133);
x_135 = 0;
x_136 = l_Lean_IR_formatFnBody___main___closed__7;
x_137 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_134);
lean::cnstr_set_scalar(x_137, sizeof(void*)*2, x_135);
x_138 = x_137;
x_139 = l_Lean_Format_sbracket___closed__1;
x_140 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_140, 0, x_138);
lean::cnstr_set(x_140, 1, x_139);
lean::cnstr_set_scalar(x_140, sizeof(void*)*2, x_135);
x_141 = x_140;
x_142 = l_Nat_repr(x_125);
x_143 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_143, 0, x_142);
x_144 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_144, 0, x_141);
lean::cnstr_set(x_144, 1, x_143);
lean::cnstr_set_scalar(x_144, sizeof(void*)*2, x_135);
x_145 = x_144;
x_146 = l_Lean_IR_formatFnBody___main___closed__6;
x_147 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_147, 0, x_145);
lean::cnstr_set(x_147, 1, x_146);
lean::cnstr_set_scalar(x_147, sizeof(void*)*2, x_135);
x_148 = x_147;
x_149 = l_Lean_Name_toStringWithSep___main(x_132, x_127);
x_150 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_150, 0, x_149);
x_151 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_151, 0, x_148);
lean::cnstr_set(x_151, 1, x_150);
lean::cnstr_set_scalar(x_151, sizeof(void*)*2, x_135);
x_152 = x_151;
x_153 = l_Lean_IR_formatFnBody___main___closed__2;
x_154 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_154, 0, x_152);
lean::cnstr_set(x_154, 1, x_153);
lean::cnstr_set_scalar(x_154, sizeof(void*)*2, x_135);
x_155 = x_154;
x_156 = lean::box(1);
x_157 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_157, 0, x_155);
lean::cnstr_set(x_157, 1, x_156);
lean::cnstr_set_scalar(x_157, sizeof(void*)*2, x_135);
x_158 = x_157;
x_159 = l_Lean_IR_formatFnBody___main(x_0, x_129);
x_160 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_160, 0, x_158);
lean::cnstr_set(x_160, 1, x_159);
lean::cnstr_set_scalar(x_160, sizeof(void*)*2, x_135);
x_161 = x_160;
return x_161;
}
case 4:
{
obj* x_162; obj* x_164; obj* x_166; obj* x_168; uint8 x_170; obj* x_171; obj* x_174; obj* x_175; obj* x_176; uint8 x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; 
x_162 = lean::cnstr_get(x_1, 0);
lean::inc(x_162);
x_164 = lean::cnstr_get(x_1, 1);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_1, 2);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_1, 3);
lean::inc(x_168);
x_170 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
x_171 = lean::cnstr_get(x_1, 4);
lean::inc(x_171);
lean::dec(x_1);
x_174 = l_Lean_Name_toString___closed__1;
x_175 = l_Lean_Name_toStringWithSep___main(x_174, x_162);
x_176 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_176, 0, x_175);
x_177 = 0;
x_178 = l_Lean_IR_formatFnBody___main___closed__8;
x_179 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_179, 0, x_178);
lean::cnstr_set(x_179, 1, x_176);
lean::cnstr_set_scalar(x_179, sizeof(void*)*2, x_177);
x_180 = x_179;
x_181 = l_Lean_Format_sbracket___closed__1;
x_182 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_182, 0, x_180);
lean::cnstr_set(x_182, 1, x_181);
lean::cnstr_set_scalar(x_182, sizeof(void*)*2, x_177);
x_183 = x_182;
x_184 = l_Nat_repr(x_164);
x_185 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_185, 0, x_184);
x_186 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_186, 0, x_183);
lean::cnstr_set(x_186, 1, x_185);
lean::cnstr_set_scalar(x_186, sizeof(void*)*2, x_177);
x_187 = x_186;
x_188 = l_Lean_formatKVMap___closed__1;
x_189 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_189, 0, x_187);
lean::cnstr_set(x_189, 1, x_188);
lean::cnstr_set_scalar(x_189, sizeof(void*)*2, x_177);
x_190 = x_189;
x_191 = l_Nat_repr(x_166);
x_192 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_192, 0, x_191);
x_193 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_193, 0, x_190);
lean::cnstr_set(x_193, 1, x_192);
lean::cnstr_set_scalar(x_193, sizeof(void*)*2, x_177);
x_194 = x_193;
x_195 = l_Lean_IR_formatFnBody___main___closed__9;
x_196 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_196, 0, x_194);
lean::cnstr_set(x_196, 1, x_195);
lean::cnstr_set_scalar(x_196, sizeof(void*)*2, x_177);
x_197 = x_196;
x_198 = l___private_init_lean_compiler_ir_17__formatIRType___main(x_170);
x_199 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_199, 0, x_197);
lean::cnstr_set(x_199, 1, x_198);
lean::cnstr_set_scalar(x_199, sizeof(void*)*2, x_177);
x_200 = x_199;
x_201 = l_Lean_formatEntry___main___closed__1;
x_202 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_202, 0, x_200);
lean::cnstr_set(x_202, 1, x_201);
lean::cnstr_set_scalar(x_202, sizeof(void*)*2, x_177);
x_203 = x_202;
x_204 = l_Lean_Name_toStringWithSep___main(x_174, x_168);
x_205 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_205, 0, x_204);
x_206 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_206, 0, x_203);
lean::cnstr_set(x_206, 1, x_205);
lean::cnstr_set_scalar(x_206, sizeof(void*)*2, x_177);
x_207 = x_206;
x_208 = l_Lean_IR_formatFnBody___main___closed__2;
x_209 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_209, 0, x_207);
lean::cnstr_set(x_209, 1, x_208);
lean::cnstr_set_scalar(x_209, sizeof(void*)*2, x_177);
x_210 = x_209;
x_211 = lean::box(1);
x_212 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_212, 0, x_210);
lean::cnstr_set(x_212, 1, x_211);
lean::cnstr_set_scalar(x_212, sizeof(void*)*2, x_177);
x_213 = x_212;
x_214 = l_Lean_IR_formatFnBody___main(x_0, x_171);
x_215 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_215, 0, x_213);
lean::cnstr_set(x_215, 1, x_214);
lean::cnstr_set_scalar(x_215, sizeof(void*)*2, x_177);
x_216 = x_215;
return x_216;
}
case 5:
{
obj* x_217; obj* x_219; obj* x_221; obj* x_224; obj* x_225; obj* x_226; uint8 x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
x_217 = lean::cnstr_get(x_1, 0);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_1, 1);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_1, 2);
lean::inc(x_221);
lean::dec(x_1);
x_224 = l_Lean_Name_toString___closed__1;
x_225 = l_Lean_Name_toStringWithSep___main(x_224, x_217);
x_226 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_226, 0, x_225);
x_227 = 0;
x_228 = l_Lean_IR_formatFnBody___main___closed__10;
x_229 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_226);
lean::cnstr_set_scalar(x_229, sizeof(void*)*2, x_227);
x_230 = x_229;
x_231 = l_Lean_Format_sbracket___closed__1;
x_232 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_232, 0, x_230);
lean::cnstr_set(x_232, 1, x_231);
lean::cnstr_set_scalar(x_232, sizeof(void*)*2, x_227);
x_233 = x_232;
x_234 = l_Nat_repr(x_219);
x_235 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_235, 0, x_234);
x_236 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_236, 0, x_233);
lean::cnstr_set(x_236, 1, x_235);
lean::cnstr_set_scalar(x_236, sizeof(void*)*2, x_227);
x_237 = x_236;
x_238 = l_Lean_IR_formatFnBody___main___closed__11;
x_239 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_239, 0, x_237);
lean::cnstr_set(x_239, 1, x_238);
lean::cnstr_set_scalar(x_239, sizeof(void*)*2, x_227);
x_240 = x_239;
x_241 = lean::box(1);
x_242 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_242, 0, x_240);
lean::cnstr_set(x_242, 1, x_241);
lean::cnstr_set_scalar(x_242, sizeof(void*)*2, x_227);
x_243 = x_242;
x_244 = l_Lean_IR_formatFnBody___main(x_0, x_221);
x_245 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_245, 0, x_243);
lean::cnstr_set(x_245, 1, x_244);
lean::cnstr_set_scalar(x_245, sizeof(void*)*2, x_227);
x_246 = x_245;
return x_246;
}
case 6:
{
obj* x_247; obj* x_249; obj* x_251; obj* x_254; obj* x_255; obj* x_256; uint8 x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; uint8 x_262; obj* x_263; 
x_247 = lean::cnstr_get(x_1, 0);
lean::inc(x_247);
x_249 = lean::cnstr_get(x_1, 1);
lean::inc(x_249);
x_251 = lean::cnstr_get(x_1, 2);
lean::inc(x_251);
lean::dec(x_1);
x_254 = l_Lean_Name_toString___closed__1;
x_255 = l_Lean_Name_toStringWithSep___main(x_254, x_247);
x_256 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_256, 0, x_255);
x_257 = 0;
x_258 = l_Lean_IR_formatFnBody___main___closed__12;
x_259 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_259, 0, x_258);
lean::cnstr_set(x_259, 1, x_256);
lean::cnstr_set_scalar(x_259, sizeof(void*)*2, x_257);
x_260 = x_259;
x_261 = lean::mk_nat_obj(1ul);
x_262 = lean::nat_dec_eq(x_249, x_261);
x_263 = l_Lean_IR_formatFnBody___main(x_0, x_251);
if (x_262 == 0)
{
obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
x_264 = l_Nat_repr(x_249);
x_265 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_265, 0, x_264);
x_266 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_266, 0, x_260);
lean::cnstr_set(x_266, 1, x_265);
lean::cnstr_set_scalar(x_266, sizeof(void*)*2, x_257);
x_267 = x_266;
x_268 = l_Lean_IR_formatFnBody___main___closed__2;
x_269 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_269, 0, x_267);
lean::cnstr_set(x_269, 1, x_268);
lean::cnstr_set_scalar(x_269, sizeof(void*)*2, x_257);
x_270 = x_269;
x_271 = lean::box(1);
x_272 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_272, 0, x_270);
lean::cnstr_set(x_272, 1, x_271);
lean::cnstr_set_scalar(x_272, sizeof(void*)*2, x_257);
x_273 = x_272;
x_274 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_274, 0, x_273);
lean::cnstr_set(x_274, 1, x_263);
lean::cnstr_set_scalar(x_274, sizeof(void*)*2, x_257);
x_275 = x_274;
return x_275;
}
else
{
obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; 
lean::dec(x_249);
x_277 = l_Lean_Format_join___closed__1;
x_278 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_278, 0, x_260);
lean::cnstr_set(x_278, 1, x_277);
lean::cnstr_set_scalar(x_278, sizeof(void*)*2, x_257);
x_279 = x_278;
x_280 = l_Lean_IR_formatFnBody___main___closed__2;
x_281 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_281, 0, x_279);
lean::cnstr_set(x_281, 1, x_280);
lean::cnstr_set_scalar(x_281, sizeof(void*)*2, x_257);
x_282 = x_281;
x_283 = lean::box(1);
x_284 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_284, 0, x_282);
lean::cnstr_set(x_284, 1, x_283);
lean::cnstr_set_scalar(x_284, sizeof(void*)*2, x_257);
x_285 = x_284;
x_286 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_263);
lean::cnstr_set_scalar(x_286, sizeof(void*)*2, x_257);
x_287 = x_286;
return x_287;
}
}
case 7:
{
obj* x_288; obj* x_290; obj* x_292; obj* x_295; obj* x_296; obj* x_297; uint8 x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; uint8 x_303; obj* x_304; 
x_288 = lean::cnstr_get(x_1, 0);
lean::inc(x_288);
x_290 = lean::cnstr_get(x_1, 1);
lean::inc(x_290);
x_292 = lean::cnstr_get(x_1, 2);
lean::inc(x_292);
lean::dec(x_1);
x_295 = l_Lean_Name_toString___closed__1;
x_296 = l_Lean_Name_toStringWithSep___main(x_295, x_288);
x_297 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_297, 0, x_296);
x_298 = 0;
x_299 = l_Lean_IR_formatFnBody___main___closed__13;
x_300 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_300, 0, x_299);
lean::cnstr_set(x_300, 1, x_297);
lean::cnstr_set_scalar(x_300, sizeof(void*)*2, x_298);
x_301 = x_300;
x_302 = lean::mk_nat_obj(1ul);
x_303 = lean::nat_dec_eq(x_290, x_302);
x_304 = l_Lean_IR_formatFnBody___main(x_0, x_292);
if (x_303 == 0)
{
obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; 
x_305 = l_Nat_repr(x_290);
x_306 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_306, 0, x_305);
x_307 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_307, 0, x_301);
lean::cnstr_set(x_307, 1, x_306);
lean::cnstr_set_scalar(x_307, sizeof(void*)*2, x_298);
x_308 = x_307;
x_309 = l_Lean_IR_formatFnBody___main___closed__2;
x_310 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_310, 0, x_308);
lean::cnstr_set(x_310, 1, x_309);
lean::cnstr_set_scalar(x_310, sizeof(void*)*2, x_298);
x_311 = x_310;
x_312 = lean::box(1);
x_313 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_313, 0, x_311);
lean::cnstr_set(x_313, 1, x_312);
lean::cnstr_set_scalar(x_313, sizeof(void*)*2, x_298);
x_314 = x_313;
x_315 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_304);
lean::cnstr_set_scalar(x_315, sizeof(void*)*2, x_298);
x_316 = x_315;
return x_316;
}
else
{
obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; 
lean::dec(x_290);
x_318 = l_Lean_Format_join___closed__1;
x_319 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_319, 0, x_301);
lean::cnstr_set(x_319, 1, x_318);
lean::cnstr_set_scalar(x_319, sizeof(void*)*2, x_298);
x_320 = x_319;
x_321 = l_Lean_IR_formatFnBody___main___closed__2;
x_322 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_322, 0, x_320);
lean::cnstr_set(x_322, 1, x_321);
lean::cnstr_set_scalar(x_322, sizeof(void*)*2, x_298);
x_323 = x_322;
x_324 = lean::box(1);
x_325 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_325, 0, x_323);
lean::cnstr_set(x_325, 1, x_324);
lean::cnstr_set_scalar(x_325, sizeof(void*)*2, x_298);
x_326 = x_325;
x_327 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_304);
lean::cnstr_set_scalar(x_327, sizeof(void*)*2, x_298);
x_328 = x_327;
return x_328;
}
}
case 8:
{
obj* x_329; obj* x_331; obj* x_334; uint8 x_335; obj* x_336; obj* x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; obj* x_345; obj* x_346; obj* x_347; 
x_329 = lean::cnstr_get(x_1, 0);
lean::inc(x_329);
x_331 = lean::cnstr_get(x_1, 1);
lean::inc(x_331);
lean::dec(x_1);
x_334 = l_Lean_formatKVMap(x_329);
x_335 = 0;
x_336 = l_Lean_IR_formatFnBody___main___closed__14;
x_337 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_337, 0, x_336);
lean::cnstr_set(x_337, 1, x_334);
lean::cnstr_set_scalar(x_337, sizeof(void*)*2, x_335);
x_338 = x_337;
x_339 = l_Lean_IR_formatFnBody___main___closed__2;
x_340 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_340, 0, x_338);
lean::cnstr_set(x_340, 1, x_339);
lean::cnstr_set_scalar(x_340, sizeof(void*)*2, x_335);
x_341 = x_340;
x_342 = lean::box(1);
x_343 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_343, 0, x_341);
lean::cnstr_set(x_343, 1, x_342);
lean::cnstr_set_scalar(x_343, sizeof(void*)*2, x_335);
x_344 = x_343;
x_345 = l_Lean_IR_formatFnBody___main(x_0, x_331);
x_346 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_346, 0, x_344);
lean::cnstr_set(x_346, 1, x_345);
lean::cnstr_set_scalar(x_346, sizeof(void*)*2, x_335);
x_347 = x_346;
return x_347;
}
case 9:
{
obj* x_348; obj* x_350; obj* x_353; obj* x_354; obj* x_355; uint8 x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_367; obj* x_368; 
x_348 = lean::cnstr_get(x_1, 1);
lean::inc(x_348);
x_350 = lean::cnstr_get(x_1, 2);
lean::inc(x_350);
lean::dec(x_1);
x_353 = l_Lean_Name_toString___closed__1;
x_354 = l_Lean_Name_toStringWithSep___main(x_353, x_348);
x_355 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_355, 0, x_354);
x_356 = 0;
x_357 = l_Lean_IR_formatFnBody___main___closed__15;
x_358 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_358, 0, x_357);
lean::cnstr_set(x_358, 1, x_355);
lean::cnstr_set_scalar(x_358, sizeof(void*)*2, x_356);
x_359 = x_358;
x_360 = l_Lean_IR_formatFnBody___main___closed__16;
x_361 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_361, 0, x_359);
lean::cnstr_set(x_361, 1, x_360);
lean::cnstr_set_scalar(x_361, sizeof(void*)*2, x_356);
x_362 = x_361;
x_363 = lean::mk_nat_obj(0ul);
x_364 = lean::box(1);
x_365 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3(x_0, x_350, x_350, x_363, x_364);
lean::dec(x_350);
x_367 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_367, 0, x_362);
lean::cnstr_set(x_367, 1, x_365);
lean::cnstr_set_scalar(x_367, sizeof(void*)*2, x_356);
x_368 = x_367;
return x_368;
}
case 10:
{
obj* x_370; obj* x_373; obj* x_374; obj* x_375; uint8 x_376; obj* x_377; obj* x_378; obj* x_379; 
lean::dec(x_0);
x_370 = lean::cnstr_get(x_1, 0);
lean::inc(x_370);
lean::dec(x_1);
x_373 = l_Lean_Name_toString___closed__1;
x_374 = l_Lean_Name_toStringWithSep___main(x_373, x_370);
x_375 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_375, 0, x_374);
x_376 = 0;
x_377 = l_Lean_IR_formatFnBody___main___closed__17;
x_378 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_378, 0, x_377);
lean::cnstr_set(x_378, 1, x_375);
lean::cnstr_set_scalar(x_378, sizeof(void*)*2, x_376);
x_379 = x_378;
return x_379;
}
case 11:
{
obj* x_381; obj* x_383; obj* x_386; obj* x_387; obj* x_388; uint8 x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_395; obj* x_396; obj* x_398; obj* x_399; 
lean::dec(x_0);
x_381 = lean::cnstr_get(x_1, 0);
lean::inc(x_381);
x_383 = lean::cnstr_get(x_1, 1);
lean::inc(x_383);
lean::dec(x_1);
x_386 = l_Lean_Name_toString___closed__1;
x_387 = l_Lean_Name_toStringWithSep___main(x_386, x_381);
x_388 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_388, 0, x_387);
x_389 = 0;
x_390 = l_Lean_IR_formatFnBody___main___closed__18;
x_391 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_391, 0, x_390);
lean::cnstr_set(x_391, 1, x_388);
lean::cnstr_set_scalar(x_391, sizeof(void*)*2, x_389);
x_392 = x_391;
x_393 = l_Lean_Format_flatten___main___closed__1;
x_394 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_394, 0, x_392);
lean::cnstr_set(x_394, 1, x_393);
lean::cnstr_set_scalar(x_394, sizeof(void*)*2, x_389);
x_395 = x_394;
x_396 = l___private_init_lean_compiler_ir_13__formatArgs(x_383);
lean::dec(x_383);
x_398 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_398, 0, x_395);
lean::cnstr_set(x_398, 1, x_396);
lean::cnstr_set_scalar(x_398, sizeof(void*)*2, x_389);
x_399 = x_398;
return x_399;
}
default:
{
obj* x_401; 
lean::dec(x_0);
x_401 = l_Lean_IR_formatFnBody___main___closed__19;
return x_401;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Format_joinArraySep___at_Lean_IR_formatFnBody___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Format_joinArraySep___at_Lean_IR_formatFnBody___main___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_IR_formatFnBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_formatFnBody___main(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_fnBodyHasFormat() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(2ul);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatFnBody), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatDecl___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("def ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_formatDecl___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("extern ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_formatDecl___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; uint8 x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_2);
x_12 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_13 = 0;
x_14 = l_Lean_IR_formatDecl___main___closed__1;
x_15 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set_scalar(x_15, sizeof(void*)*2, x_13);
x_16 = x_15;
x_17 = l_Lean_Format_flatten___main___closed__1;
x_18 = lean::mk_nat_obj(0ul);
x_19 = lean::box(0);
x_20 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_4, x_17, x_4, x_18, x_19);
lean::dec(x_4);
x_22 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_22, 0, x_16);
lean::cnstr_set(x_22, 1, x_20);
lean::cnstr_set_scalar(x_22, sizeof(void*)*2, x_13);
x_23 = x_22;
x_24 = l___private_init_lean_compiler_ir_18__formatParam___main___closed__1;
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_13);
x_26 = x_25;
x_27 = l___private_init_lean_compiler_ir_17__formatIRType___main(x_6);
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_13);
x_29 = x_28;
x_30 = l_Lean_IR_formatFnBody___main___closed__4;
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_13);
x_32 = x_31;
lean::inc(x_0);
x_34 = l_Lean_IR_formatFnBody___main(x_0, x_7);
x_35 = lean::box(1);
x_36 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*2, x_13);
x_37 = x_36;
x_38 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_38, 0, x_0);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_39, 0, x_32);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set_scalar(x_39, sizeof(void*)*2, x_13);
x_40 = x_39;
return x_40;
}
else
{
obj* x_42; obj* x_44; uint8 x_46; obj* x_48; obj* x_49; obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_0);
x_42 = lean::cnstr_get(x_1, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_1, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*2);
lean::dec(x_1);
x_48 = l_Lean_Name_toString___closed__1;
x_49 = l_Lean_Name_toStringWithSep___main(x_48, x_42);
x_50 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
x_51 = 0;
x_52 = l_Lean_IR_formatDecl___main___closed__2;
x_53 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_50);
lean::cnstr_set_scalar(x_53, sizeof(void*)*2, x_51);
x_54 = x_53;
x_55 = l_Lean_Format_flatten___main___closed__1;
x_56 = lean::mk_nat_obj(0ul);
x_57 = lean::box(0);
x_58 = l_Array_miterateAux___main___at_Lean_IR_formatFnBody___main___spec__2(x_44, x_55, x_44, x_56, x_57);
lean::dec(x_44);
x_60 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_60, 0, x_54);
lean::cnstr_set(x_60, 1, x_58);
lean::cnstr_set_scalar(x_60, sizeof(void*)*2, x_51);
x_61 = x_60;
x_62 = l___private_init_lean_compiler_ir_18__formatParam___main___closed__1;
x_63 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_62);
lean::cnstr_set_scalar(x_63, sizeof(void*)*2, x_51);
x_64 = x_63;
x_65 = l___private_init_lean_compiler_ir_17__formatIRType___main(x_46);
x_66 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set(x_66, 1, x_65);
lean::cnstr_set_scalar(x_66, sizeof(void*)*2, x_51);
x_67 = x_66;
return x_67;
}
}
}
obj* l_Lean_IR_formatDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_formatDecl___main(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_IR_declHasFormat() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(2ul);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_formatDecl), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_kvmap(obj*);
obj* initialize_init_lean_format(obj*);
obj* initialize_init_data_array_default(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_kvmap(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_MData_empty = _init_l_Lean_IR_MData_empty();
lean::mark_persistent(l_Lean_IR_MData_empty);
 l_Lean_IR_MData_HasEmptyc = _init_l_Lean_IR_MData_HasEmptyc();
lean::mark_persistent(l_Lean_IR_MData_HasEmptyc);
 l_Lean_IR_IRType_HasBeq = _init_l_Lean_IR_IRType_HasBeq();
lean::mark_persistent(l_Lean_IR_IRType_HasBeq);
 lean::ir::mk_irrelevant_arg_core = lean::ir::_init_mk_irrelevant_arg_core();
lean::mark_persistent(lean::ir::mk_irrelevant_arg_core);
 l_Lean_IR_LitVal_HasBeq = _init_l_Lean_IR_LitVal_HasBeq();
lean::mark_persistent(l_Lean_IR_LitVal_HasBeq);
 l_Lean_IR_CtorInfo_HasBeq = _init_l_Lean_IR_CtorInfo_HasBeq();
lean::mark_persistent(l_Lean_IR_CtorInfo_HasBeq);
 lean::ir::mk_unreachable_core = lean::ir::_init_mk_unreachable_core();
lean::mark_persistent(lean::ir::mk_unreachable_core);
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
 l_Lean_IR_HasAndthen = _init_l_Lean_IR_HasAndthen();
lean::mark_persistent(l_Lean_IR_HasAndthen);
 l___private_init_lean_compiler_ir_11__collectFnBody___main___closed__1 = _init_l___private_init_lean_compiler_ir_11__collectFnBody___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_11__collectFnBody___main___closed__1);
 l___private_init_lean_compiler_ir_12__formatArg___main___closed__1 = _init_l___private_init_lean_compiler_ir_12__formatArg___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_12__formatArg___main___closed__1);
 l_Lean_IR_argHasFormat = _init_l_Lean_IR_argHasFormat();
lean::mark_persistent(l_Lean_IR_argHasFormat);
 l_Lean_IR_argsHasFormat = _init_l_Lean_IR_argsHasFormat();
lean::mark_persistent(l_Lean_IR_argsHasFormat);
 l_Lean_IR_litValHasFormat = _init_l_Lean_IR_litValHasFormat();
lean::mark_persistent(l_Lean_IR_litValHasFormat);
 l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__1 = _init_l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__1);
 l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__2 = _init_l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_15__formatCtorInfo___main___closed__2);
 l_Lean_IR_ctorInfoHasFormat = _init_l_Lean_IR_ctorInfoHasFormat();
lean::mark_persistent(l_Lean_IR_ctorInfoHasFormat);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__1 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__1);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__2 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__2);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__3 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__3);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__4 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__4();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__4);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__5 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__5();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__5);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__6 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__6();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__6);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__7 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__7();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__7);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__8 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__8();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__8);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__9 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__9();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__9);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__10 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__10();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__10);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__11 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__11();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__11);
 l___private_init_lean_compiler_ir_16__formatExpr___main___closed__12 = _init_l___private_init_lean_compiler_ir_16__formatExpr___main___closed__12();
lean::mark_persistent(l___private_init_lean_compiler_ir_16__formatExpr___main___closed__12);
 l_Lean_IR_exprHasFormat = _init_l_Lean_IR_exprHasFormat();
lean::mark_persistent(l_Lean_IR_exprHasFormat);
 l___private_init_lean_compiler_ir_17__formatIRType___main___closed__1 = _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_17__formatIRType___main___closed__1);
 l___private_init_lean_compiler_ir_17__formatIRType___main___closed__2 = _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_17__formatIRType___main___closed__2);
 l___private_init_lean_compiler_ir_17__formatIRType___main___closed__3 = _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__3();
lean::mark_persistent(l___private_init_lean_compiler_ir_17__formatIRType___main___closed__3);
 l___private_init_lean_compiler_ir_17__formatIRType___main___closed__4 = _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__4();
lean::mark_persistent(l___private_init_lean_compiler_ir_17__formatIRType___main___closed__4);
 l___private_init_lean_compiler_ir_17__formatIRType___main___closed__5 = _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__5();
lean::mark_persistent(l___private_init_lean_compiler_ir_17__formatIRType___main___closed__5);
 l___private_init_lean_compiler_ir_17__formatIRType___main___closed__6 = _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__6();
lean::mark_persistent(l___private_init_lean_compiler_ir_17__formatIRType___main___closed__6);
 l___private_init_lean_compiler_ir_17__formatIRType___main___closed__7 = _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__7();
lean::mark_persistent(l___private_init_lean_compiler_ir_17__formatIRType___main___closed__7);
 l___private_init_lean_compiler_ir_17__formatIRType___main___closed__8 = _init_l___private_init_lean_compiler_ir_17__formatIRType___main___closed__8();
lean::mark_persistent(l___private_init_lean_compiler_ir_17__formatIRType___main___closed__8);
 l_Lean_IR_typeHasFormat = _init_l_Lean_IR_typeHasFormat();
lean::mark_persistent(l_Lean_IR_typeHasFormat);
 l___private_init_lean_compiler_ir_18__formatParam___main___closed__1 = _init_l___private_init_lean_compiler_ir_18__formatParam___main___closed__1();
lean::mark_persistent(l___private_init_lean_compiler_ir_18__formatParam___main___closed__1);
 l___private_init_lean_compiler_ir_18__formatParam___main___closed__2 = _init_l___private_init_lean_compiler_ir_18__formatParam___main___closed__2();
lean::mark_persistent(l___private_init_lean_compiler_ir_18__formatParam___main___closed__2);
 l_Lean_IR_paramHasFormat = _init_l_Lean_IR_paramHasFormat();
lean::mark_persistent(l_Lean_IR_paramHasFormat);
 l_Lean_IR_formatAlt___main___closed__1 = _init_l_Lean_IR_formatAlt___main___closed__1();
lean::mark_persistent(l_Lean_IR_formatAlt___main___closed__1);
 l_Lean_IR_formatAlt___main___closed__2 = _init_l_Lean_IR_formatAlt___main___closed__2();
lean::mark_persistent(l_Lean_IR_formatAlt___main___closed__2);
 l_Lean_IR_formatFnBody___main___closed__1 = _init_l_Lean_IR_formatFnBody___main___closed__1();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__1);
 l_Lean_IR_formatFnBody___main___closed__2 = _init_l_Lean_IR_formatFnBody___main___closed__2();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__2);
 l_Lean_IR_formatFnBody___main___closed__3 = _init_l_Lean_IR_formatFnBody___main___closed__3();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__3);
 l_Lean_IR_formatFnBody___main___closed__4 = _init_l_Lean_IR_formatFnBody___main___closed__4();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__4);
 l_Lean_IR_formatFnBody___main___closed__5 = _init_l_Lean_IR_formatFnBody___main___closed__5();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__5);
 l_Lean_IR_formatFnBody___main___closed__6 = _init_l_Lean_IR_formatFnBody___main___closed__6();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__6);
 l_Lean_IR_formatFnBody___main___closed__7 = _init_l_Lean_IR_formatFnBody___main___closed__7();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__7);
 l_Lean_IR_formatFnBody___main___closed__8 = _init_l_Lean_IR_formatFnBody___main___closed__8();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__8);
 l_Lean_IR_formatFnBody___main___closed__9 = _init_l_Lean_IR_formatFnBody___main___closed__9();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__9);
 l_Lean_IR_formatFnBody___main___closed__10 = _init_l_Lean_IR_formatFnBody___main___closed__10();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__10);
 l_Lean_IR_formatFnBody___main___closed__11 = _init_l_Lean_IR_formatFnBody___main___closed__11();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__11);
 l_Lean_IR_formatFnBody___main___closed__12 = _init_l_Lean_IR_formatFnBody___main___closed__12();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__12);
 l_Lean_IR_formatFnBody___main___closed__13 = _init_l_Lean_IR_formatFnBody___main___closed__13();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__13);
 l_Lean_IR_formatFnBody___main___closed__14 = _init_l_Lean_IR_formatFnBody___main___closed__14();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__14);
 l_Lean_IR_formatFnBody___main___closed__15 = _init_l_Lean_IR_formatFnBody___main___closed__15();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__15);
 l_Lean_IR_formatFnBody___main___closed__16 = _init_l_Lean_IR_formatFnBody___main___closed__16();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__16);
 l_Lean_IR_formatFnBody___main___closed__17 = _init_l_Lean_IR_formatFnBody___main___closed__17();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__17);
 l_Lean_IR_formatFnBody___main___closed__18 = _init_l_Lean_IR_formatFnBody___main___closed__18();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__18);
 l_Lean_IR_formatFnBody___main___closed__19 = _init_l_Lean_IR_formatFnBody___main___closed__19();
lean::mark_persistent(l_Lean_IR_formatFnBody___main___closed__19);
 l_Lean_IR_fnBodyHasFormat = _init_l_Lean_IR_fnBodyHasFormat();
lean::mark_persistent(l_Lean_IR_fnBodyHasFormat);
 l_Lean_IR_formatDecl___main___closed__1 = _init_l_Lean_IR_formatDecl___main___closed__1();
lean::mark_persistent(l_Lean_IR_formatDecl___main___closed__1);
 l_Lean_IR_formatDecl___main___closed__2 = _init_l_Lean_IR_formatDecl___main___closed__2();
lean::mark_persistent(l_Lean_IR_formatDecl___main___closed__2);
 l_Lean_IR_declHasFormat = _init_l_Lean_IR_declHasFormat();
lean::mark_persistent(l_Lean_IR_declHasFormat);
return w;
}
