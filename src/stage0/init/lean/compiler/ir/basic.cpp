// Lean compiler output
// Module: init.lean.compiler.ir.basic
// Imports: init.data.array.default init.lean.name init.lean.extern init.lean.kvmap init.lean.format
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
obj* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(obj*, obj*);
obj* l_RBNode_setBlack___main___rarg(obj*);
obj* l_Lean_IR_FnBody_beq___boxed(obj*, obj*);
obj* l_Lean_IR_LocalContext_addParams___boxed(obj*, obj*);
obj* l_Lean_IR_LocalContext_isJP___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_setBody(obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___boxed(obj*);
namespace lean {
namespace ir {
obj* mk_sset_core(obj*, obj*, obj*, obj*, uint8, obj*);
}}
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_IR_VarIdSet_Inhabited;
obj* l_Lean_IR_mkVDecl___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_setBody(obj*, obj*);
obj* l_Lean_IR_IRType_isScalar___main___boxed(obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_Lean_IR_vsetInh;
obj* l_Lean_IR_VarId_Lean_HasFormat(obj*);
obj* l_Lean_IR_Alt_isDefault___boxed(obj*);
uint8 l_Lean_IR_IRType_beq(uint8, uint8);
uint8 l_Lean_IR_Arg_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___main___rarg___closed__1;
obj* l_Lean_IR_AltCore_mmodifyBody___main(obj*);
obj* l_Lean_IR_CtorInfo_isRef___boxed(obj*);
namespace lean {
namespace ir {
obj* mk_jdecl_core(obj*, obj*, obj*, obj*);
}}
namespace lean {
namespace ir {
obj* mk_var_arg_core(obj*);
}}
obj* l_Lean_IR_JoinPointId_HasToString___closed__1;
obj* l_Lean_IR_mmodifyJPs(obj*);
obj* l_RBNode_balRight___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_isTerminal___boxed(obj*);
uint8 l_Lean_IR_IRType_beq___main(uint8, uint8);
obj* l_Lean_IR_AltCore_mmodifyBody(obj*);
obj* l_Lean_IR_LocalContext_getJPBody(obj*, obj*);
obj* l_Lean_IR_LocalContext_isLocalVar___boxed(obj*, obj*);
obj* l_Lean_IR_addParamsRename___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_addLocal(obj*, obj*, uint8, obj*);
namespace lean {
namespace ir {
obj* mk_fapp_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_AltCore_modifyBody___main(obj*, obj*);
uint8 l_Lean_IR_LocalContext_isParam(obj*, obj*);
uint8 l_Lean_IR_LocalContext_contains(obj*, obj*);
obj* l_Lean_IR_addParamRename(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_alt_core(obj*, obj*, obj*, obj*, obj*, obj*);
}}
obj* l_Lean_IR_modifyJPs(obj*, obj*);
uint8 l_Lean_IR_LitVal_beq___main(obj*, obj*);
obj* l_Lean_IR_AltCore_body___main___boxed(obj*);
obj* l_Lean_IR_mmodifyJPs___boxed(obj*);
obj* l_Lean_IR_mkParam___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_HasBeq;
uint8 l_Lean_IR_Decl_resultType___main(obj*);
uint8 l_Lean_IR_VarId_HasBeq(obj*, obj*);
obj* l_Lean_IR_FnBody_body(obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_alphaEqv___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_VarId_alphaEqv(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_jmp_core(obj*, obj*);
}}
obj* l_Lean_IR_AltCore_modifyBody(obj*, obj*);
obj* l_Lean_IR_LocalContext_addLocal___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_JoinPointId_HasBeq___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_nil;
uint8 l_Lean_IR_FnBody_alphaEqv(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_str_expr_core(obj*);
}}
obj* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1___boxed(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_proj_expr_core(obj*, obj*);
}}
usize l_Lean_IR_JoinPointId_Hashable(obj*);
uint8 l_Lean_IR_CtorInfo_beq(obj*, obj*);
obj* l_Lean_IR_IRType_isObj___boxed(obj*);
uint8 l_Lean_IR_IRType_isObj___main(uint8);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Decl_resultType___boxed(obj*);
obj* l_Lean_IR_Decl_resultType___main___boxed(obj*);
obj* l_Lean_IR_Alt_default(obj*);
uint8 l_Lean_IR_Decl_resultType(obj*);
namespace lean {
namespace ir {
obj* mk_num_expr_core(obj*);
}}
uint8 l_Lean_IR_FnBody_isPure(obj*);
obj* l_Lean_IR_VarId_hasAeqv;
namespace lean {
namespace ir {
obj* mk_sproj_expr_core(obj*, obj*, obj*);
}}
obj* l_Lean_IR_CtorInfo_isScalar___boxed(obj*);
uint8 l_Lean_IR_LitVal_beq(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_mkSSet___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_Expr_isPure___main(obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_FnBody_alphaEqv___main___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_isScalar___boxed(obj*);
obj* l_Lean_IR_Arg_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_addJP(obj*, obj*, obj*, obj*);
obj* l_Array_miterate_u_2082Aux___main___at_Lean_IR_addParamsRename___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___main___boxed(obj*);
obj* l_Lean_IR_AltCore_body(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___rarg(obj*, obj*, obj*);
uint8 l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_flattenAux___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2___boxed(obj*, obj*);
obj* l_Lean_IR_reshape(obj*, obj*);
obj* l_Lean_IR_JoinPointId_Lean_HasFormat(obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
uint8 l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_mkExternDecl___boxed(obj*, obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_case_core(obj*, obj*, obj*);
}}
obj* l_Array_anyMAux___main___at_Lean_IR_FnBody_isPure___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_JoinPointId_Hashable___boxed(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_RBNode_balLeft___main___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_addParamsRename(obj*, obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Decl_Inhabited;
obj* l_Lean_IR_Decl_params___boxed(obj*);
obj* l_Lean_IR_LocalContext_getJPParams___boxed(obj*, obj*);
obj* l_Lean_IR_args_hasAeqv;
uint8 l_Lean_IR_Arg_beq(obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_args_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_HasBeq;
uint8 l_Lean_IR_Expr_alphaEqv(obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Lean_IR_LocalContext_eraseJoinPointDecl(obj*, obj*);
obj* l_Lean_IR_Decl_name___boxed(obj*);
obj* l_Lean_IR_LitVal_beq___boxed(obj*, obj*);
obj* l_Lean_IR_Decl_name___main(obj*);
obj* l_RBNode_appendTrees___main___rarg(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_ret_core(obj*);
}}
obj* l_Lean_IR_FnBody_flatten(obj*);
obj* l_Lean_IR_LocalContext_addParam(obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_CtorInfo_isScalar(obj*);
namespace lean {
namespace ir {
obj* mk_extern_decl_core(obj*, obj*, uint8, obj*);
}}
obj* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
namespace lean {
namespace ir {
obj* mk_param_core(obj*, uint8, uint8);
}}
obj* l_Lean_IR_AltCore_body___boxed(obj*);
obj* l_Lean_IR_paramInh;
uint8 l_RBNode_isRed___main___rarg(obj*);
uint8 l_Lean_IR_CtorInfo_isRef(obj*);
uint8 l_Lean_KVMap_eqv(obj*, obj*);
obj* l_Lean_IR_Expr_hasAeqv;
obj* l_Lean_IR_LocalContext_addParams(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_uset_core(obj*, obj*, obj*, obj*);
}}
obj* l_Lean_IR_LocalContext_getType(obj*, obj*);
obj* l_Lean_IR_FnBody_body___boxed(obj*);
obj* l_Lean_IR_VarId_Hashable___boxed(obj*);
obj* l_Lean_IR_IRType_HasBeq;
obj* l_Lean_IR_altInh;
obj* l_Lean_IR_FnBody_body___main___boxed(obj*);
obj* l_Lean_IR_FnBody_isTerminal___main___boxed(obj*);
uint8 l_Lean_IR_Alt_isDefault___main(obj*);
obj* l_Lean_IR_VarId_HasBeq___boxed(obj*, obj*);
obj* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(obj*, obj*);
obj* l_Lean_IR_LocalContext_getJPBody___boxed(obj*, obj*);
obj* l_Lean_IR_Expr_isPure___boxed(obj*);
obj* l_Lean_IR_FnBody_split(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_Lean_IR_LocalContext_getJPParams(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___boxed(obj*);
namespace lean {
namespace ir {
obj* mk_irrelevant_arg_core;
}}
obj* l_Lean_IR_Decl_params(obj*);
obj* l_Lean_IR_Arg_alphaEqv___main___boxed(obj*, obj*, obj*);
uint8 l_Array_anyMAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(obj*, obj*);
obj* l_Lean_IR_LitVal_beq___main___boxed(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_app_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_Expr_isPure___main___boxed(obj*);
obj* l_Lean_IR_VarId_HasToString(obj*);
namespace lean {
namespace ir {
obj* mk_unreachable_core;
}}
uint8 l_RBNode_isBlack___main___rarg(obj*);
uint8 l_Lean_IR_FnBody_isTerminal(obj*);
obj* l_Lean_IR_addVarRename(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_modifyJPs___spec__1(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_mmodifyBody___main___rarg(obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_isPure___main(obj*);
obj* l_Lean_IR_Decl_name(obj*);
uint8 l_Lean_IR_Arg_alphaEqv___main(obj*, obj*, obj*);
obj* l_Lean_IR_VarId_alphaEqv___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_mkDecl___boxed(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_CtorInfo_beq___main(obj*, obj*);
uint8 l_Lean_IR_FnBody_beq(obj*, obj*);
uint8 l_Lean_IR_args_alphaEqv(obj*, obj*, obj*);
obj* l_Lean_IR_CtorInfo_beq___main___boxed(obj*, obj*);
uint8 l_Lean_IR_Expr_alphaEqv___main(obj*, obj*, obj*);
uint8 l_Lean_IR_LocalContext_isLocalVar(obj*, obj*);
obj* l_Lean_IR_VarId_HasToString___closed__1;
uint8 l_Lean_IR_Expr_isPure(obj*);
uint8 l_Lean_IR_Index_lt(obj*, obj*);
obj* l_Lean_IR_Decl_params___main(obj*);
namespace lean {
namespace ir {
obj* mk_decl_core(obj*, obj*, uint8, obj*);
}}
uint8 l_Lean_IR_JoinPointId_HasBeq(obj*, obj*);
obj* l_Lean_IR_Decl_params___main___boxed(obj*);
uint8 l_Lean_IR_Arg_beq___main(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_uproj_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_flattenAux(obj*, obj*);
obj* l_Lean_IR_Arg_hasAeqv;
obj* l_Lean_IR_LocalContext_isParam___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_isPure___boxed(obj*);
uint8 l_Lean_IR_IRType_isScalar(uint8);
obj* l_Lean_IR_Alt_ctor(obj*, obj*);
obj* l_Lean_IR_MData_HasEmptyc;
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
uint8 l_Array_isEqvAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Arg_beq___main___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_isPure___main___boxed(obj*);
uint8 l_Lean_IR_Alt_isDefault(obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
obj* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1___boxed(obj*, obj*);
namespace lean {
usize usize_of_nat(obj*);
}
usize l_Lean_IR_VarId_Hashable(obj*);
obj* l_Lean_IR_push(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_papp_expr_core(obj*, obj*);
}}
obj* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(obj*, obj*);
namespace lean {
namespace ir {
obj* mk_ctor_expr_core(obj*, obj*, obj*, obj*, obj*, obj*);
}}
obj* l_Lean_IR_LocalContext_contains___boxed(obj*, obj*);
obj* l_Lean_IR_mmodifyJPs___rarg(obj*, obj*, obj*);
namespace lean {
namespace ir {
obj* mk_vdecl_core(obj*, uint8, obj*, obj*);
}}
obj* l_Lean_IR_JoinPointId_HasToString(obj*);
obj* l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_isObj___main___boxed(obj*);
obj* l_Lean_IR_IRType_beq___boxed(obj*, obj*);
obj* l_Lean_IR_Decl_name___main___boxed(obj*);
obj* l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(obj*, obj*, obj*);
uint8 l_Lean_IR_LocalContext_isJP(obj*, obj*);
obj* l_Lean_IR_Index_lt___boxed(obj*, obj*);
obj* l_Lean_IR_AltCore_setBody___main(obj*, obj*);
obj* l_Lean_IR_reshapeAux___main(obj*, obj*, obj*);
obj* l_Lean_IR_LitVal_HasBeq;
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_Expr_alphaEqv___main___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Arg_HasBeq;
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1(obj*);
obj* l_Lean_IR_CtorInfo_beq___boxed(obj*, obj*);
uint8 l_Lean_IR_IRType_isObj(uint8);
obj* l_Lean_IR_Arg_beq___boxed(obj*, obj*);
obj* l_Lean_IR_reshapeAux(obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_resetBody(obj*);
obj* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Arg_Inhabited;
obj* l_Lean_IR_MData_empty;
obj* l_Lean_IR_Inhabited;
obj* l_Lean_IR_Alt_isDefault___main___boxed(obj*);
uint8 l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1(obj*, obj*, obj*);
obj* l_Lean_IR_LocalContext_getType___boxed(obj*, obj*);
obj* l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_IRType_beq___main___boxed(obj*, obj*);
uint8 l_Lean_IR_IRType_isScalar___main(uint8);
obj* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(obj*, obj*);
uint8 l_Lean_IR_Index_lt(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::nat_dec_lt(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Index_lt___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Index_lt(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
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
usize l_Lean_IR_VarId_Hashable(obj* x_0) {
_start:
{
usize x_1; 
x_1 = lean::usize_of_nat(x_0);
return x_1;
}
}
obj* l_Lean_IR_VarId_Hashable___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_Lean_IR_VarId_Hashable(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
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
usize l_Lean_IR_JoinPointId_Hashable(obj* x_0) {
_start:
{
usize x_1; 
x_1 = lean::usize_of_nat(x_0);
return x_1;
}
}
obj* l_Lean_IR_JoinPointId_Hashable___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_Lean_IR_JoinPointId_Hashable(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
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
uint8 l_Lean_IR_IRType_isScalar___main(uint8 x_0) {
_start:
{
switch (x_0) {
case 6:
{
uint8 x_1; 
x_1 = 0;
return x_1;
}
case 7:
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
case 8:
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
default:
{
uint8 x_4; 
x_4 = 1;
return x_4;
}
}
}
}
obj* l_Lean_IR_IRType_isScalar___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_IR_IRType_isScalar___main(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_IR_IRType_isScalar(uint8 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_IRType_isScalar___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_IRType_isScalar___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_IR_IRType_isScalar(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_IR_IRType_isObj___main(uint8 x_0) {
_start:
{
switch (x_0) {
case 7:
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
case 8:
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
}
obj* l_Lean_IR_IRType_isObj___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_IR_IRType_isObj___main(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_IR_IRType_isObj(uint8 x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_IRType_isObj___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_IRType_isObj___boxed(obj* x_0) {
_start:
{
uint8 x_1; uint8 x_2; obj* x_3; 
x_1 = lean::unbox(x_0);
x_2 = l_Lean_IR_IRType_isObj(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
uint8 l_Lean_IR_Arg_beq___main(obj* x_0, obj* x_1) {
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
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_Lean_IR_Arg_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Arg_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_Arg_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_Arg_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Arg_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Arg_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_Arg_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Arg_beq___boxed), 2, 0);
return x_0;
}
}
obj* _init_l_Lean_IR_Arg_Inhabited() {
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
uint8 l_Lean_IR_CtorInfo_isRef(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; 
x_1 = lean::cnstr_get(x_0, 2);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
obj* x_4; uint8 x_5; 
x_4 = lean::cnstr_get(x_0, 3);
x_5 = lean::nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_0, 4);
x_7 = lean::nat_dec_lt(x_2, x_6);
return x_7;
}
else
{
uint8 x_8; 
x_8 = 1;
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = 1;
return x_9;
}
}
}
obj* l_Lean_IR_CtorInfo_isRef___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_CtorInfo_isRef(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_CtorInfo_isScalar(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_CtorInfo_isRef(x_0);
if (x_1 == 0)
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
}
}
obj* l_Lean_IR_CtorInfo_isScalar___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_CtorInfo_isScalar(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
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
x_0 = lean::box(13);
return x_0;
}
}
obj* _init_l_Lean_IR_FnBody_nil() {
_start:
{
obj* x_0; 
x_0 = lean::box(13);
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
obj* mk_jdecl_core(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_cnstr(1, 4, 0);
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
x_3 = lean::alloc_cnstr(10, 3, 0);
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
x_1 = lean::alloc_cnstr(11, 1, 0);
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
x_2 = lean::alloc_cnstr(12, 2, 0);
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
x_0 = lean::box(13);
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
x_0 = lean::box(13);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
uint8 l_Lean_IR_FnBody_isTerminal___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 10:
{
uint8 x_1; 
x_1 = 1;
return x_1;
}
case 11:
{
uint8 x_2; 
x_2 = 1;
return x_2;
}
case 12:
{
uint8 x_3; 
x_3 = 1;
return x_3;
}
case 13:
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
obj* x_11; 
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
return x_11;
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
lean::inc(x_0);
return x_0;
}
case 13:
{
return x_0;
}
default:
{
obj* x_16; 
x_16 = lean::cnstr_get(x_0, 2);
lean::inc(x_16);
return x_16;
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_0, 0);
x_12 = lean::cnstr_get(x_0, 1);
x_14 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_16 = x_0;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_0);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_12);
lean::cnstr_set(x_17, 2, x_14);
lean::cnstr_set(x_17, 3, x_1);
return x_17;
}
case 2:
{
obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_0, 0);
x_20 = lean::cnstr_get(x_0, 1);
x_22 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_24 = x_0;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_0);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_18);
lean::cnstr_set(x_25, 1, x_20);
lean::cnstr_set(x_25, 2, x_22);
lean::cnstr_set(x_25, 3, x_1);
return x_25;
}
case 3:
{
obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_0, 0);
x_28 = lean::cnstr_get(x_0, 1);
x_30 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 3);
 x_32 = x_0;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_0);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(3, 4, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_26);
lean::cnstr_set(x_33, 1, x_28);
lean::cnstr_set(x_33, 2, x_30);
lean::cnstr_set(x_33, 3, x_1);
return x_33;
}
case 4:
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
x_42 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*5);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 4);
 x_43 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(4, 5, 1);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set(x_44, 1, x_36);
lean::cnstr_set(x_44, 2, x_38);
lean::cnstr_set(x_44, 3, x_40);
lean::cnstr_set(x_44, 4, x_1);
lean::cnstr_set_scalar(x_44, sizeof(void*)*5, x_42);
x_45 = x_44;
return x_45;
}
case 5:
{
obj* x_46; obj* x_48; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_0, 0);
x_48 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_50 = x_0;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_0);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(5, 3, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_46);
lean::cnstr_set(x_51, 1, x_48);
lean::cnstr_set(x_51, 2, x_1);
return x_51;
}
case 6:
{
obj* x_52; obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
x_52 = lean::cnstr_get(x_0, 0);
x_54 = lean::cnstr_get(x_0, 1);
x_56 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_57 = x_0;
} else {
 lean::inc(x_52);
 lean::inc(x_54);
 lean::dec(x_0);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(6, 3, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_52);
lean::cnstr_set(x_58, 1, x_54);
lean::cnstr_set(x_58, 2, x_1);
lean::cnstr_set_scalar(x_58, sizeof(void*)*3, x_56);
x_59 = x_58;
return x_59;
}
case 7:
{
obj* x_60; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; 
x_60 = lean::cnstr_get(x_0, 0);
x_62 = lean::cnstr_get(x_0, 1);
x_64 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 2);
 x_65 = x_0;
} else {
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_0);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(7, 3, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_60);
lean::cnstr_set(x_66, 1, x_62);
lean::cnstr_set(x_66, 2, x_1);
lean::cnstr_set_scalar(x_66, sizeof(void*)*3, x_64);
x_67 = x_66;
return x_67;
}
case 8:
{
obj* x_68; obj* x_70; obj* x_71; 
x_68 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 1);
 x_70 = x_0;
} else {
 lean::inc(x_68);
 lean::dec(x_0);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(8, 2, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_1);
return x_71;
}
case 9:
{
obj* x_72; obj* x_74; obj* x_75; 
x_72 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 1);
 x_74 = x_0;
} else {
 lean::inc(x_72);
 lean::dec(x_0);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(9, 2, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_1);
return x_75;
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
x_1 = lean::box(13);
x_2 = l_Lean_IR_FnBody_setBody___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_FnBody_split(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_Lean_IR_FnBody_body___main(x_0);
x_2 = lean::box(13);
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
x_2 = lean::box(13);
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
x_11 = lean::box(13);
x_12 = l_Lean_IR_FnBody_setBody___main(x_11, x_2);
x_1 = x_6;
x_2 = x_12;
goto _start;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::array_fget(x_0, x_6);
x_15 = lean::box(13);
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
x_9 = lean::box(13);
x_10 = lean::array_fset(x_2, x_1, x_9);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_1, x_11);
switch (lean::obj_tag(x_8)) {
case 1:
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get(x_8, 2);
x_19 = lean::cnstr_get(x_8, 3);
if (lean::is_exclusive(x_8)) {
 x_21 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_8);
 x_21 = lean::box(0);
}
lean::inc(x_0);
x_23 = lean::apply_1(x_0, x_17);
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_15);
lean::cnstr_set(x_24, 2, x_23);
lean::cnstr_set(x_24, 3, x_19);
x_25 = lean::array_fset(x_10, x_1, x_24);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_25;
goto _start;
}
default:
{
obj* x_28; 
x_28 = lean::array_fset(x_10, x_1, x_8);
lean::dec(x_1);
x_1 = x_12;
x_2 = x_28;
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
obj* l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_2);
lean::cnstr_set(x_11, 2, x_4);
lean::cnstr_set(x_11, 3, x_3);
x_12 = lean::apply_2(x_8, lean::box(0), x_11);
return x_12;
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
x_17 = lean::box(13);
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
obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_35; obj* x_36; obj* x_38; obj* x_39; 
x_26 = lean::cnstr_get(x_16, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_16, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_16, 2);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_16, 3);
lean::inc(x_32);
lean::dec(x_16);
x_35 = lean::apply_1(x_1, x_30);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_hmmapAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2), 5, 4);
lean::closure_set(x_36, 0, x_0);
lean::closure_set(x_36, 1, x_26);
lean::closure_set(x_36, 2, x_28);
lean::closure_set(x_36, 3, x_32);
lean::inc(x_19);
x_38 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_35, x_36);
x_39 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_38, x_23);
return x_39;
}
default:
{
obj* x_41; 
lean::dec(x_1);
x_41 = lean::box(0);
x_24 = x_41;
goto lbl_25;
}
}
lbl_25:
{
obj* x_43; obj* x_46; obj* x_49; obj* x_50; 
lean::dec(x_24);
x_43 = lean::cnstr_get(x_0, 0);
lean::inc(x_43);
lean::dec(x_0);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = lean::apply_2(x_46, lean::box(0), x_16);
x_50 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_49, x_23);
return x_50;
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
obj* _init_l_Lean_IR_Decl_Inhabited() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::mk_empty_array(x_0);
x_2 = lean::box(0);
x_3 = 6;
x_4 = lean::box(13);
x_5 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set_scalar(x_5, sizeof(void*)*3, x_3);
x_6 = x_5;
return x_6;
}
}
obj* l_Lean_IR_Decl_name___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_IR_Decl_name___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_name___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_name(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_name___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_name___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_name(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_params___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* l_Lean_IR_Decl_params___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_params___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_params(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_params___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_params___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Decl_params(x_0);
lean::dec(x_0);
return x_1;
}
}
uint8 l_Lean_IR_Decl_resultType___main(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
return x_1;
}
}
obj* l_Lean_IR_Decl_resultType___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Decl_resultType___main(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
uint8 l_Lean_IR_Decl_resultType(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_Lean_IR_Decl_resultType___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Decl_resultType___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = l_Lean_IR_Decl_resultType(x_0);
x_2 = lean::box(x_1);
lean::dec(x_0);
return x_2;
}
}
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
namespace lean {
namespace ir {
obj* mk_extern_decl_core(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(1, 3, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*3, x_2);
x_5 = x_4;
return x_5;
}
}
}}
obj* l_Lean_IR_mkExternDecl___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = lean::ir::mk_extern_decl_core(x_0, x_1, x_4, x_3);
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
uint8 l_Array_anyMAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(obj* x_0, obj* x_1) {
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
lean::dec(x_1);
return x_11;
}
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_7);
x_19 = lean::mk_nat_obj(1ul);
x_20 = lean::nat_add(x_1, x_19);
lean::dec(x_1);
x_1 = x_20;
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
case 9:
{
obj* x_15; 
x_15 = lean::cnstr_get(x_0, 1);
x_0 = x_15;
goto _start;
}
case 10:
{
obj* x_17; obj* x_18; uint8 x_19; 
x_17 = lean::cnstr_get(x_0, 2);
x_18 = lean::mk_nat_obj(0ul);
x_19 = l_Array_anyMAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(x_17, x_18);
return x_19;
}
case 11:
{
uint8 x_20; 
x_20 = 1;
return x_20;
}
case 12:
{
uint8 x_21; 
x_21 = 1;
return x_21;
}
case 13:
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
obj* l_Array_anyMAux___main___at_Lean_IR_FnBody_isPure___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Array_anyMAux___main___at_Lean_IR_FnBody_isPure___main___spec__1(x_0, x_1);
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
obj* _init_l_Lean_IR_vsetInh() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(obj* x_0, obj* x_1, obj* x_2) {
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
x_22 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_13, x_1, x_2);
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
x_25 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_7, x_1, x_2);
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
x_44 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_34, x_1, x_2);
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
x_47 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_34, x_1, x_2);
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
x_181 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_28, x_1, x_2);
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
x_184 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_28, x_1, x_2);
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
obj* l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_RBNode_isRed___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_0, x_1, x_2);
x_6 = l_RBNode_setBlack___main___rarg(x_5);
return x_6;
}
}
}
obj* l_Lean_IR_LocalContext_addLocal(obj* x_0, obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set_scalar(x_4, sizeof(void*)*1, x_2);
x_5 = x_4;
x_6 = l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_0, x_1, x_5);
return x_6;
}
}
obj* l_Lean_IR_LocalContext_addLocal___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = l_Lean_IR_LocalContext_addLocal(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* l_Lean_IR_LocalContext_addJP(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_0, x_1, x_4);
return x_5;
}
}
obj* l_Lean_IR_LocalContext_addParam(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_4; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1 + 1);
lean::dec(x_1);
x_6 = lean::alloc_cnstr(0, 0, 1);
lean::cnstr_set_scalar(x_6, 0, x_4);
x_7 = x_6;
x_8 = l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_0, x_2, x_7);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_Lean_IR_LocalContext_addParam(x_3, x_8);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_2, x_10);
lean::dec(x_2);
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
obj* l_Lean_IR_LocalContext_addParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_1, x_2, x_0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_LocalContext_addParams___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_LocalContext_addParams(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(obj* x_0, obj* x_1) {
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
uint8 l_Lean_IR_LocalContext_isJP(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
switch (lean::obj_tag(x_4)) {
case 2:
{
uint8 x_8; 
lean::dec(x_4);
x_8 = 1;
return x_8;
}
default:
{
uint8 x_10; 
lean::dec(x_4);
x_10 = 0;
return x_10;
}
}
}
}
}
obj* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_LocalContext_isJP___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_LocalContext_isJP(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_LocalContext_getJPBody(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 2:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_Lean_IR_LocalContext_getJPBody___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_LocalContext_getJPBody(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_LocalContext_getJPParams(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 2:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
default:
{
obj* x_13; 
lean::dec(x_6);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
}
}
}
}
obj* l_Lean_IR_LocalContext_getJPParams___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_LocalContext_getJPParams(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
uint8 l_Lean_IR_LocalContext_isParam(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
switch (lean::obj_tag(x_4)) {
case 0:
{
uint8 x_8; 
lean::dec(x_4);
x_8 = 1;
return x_8;
}
default:
{
uint8 x_10; 
lean::dec(x_4);
x_10 = 0;
return x_10;
}
}
}
}
}
obj* l_Lean_IR_LocalContext_isParam___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_LocalContext_isParam(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_LocalContext_isLocalVar(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
switch (lean::obj_tag(x_4)) {
case 1:
{
uint8 x_8; 
lean::dec(x_4);
x_8 = 1;
return x_8;
}
default:
{
uint8 x_10; 
lean::dec(x_4);
x_10 = 0;
return x_10;
}
}
}
}
}
obj* l_Lean_IR_LocalContext_isLocalVar___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_LocalContext_isLocalVar(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_LocalContext_contains(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8 x_5; 
lean::dec(x_2);
x_5 = 1;
return x_5;
}
}
}
obj* l_Lean_IR_LocalContext_contains___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_LocalContext_contains(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_10; uint8 x_11; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_8 = lean::cnstr_get(x_1, 3);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 lean::cnstr_set(x_1, 1, lean::box(0));
 lean::cnstr_set(x_1, 2, lean::box(0));
 lean::cnstr_set(x_1, 3, lean::box(0));
 x_10 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_1);
 x_10 = lean::box(0);
}
x_11 = lean::nat_dec_lt(x_0, x_4);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = lean::nat_dec_lt(x_4, x_0);
if (x_12 == 0)
{
obj* x_16; 
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_6);
x_16 = l_RBNode_appendTrees___main___rarg(x_2, x_8);
return x_16;
}
else
{
uint8 x_17; 
x_17 = l_RBNode_isBlack___main___rarg(x_8);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; obj* x_20; obj* x_21; 
x_18 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_0, x_8);
x_19 = 0;
if (lean::is_scalar(x_10)) {
 x_20 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_20 = x_10;
}
lean::cnstr_set(x_20, 0, x_2);
lean::cnstr_set(x_20, 1, x_4);
lean::cnstr_set(x_20, 2, x_6);
lean::cnstr_set(x_20, 3, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*4, x_19);
x_21 = x_20;
return x_21;
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_10);
x_23 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_0, x_8);
x_24 = l_RBNode_balRight___rarg(x_2, x_4, x_6, x_23);
return x_24;
}
}
}
else
{
uint8 x_25; 
x_25 = l_RBNode_isBlack___main___rarg(x_2);
if (x_25 == 0)
{
obj* x_26; uint8 x_27; obj* x_28; obj* x_29; 
x_26 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_0, x_2);
x_27 = 0;
if (lean::is_scalar(x_10)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_10;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_4);
lean::cnstr_set(x_28, 2, x_6);
lean::cnstr_set(x_28, 3, x_8);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_27);
x_29 = x_28;
return x_29;
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_10);
x_31 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_0, x_2);
x_32 = l_RBNode_balLeft___main___rarg(x_31, x_4, x_6, x_8);
return x_32;
}
}
}
}
}
obj* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_0, x_1);
x_3 = l_RBNode_setBlack___main___rarg(x_2);
return x_3;
}
}
obj* l_Lean_IR_LocalContext_eraseJoinPointDecl(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(x_1, x_0);
return x_2;
}
}
obj* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_LocalContext_eraseJoinPointDecl(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_LocalContext_getType(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_0, x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 x_6 = x_2;
} else {
 lean::inc(x_4);
 lean::dec(x_2);
 x_6 = lean::box(0);
}
switch (lean::obj_tag(x_4)) {
case 0:
{
uint8 x_7; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get_scalar<uint8>(x_4, 0);
lean::dec(x_4);
x_9 = lean::box(x_7);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
case 1:
{
uint8 x_11; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
lean::dec(x_4);
x_13 = lean::box(x_11);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
default:
{
obj* x_17; 
lean::dec(x_6);
lean::dec(x_4);
x_17 = lean::box(0);
return x_17;
}
}
}
}
}
obj* l_Lean_IR_LocalContext_getType___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_LocalContext_getType(x_0, x_1);
lean::dec(x_1);
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
obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_1, 1);
x_15 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get(x_2, 1);
x_17 = lean::nat_dec_eq(x_13, x_15);
if (x_17 == 0)
{
uint8 x_19; 
lean::dec(x_0);
x_19 = 0;
return x_19;
}
else
{
uint8 x_20; 
x_20 = l_Lean_IR_VarId_alphaEqv(x_0, x_14, x_16);
return x_20;
}
}
default:
{
uint8 x_22; 
lean::dec(x_0);
x_22 = 0;
return x_22;
}
}
}
case 2:
{
uint8 x_23; 
x_23 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; obj* x_30; uint8 x_32; 
x_24 = lean::cnstr_get(x_1, 0);
x_25 = lean::cnstr_get(x_1, 1);
x_26 = lean::cnstr_get(x_1, 2);
x_27 = lean::cnstr_get(x_2, 0);
x_28 = lean::cnstr_get(x_2, 1);
x_29 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_30 = lean::cnstr_get(x_2, 2);
lean::inc(x_0);
x_32 = l_Lean_IR_VarId_alphaEqv(x_0, x_24, x_27);
if (x_32 == 0)
{
uint8 x_34; 
lean::dec(x_0);
x_34 = 0;
return x_34;
}
else
{
uint8 x_35; 
x_35 = l_Lean_IR_CtorInfo_beq___main(x_25, x_28);
if (x_35 == 0)
{
uint8 x_37; 
lean::dec(x_0);
x_37 = 0;
return x_37;
}
else
{
if (x_23 == 0)
{
if (x_29 == 0)
{
uint8 x_38; 
x_38 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_26, x_30);
return x_38;
}
else
{
uint8 x_40; 
lean::dec(x_0);
x_40 = 0;
return x_40;
}
}
else
{
if (x_29 == 0)
{
uint8 x_42; 
lean::dec(x_0);
x_42 = 0;
return x_42;
}
else
{
uint8 x_43; 
x_43 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_26, x_30);
return x_43;
}
}
}
}
}
default:
{
uint8 x_45; 
lean::dec(x_0);
x_45 = 0;
return x_45;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; uint8 x_50; 
x_46 = lean::cnstr_get(x_1, 0);
x_47 = lean::cnstr_get(x_1, 1);
x_48 = lean::cnstr_get(x_2, 0);
x_49 = lean::cnstr_get(x_2, 1);
x_50 = lean::nat_dec_eq(x_46, x_48);
if (x_50 == 0)
{
uint8 x_52; 
lean::dec(x_0);
x_52 = 0;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_Lean_IR_VarId_alphaEqv(x_0, x_47, x_49);
return x_53;
}
}
default:
{
uint8 x_55; 
lean::dec(x_0);
x_55 = 0;
return x_55;
}
}
}
case 4:
{
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_1, 0);
x_57 = lean::cnstr_get(x_1, 1);
x_58 = lean::cnstr_get(x_2, 0);
x_59 = lean::cnstr_get(x_2, 1);
x_60 = lean::nat_dec_eq(x_56, x_58);
if (x_60 == 0)
{
uint8 x_62; 
lean::dec(x_0);
x_62 = 0;
return x_62;
}
else
{
uint8 x_63; 
x_63 = l_Lean_IR_VarId_alphaEqv(x_0, x_57, x_59);
return x_63;
}
}
default:
{
uint8 x_65; 
lean::dec(x_0);
x_65 = 0;
return x_65;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; uint8 x_72; 
x_66 = lean::cnstr_get(x_1, 0);
x_67 = lean::cnstr_get(x_1, 1);
x_68 = lean::cnstr_get(x_1, 2);
x_69 = lean::cnstr_get(x_2, 0);
x_70 = lean::cnstr_get(x_2, 1);
x_71 = lean::cnstr_get(x_2, 2);
x_72 = lean::nat_dec_eq(x_66, x_69);
if (x_72 == 0)
{
uint8 x_74; 
lean::dec(x_0);
x_74 = 0;
return x_74;
}
else
{
uint8 x_75; 
x_75 = lean::nat_dec_eq(x_67, x_70);
if (x_75 == 0)
{
uint8 x_77; 
lean::dec(x_0);
x_77 = 0;
return x_77;
}
else
{
uint8 x_78; 
x_78 = l_Lean_IR_VarId_alphaEqv(x_0, x_68, x_71);
return x_78;
}
}
}
default:
{
uint8 x_80; 
lean::dec(x_0);
x_80 = 0;
return x_80;
}
}
}
case 6:
{
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; uint8 x_85; 
x_81 = lean::cnstr_get(x_1, 0);
x_82 = lean::cnstr_get(x_1, 1);
x_83 = lean::cnstr_get(x_2, 0);
x_84 = lean::cnstr_get(x_2, 1);
x_85 = lean_name_dec_eq(x_81, x_83);
if (x_85 == 0)
{
uint8 x_87; 
lean::dec(x_0);
x_87 = 0;
return x_87;
}
else
{
uint8 x_88; 
x_88 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_82, x_84);
return x_88;
}
}
default:
{
uint8 x_90; 
lean::dec(x_0);
x_90 = 0;
return x_90;
}
}
}
case 7:
{
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_91; obj* x_92; obj* x_93; uint8 x_94; 
x_91 = lean::cnstr_get(x_1, 0);
x_92 = lean::cnstr_get(x_2, 0);
x_93 = lean::cnstr_get(x_2, 1);
x_94 = lean_name_dec_eq(x_91, x_92);
if (x_94 == 0)
{
uint8 x_96; 
lean::dec(x_0);
x_96 = 0;
return x_96;
}
else
{
uint8 x_97; 
x_97 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_93, x_93);
return x_97;
}
}
default:
{
uint8 x_99; 
lean::dec(x_0);
x_99 = 0;
return x_99;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; uint8 x_105; 
x_100 = lean::cnstr_get(x_1, 0);
x_101 = lean::cnstr_get(x_1, 1);
x_102 = lean::cnstr_get(x_2, 0);
x_103 = lean::cnstr_get(x_2, 1);
lean::inc(x_0);
x_105 = l_Lean_IR_VarId_alphaEqv(x_0, x_100, x_102);
if (x_105 == 0)
{
uint8 x_107; 
lean::dec(x_0);
x_107 = 0;
return x_107;
}
else
{
uint8 x_108; 
x_108 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_101, x_103);
return x_108;
}
}
default:
{
uint8 x_110; 
lean::dec(x_0);
x_110 = 0;
return x_110;
}
}
}
case 9:
{
uint8 x_111; 
x_111 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_112; uint8 x_113; obj* x_114; uint8 x_115; 
x_112 = lean::cnstr_get(x_1, 0);
x_113 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
x_114 = lean::cnstr_get(x_2, 0);
x_115 = l_Lean_IR_IRType_beq___main(x_111, x_113);
if (x_115 == 0)
{
uint8 x_117; 
lean::dec(x_0);
x_117 = 0;
return x_117;
}
else
{
uint8 x_118; 
x_118 = l_Lean_IR_VarId_alphaEqv(x_0, x_112, x_114);
return x_118;
}
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
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_121; obj* x_122; uint8 x_123; 
x_121 = lean::cnstr_get(x_1, 0);
x_122 = lean::cnstr_get(x_2, 0);
x_123 = l_Lean_IR_VarId_alphaEqv(x_0, x_121, x_122);
return x_123;
}
default:
{
uint8 x_125; 
lean::dec(x_0);
x_125 = 0;
return x_125;
}
}
}
case 11:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_127; obj* x_128; uint8 x_129; 
x_127 = lean::cnstr_get(x_1, 0);
x_128 = lean::cnstr_get(x_2, 0);
x_129 = l_Lean_IR_LitVal_beq___main(x_127, x_128);
return x_129;
}
default:
{
uint8 x_130; 
x_130 = 0;
return x_130;
}
}
}
case 12:
{
switch (lean::obj_tag(x_2)) {
case 12:
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
default:
{
switch (lean::obj_tag(x_2)) {
case 13:
{
obj* x_136; obj* x_137; uint8 x_138; 
x_136 = lean::cnstr_get(x_1, 0);
x_137 = lean::cnstr_get(x_2, 0);
x_138 = l_Lean_IR_VarId_alphaEqv(x_0, x_136, x_137);
return x_138;
}
default:
{
uint8 x_140; 
lean::dec(x_0);
x_140 = 0;
return x_140;
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
case 13:
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
switch (lean::obj_tag(x_2)) {
case 1:
{
obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_58; obj* x_60; obj* x_62; obj* x_66; 
x_47 = lean::cnstr_get(x_1, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_1, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_1, 2);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_1, 3);
lean::inc(x_53);
lean::dec(x_1);
x_56 = lean::cnstr_get(x_2, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_2, 1);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_2, 2);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_2, 3);
lean::inc(x_62);
lean::dec(x_2);
lean::inc(x_0);
x_66 = l_Lean_IR_addParamsRename(x_0, x_49, x_58);
lean::dec(x_58);
lean::dec(x_49);
if (lean::obj_tag(x_66) == 0)
{
uint8 x_76; 
lean::dec(x_0);
lean::dec(x_53);
lean::dec(x_56);
lean::dec(x_62);
lean::dec(x_51);
lean::dec(x_47);
lean::dec(x_60);
x_76 = 0;
return x_76;
}
else
{
obj* x_77; uint8 x_80; 
x_77 = lean::cnstr_get(x_66, 0);
lean::inc(x_77);
lean::dec(x_66);
x_80 = l_Lean_IR_FnBody_alphaEqv___main(x_77, x_51, x_60);
if (x_80 == 0)
{
uint8 x_86; 
lean::dec(x_0);
lean::dec(x_53);
lean::dec(x_56);
lean::dec(x_62);
lean::dec(x_47);
x_86 = 0;
return x_86;
}
else
{
obj* x_87; 
x_87 = l_Lean_IR_addVarRename(x_0, x_47, x_56);
x_0 = x_87;
x_1 = x_53;
x_2 = x_62;
goto _start;
}
}
}
case 13:
{
uint8 x_91; 
lean::dec(x_1);
lean::dec(x_0);
x_91 = 0;
return x_91;
}
default:
{
uint8 x_95; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_95 = 0;
return x_95;
}
}
}
case 2:
{
switch (lean::obj_tag(x_2)) {
case 2:
{
obj* x_96; obj* x_98; obj* x_100; obj* x_102; obj* x_105; obj* x_107; obj* x_109; obj* x_111; uint8 x_115; 
x_96 = lean::cnstr_get(x_1, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_1, 1);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_1, 2);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_1, 3);
lean::inc(x_102);
lean::dec(x_1);
x_105 = lean::cnstr_get(x_2, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_2, 1);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_2, 2);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_2, 3);
lean::inc(x_111);
lean::dec(x_2);
lean::inc(x_0);
x_115 = l_Lean_IR_VarId_alphaEqv(x_0, x_96, x_105);
lean::dec(x_105);
lean::dec(x_96);
if (x_115 == 0)
{
uint8 x_125; 
lean::dec(x_109);
lean::dec(x_111);
lean::dec(x_98);
lean::dec(x_107);
lean::dec(x_100);
lean::dec(x_102);
lean::dec(x_0);
x_125 = 0;
return x_125;
}
else
{
uint8 x_126; 
x_126 = lean::nat_dec_eq(x_98, x_107);
lean::dec(x_107);
lean::dec(x_98);
if (x_126 == 0)
{
uint8 x_134; 
lean::dec(x_109);
lean::dec(x_111);
lean::dec(x_100);
lean::dec(x_102);
lean::dec(x_0);
x_134 = 0;
return x_134;
}
else
{
uint8 x_136; 
lean::inc(x_0);
x_136 = l_Lean_IR_VarId_alphaEqv(x_0, x_100, x_109);
lean::dec(x_109);
lean::dec(x_100);
if (x_136 == 0)
{
uint8 x_142; 
lean::dec(x_111);
lean::dec(x_102);
lean::dec(x_0);
x_142 = 0;
return x_142;
}
else
{
x_1 = x_102;
x_2 = x_111;
goto _start;
}
}
}
}
case 13:
{
uint8 x_146; 
lean::dec(x_1);
lean::dec(x_0);
x_146 = 0;
return x_146;
}
default:
{
uint8 x_150; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_150 = 0;
return x_150;
}
}
}
case 3:
{
switch (lean::obj_tag(x_2)) {
case 3:
{
obj* x_151; obj* x_153; obj* x_155; obj* x_157; obj* x_160; obj* x_162; obj* x_164; obj* x_166; uint8 x_170; 
x_151 = lean::cnstr_get(x_1, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_1, 1);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_1, 2);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_1, 3);
lean::inc(x_157);
lean::dec(x_1);
x_160 = lean::cnstr_get(x_2, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_2, 1);
lean::inc(x_162);
x_164 = lean::cnstr_get(x_2, 2);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_2, 3);
lean::inc(x_166);
lean::dec(x_2);
lean::inc(x_0);
x_170 = l_Lean_IR_VarId_alphaEqv(x_0, x_151, x_160);
lean::dec(x_160);
lean::dec(x_151);
if (x_170 == 0)
{
uint8 x_180; 
lean::dec(x_0);
lean::dec(x_166);
lean::dec(x_164);
lean::dec(x_153);
lean::dec(x_162);
lean::dec(x_157);
lean::dec(x_155);
x_180 = 0;
return x_180;
}
else
{
uint8 x_181; 
x_181 = lean::nat_dec_eq(x_153, x_162);
lean::dec(x_162);
lean::dec(x_153);
if (x_181 == 0)
{
uint8 x_189; 
lean::dec(x_0);
lean::dec(x_166);
lean::dec(x_164);
lean::dec(x_157);
lean::dec(x_155);
x_189 = 0;
return x_189;
}
else
{
uint8 x_191; 
lean::inc(x_0);
x_191 = l_Lean_IR_VarId_alphaEqv(x_0, x_155, x_164);
lean::dec(x_164);
lean::dec(x_155);
if (x_191 == 0)
{
uint8 x_197; 
lean::dec(x_0);
lean::dec(x_166);
lean::dec(x_157);
x_197 = 0;
return x_197;
}
else
{
x_1 = x_157;
x_2 = x_166;
goto _start;
}
}
}
}
case 13:
{
uint8 x_201; 
lean::dec(x_1);
lean::dec(x_0);
x_201 = 0;
return x_201;
}
default:
{
uint8 x_205; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_205 = 0;
return x_205;
}
}
}
case 4:
{
uint8 x_206; 
x_206 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*5);
switch (lean::obj_tag(x_2)) {
case 4:
{
obj* x_207; obj* x_209; obj* x_211; obj* x_213; obj* x_215; obj* x_218; obj* x_220; obj* x_222; obj* x_224; uint8 x_226; obj* x_227; uint8 x_231; 
x_207 = lean::cnstr_get(x_1, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_1, 1);
lean::inc(x_209);
x_211 = lean::cnstr_get(x_1, 2);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_1, 3);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_1, 4);
lean::inc(x_215);
lean::dec(x_1);
x_218 = lean::cnstr_get(x_2, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_2, 1);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_2, 2);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_2, 3);
lean::inc(x_224);
x_226 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*5);
x_227 = lean::cnstr_get(x_2, 4);
lean::inc(x_227);
lean::dec(x_2);
lean::inc(x_0);
x_231 = l_Lean_IR_VarId_alphaEqv(x_0, x_207, x_218);
lean::dec(x_218);
lean::dec(x_207);
if (x_231 == 0)
{
uint8 x_243; 
lean::dec(x_224);
lean::dec(x_227);
lean::dec(x_222);
lean::dec(x_215);
lean::dec(x_209);
lean::dec(x_220);
lean::dec(x_0);
lean::dec(x_213);
lean::dec(x_211);
x_243 = 0;
return x_243;
}
else
{
uint8 x_244; 
x_244 = lean::nat_dec_eq(x_209, x_220);
lean::dec(x_220);
lean::dec(x_209);
if (x_244 == 0)
{
uint8 x_254; 
lean::dec(x_224);
lean::dec(x_227);
lean::dec(x_222);
lean::dec(x_215);
lean::dec(x_0);
lean::dec(x_213);
lean::dec(x_211);
x_254 = 0;
return x_254;
}
else
{
uint8 x_255; 
x_255 = lean::nat_dec_eq(x_211, x_222);
lean::dec(x_222);
lean::dec(x_211);
if (x_255 == 0)
{
uint8 x_263; 
lean::dec(x_224);
lean::dec(x_227);
lean::dec(x_215);
lean::dec(x_0);
lean::dec(x_213);
x_263 = 0;
return x_263;
}
else
{
uint8 x_265; 
lean::inc(x_0);
x_265 = l_Lean_IR_VarId_alphaEqv(x_0, x_213, x_224);
lean::dec(x_224);
lean::dec(x_213);
if (x_265 == 0)
{
uint8 x_271; 
lean::dec(x_227);
lean::dec(x_215);
lean::dec(x_0);
x_271 = 0;
return x_271;
}
else
{
uint8 x_272; 
x_272 = l_Lean_IR_IRType_beq___main(x_206, x_226);
if (x_272 == 0)
{
uint8 x_276; 
lean::dec(x_227);
lean::dec(x_215);
lean::dec(x_0);
x_276 = 0;
return x_276;
}
else
{
x_1 = x_215;
x_2 = x_227;
goto _start;
}
}
}
}
}
}
case 13:
{
uint8 x_280; 
lean::dec(x_1);
lean::dec(x_0);
x_280 = 0;
return x_280;
}
default:
{
uint8 x_284; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_284 = 0;
return x_284;
}
}
}
case 5:
{
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_285; obj* x_287; obj* x_289; obj* x_292; obj* x_294; obj* x_296; uint8 x_300; 
x_285 = lean::cnstr_get(x_1, 0);
lean::inc(x_285);
x_287 = lean::cnstr_get(x_1, 1);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_1, 2);
lean::inc(x_289);
lean::dec(x_1);
x_292 = lean::cnstr_get(x_2, 0);
lean::inc(x_292);
x_294 = lean::cnstr_get(x_2, 1);
lean::inc(x_294);
x_296 = lean::cnstr_get(x_2, 2);
lean::inc(x_296);
lean::dec(x_2);
lean::inc(x_0);
x_300 = l_Lean_IR_VarId_alphaEqv(x_0, x_285, x_292);
lean::dec(x_292);
lean::dec(x_285);
if (x_300 == 0)
{
uint8 x_308; 
lean::dec(x_287);
lean::dec(x_289);
lean::dec(x_294);
lean::dec(x_296);
lean::dec(x_0);
x_308 = 0;
return x_308;
}
else
{
uint8 x_309; 
x_309 = lean::nat_dec_eq(x_287, x_294);
lean::dec(x_294);
lean::dec(x_287);
if (x_309 == 0)
{
uint8 x_315; 
lean::dec(x_289);
lean::dec(x_296);
lean::dec(x_0);
x_315 = 0;
return x_315;
}
else
{
x_1 = x_289;
x_2 = x_296;
goto _start;
}
}
}
case 13:
{
uint8 x_319; 
lean::dec(x_1);
lean::dec(x_0);
x_319 = 0;
return x_319;
}
default:
{
uint8 x_323; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_323 = 0;
return x_323;
}
}
}
case 6:
{
uint8 x_324; 
x_324 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 6:
{
obj* x_325; obj* x_327; obj* x_329; obj* x_332; obj* x_334; uint8 x_336; obj* x_337; uint8 x_341; 
x_325 = lean::cnstr_get(x_1, 0);
lean::inc(x_325);
x_327 = lean::cnstr_get(x_1, 1);
lean::inc(x_327);
x_329 = lean::cnstr_get(x_1, 2);
lean::inc(x_329);
lean::dec(x_1);
x_332 = lean::cnstr_get(x_2, 0);
lean::inc(x_332);
x_334 = lean::cnstr_get(x_2, 1);
lean::inc(x_334);
x_336 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_337 = lean::cnstr_get(x_2, 2);
lean::inc(x_337);
lean::dec(x_2);
lean::inc(x_0);
x_341 = l_Lean_IR_VarId_alphaEqv(x_0, x_325, x_332);
lean::dec(x_332);
lean::dec(x_325);
if (x_341 == 0)
{
uint8 x_349; 
lean::dec(x_0);
lean::dec(x_327);
lean::dec(x_329);
lean::dec(x_334);
lean::dec(x_337);
x_349 = 0;
return x_349;
}
else
{
uint8 x_350; 
x_350 = lean::nat_dec_eq(x_327, x_334);
lean::dec(x_334);
lean::dec(x_327);
if (x_350 == 0)
{
uint8 x_356; 
lean::dec(x_0);
lean::dec(x_329);
lean::dec(x_337);
x_356 = 0;
return x_356;
}
else
{
if (x_324 == 0)
{
if (x_336 == 0)
{
x_1 = x_329;
x_2 = x_337;
goto _start;
}
else
{
uint8 x_361; 
lean::dec(x_0);
lean::dec(x_329);
lean::dec(x_337);
x_361 = 0;
return x_361;
}
}
else
{
if (x_336 == 0)
{
uint8 x_365; 
lean::dec(x_0);
lean::dec(x_329);
lean::dec(x_337);
x_365 = 0;
return x_365;
}
else
{
x_1 = x_329;
x_2 = x_337;
goto _start;
}
}
}
}
}
case 13:
{
uint8 x_369; 
lean::dec(x_1);
lean::dec(x_0);
x_369 = 0;
return x_369;
}
default:
{
uint8 x_373; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_373 = 0;
return x_373;
}
}
}
case 7:
{
uint8 x_374; 
x_374 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*3);
switch (lean::obj_tag(x_2)) {
case 7:
{
obj* x_375; obj* x_377; obj* x_379; obj* x_382; obj* x_384; uint8 x_386; obj* x_387; uint8 x_391; 
x_375 = lean::cnstr_get(x_1, 0);
lean::inc(x_375);
x_377 = lean::cnstr_get(x_1, 1);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_1, 2);
lean::inc(x_379);
lean::dec(x_1);
x_382 = lean::cnstr_get(x_2, 0);
lean::inc(x_382);
x_384 = lean::cnstr_get(x_2, 1);
lean::inc(x_384);
x_386 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*3);
x_387 = lean::cnstr_get(x_2, 2);
lean::inc(x_387);
lean::dec(x_2);
lean::inc(x_0);
x_391 = l_Lean_IR_VarId_alphaEqv(x_0, x_375, x_382);
lean::dec(x_382);
lean::dec(x_375);
if (x_391 == 0)
{
uint8 x_399; 
lean::dec(x_387);
lean::dec(x_377);
lean::dec(x_384);
lean::dec(x_379);
lean::dec(x_0);
x_399 = 0;
return x_399;
}
else
{
uint8 x_400; 
x_400 = lean::nat_dec_eq(x_377, x_384);
lean::dec(x_384);
lean::dec(x_377);
if (x_400 == 0)
{
uint8 x_406; 
lean::dec(x_387);
lean::dec(x_379);
lean::dec(x_0);
x_406 = 0;
return x_406;
}
else
{
if (x_374 == 0)
{
if (x_386 == 0)
{
x_1 = x_379;
x_2 = x_387;
goto _start;
}
else
{
uint8 x_411; 
lean::dec(x_387);
lean::dec(x_379);
lean::dec(x_0);
x_411 = 0;
return x_411;
}
}
else
{
if (x_386 == 0)
{
uint8 x_415; 
lean::dec(x_387);
lean::dec(x_379);
lean::dec(x_0);
x_415 = 0;
return x_415;
}
else
{
x_1 = x_379;
x_2 = x_387;
goto _start;
}
}
}
}
}
case 13:
{
uint8 x_419; 
lean::dec(x_1);
lean::dec(x_0);
x_419 = 0;
return x_419;
}
default:
{
uint8 x_423; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_423 = 0;
return x_423;
}
}
}
case 8:
{
switch (lean::obj_tag(x_2)) {
case 8:
{
obj* x_424; obj* x_426; obj* x_429; obj* x_431; uint8 x_435; 
x_424 = lean::cnstr_get(x_1, 0);
lean::inc(x_424);
x_426 = lean::cnstr_get(x_1, 1);
lean::inc(x_426);
lean::dec(x_1);
x_429 = lean::cnstr_get(x_2, 0);
lean::inc(x_429);
x_431 = lean::cnstr_get(x_2, 1);
lean::inc(x_431);
lean::dec(x_2);
lean::inc(x_0);
x_435 = l_Lean_IR_VarId_alphaEqv(x_0, x_424, x_429);
lean::dec(x_429);
lean::dec(x_424);
if (x_435 == 0)
{
uint8 x_441; 
lean::dec(x_426);
lean::dec(x_431);
lean::dec(x_0);
x_441 = 0;
return x_441;
}
else
{
x_1 = x_426;
x_2 = x_431;
goto _start;
}
}
case 13:
{
uint8 x_445; 
lean::dec(x_1);
lean::dec(x_0);
x_445 = 0;
return x_445;
}
default:
{
uint8 x_449; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_449 = 0;
return x_449;
}
}
}
case 9:
{
switch (lean::obj_tag(x_2)) {
case 9:
{
obj* x_450; obj* x_452; obj* x_455; obj* x_457; uint8 x_460; 
x_450 = lean::cnstr_get(x_1, 0);
lean::inc(x_450);
x_452 = lean::cnstr_get(x_1, 1);
lean::inc(x_452);
lean::dec(x_1);
x_455 = lean::cnstr_get(x_2, 0);
lean::inc(x_455);
x_457 = lean::cnstr_get(x_2, 1);
lean::inc(x_457);
lean::dec(x_2);
x_460 = l_Lean_KVMap_eqv(x_450, x_455);
if (x_460 == 0)
{
uint8 x_464; 
lean::dec(x_0);
lean::dec(x_452);
lean::dec(x_457);
x_464 = 0;
return x_464;
}
else
{
x_1 = x_452;
x_2 = x_457;
goto _start;
}
}
case 13:
{
uint8 x_468; 
lean::dec(x_1);
lean::dec(x_0);
x_468 = 0;
return x_468;
}
default:
{
uint8 x_472; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_472 = 0;
return x_472;
}
}
}
case 10:
{
switch (lean::obj_tag(x_2)) {
case 10:
{
obj* x_473; obj* x_475; obj* x_477; obj* x_480; obj* x_482; obj* x_484; uint8 x_487; 
x_473 = lean::cnstr_get(x_1, 0);
lean::inc(x_473);
x_475 = lean::cnstr_get(x_1, 1);
lean::inc(x_475);
x_477 = lean::cnstr_get(x_1, 2);
lean::inc(x_477);
lean::dec(x_1);
x_480 = lean::cnstr_get(x_2, 0);
lean::inc(x_480);
x_482 = lean::cnstr_get(x_2, 1);
lean::inc(x_482);
x_484 = lean::cnstr_get(x_2, 2);
lean::inc(x_484);
lean::dec(x_2);
x_487 = lean_name_dec_eq(x_473, x_480);
lean::dec(x_480);
lean::dec(x_473);
if (x_487 == 0)
{
uint8 x_495; 
lean::dec(x_482);
lean::dec(x_477);
lean::dec(x_484);
lean::dec(x_475);
lean::dec(x_0);
x_495 = 0;
return x_495;
}
else
{
uint8 x_497; 
lean::inc(x_0);
x_497 = l_Lean_IR_VarId_alphaEqv(x_0, x_475, x_482);
lean::dec(x_482);
lean::dec(x_475);
if (x_497 == 0)
{
uint8 x_503; 
lean::dec(x_477);
lean::dec(x_484);
lean::dec(x_0);
x_503 = 0;
return x_503;
}
else
{
uint8 x_504; 
x_504 = l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(x_0, x_477, x_484);
lean::dec(x_484);
lean::dec(x_477);
return x_504;
}
}
}
case 13:
{
uint8 x_509; 
lean::dec(x_1);
lean::dec(x_0);
x_509 = 0;
return x_509;
}
default:
{
uint8 x_513; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_513 = 0;
return x_513;
}
}
}
case 11:
{
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_514; obj* x_517; uint8 x_520; 
x_514 = lean::cnstr_get(x_1, 0);
lean::inc(x_514);
lean::dec(x_1);
x_517 = lean::cnstr_get(x_2, 0);
lean::inc(x_517);
lean::dec(x_2);
x_520 = l_Lean_IR_Arg_alphaEqv___main(x_0, x_514, x_517);
lean::dec(x_517);
lean::dec(x_514);
return x_520;
}
case 13:
{
uint8 x_525; 
lean::dec(x_1);
lean::dec(x_0);
x_525 = 0;
return x_525;
}
default:
{
uint8 x_529; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_529 = 0;
return x_529;
}
}
}
case 12:
{
switch (lean::obj_tag(x_2)) {
case 12:
{
obj* x_530; obj* x_532; obj* x_535; obj* x_537; uint8 x_540; 
x_530 = lean::cnstr_get(x_1, 0);
lean::inc(x_530);
x_532 = lean::cnstr_get(x_1, 1);
lean::inc(x_532);
lean::dec(x_1);
x_535 = lean::cnstr_get(x_2, 0);
lean::inc(x_535);
x_537 = lean::cnstr_get(x_2, 1);
lean::inc(x_537);
lean::dec(x_2);
x_540 = lean::nat_dec_eq(x_530, x_535);
lean::dec(x_535);
lean::dec(x_530);
if (x_540 == 0)
{
uint8 x_546; 
lean::dec(x_0);
lean::dec(x_532);
lean::dec(x_537);
x_546 = 0;
return x_546;
}
else
{
uint8 x_547; 
x_547 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_0, x_532, x_537);
lean::dec(x_537);
lean::dec(x_532);
return x_547;
}
}
case 13:
{
uint8 x_552; 
lean::dec(x_1);
lean::dec(x_0);
x_552 = 0;
return x_552;
}
default:
{
uint8 x_556; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_556 = 0;
return x_556;
}
}
}
default:
{
lean::dec(x_0);
switch (lean::obj_tag(x_2)) {
case 13:
{
uint8 x_558; 
x_558 = 1;
return x_558;
}
default:
{
uint8 x_560; 
lean::dec(x_2);
x_560 = 0;
return x_560;
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
obj* _init_l_Lean_IR_VarIdSet_Inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* initialize_init_data_array_default(obj*);
obj* initialize_init_lean_name(obj*);
obj* initialize_init_lean_extern(obj*);
obj* initialize_init_lean_kvmap(obj*);
obj* initialize_init_lean_format(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_basic(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_extern(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_kvmap(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_format(w);
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
 l_Lean_IR_Arg_HasBeq = _init_l_Lean_IR_Arg_HasBeq();
lean::mark_persistent(l_Lean_IR_Arg_HasBeq);
 l_Lean_IR_Arg_Inhabited = _init_l_Lean_IR_Arg_Inhabited();
lean::mark_persistent(l_Lean_IR_Arg_Inhabited);
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
 l_Lean_IR_Decl_Inhabited = _init_l_Lean_IR_Decl_Inhabited();
lean::mark_persistent(l_Lean_IR_Decl_Inhabited);
 l_Lean_IR_vsetInh = _init_l_Lean_IR_vsetInh();
lean::mark_persistent(l_Lean_IR_vsetInh);
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
 l_Lean_IR_VarIdSet_Inhabited = _init_l_Lean_IR_VarIdSet_Inhabited();
lean::mark_persistent(l_Lean_IR_VarIdSet_Inhabited);
return w;
}
