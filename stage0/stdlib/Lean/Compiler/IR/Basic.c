// Lean compiler output
// Module: Lean.Compiler.IR.Basic
// Imports: Init Lean.Data.KVMap Lean.Data.Name Lean.Data.Format Lean.Compiler.ExternAttr
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Lean_IR_instAlphaEqvArg___closed__1;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_IR_instAlphaEqvExpr___closed__1;
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_app_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_str_expr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedAlt;
LEAN_EXPORT lean_object* l_Lean_IR_instBEqCtorInfo;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_IR_FnBody_alphaEqv___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_IRType_instBEqIRType___closed__1;
LEAN_EXPORT lean_object* lean_ir_mk_fapp_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instHashableJoinPointId___boxed(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__14;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_IR_FnBody_alphaEqv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instAlphaEqvVarId;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mkParam___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_instReprCtorInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatVarId(lean_object*);
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isScalar___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1123____at_Lean_IR_IRType_beq___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_alt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_instBEqVarId(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__9;
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object*);
static lean_object* l_Lean_IR_instBEqCtorInfo___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_instAlphaEqvExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_IR_addParamsRename___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__12;
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__16;
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_beq___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1123____at_Lean_IR_IRType_beq___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reshapeAux___closed__3;
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__22;
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instAlphaEqvArrayArg;
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isRef___boxed(lean_object*);
lean_object* l_Lean_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_instInhabitedDecl___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedFnBody;
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isIrrelevant___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_jdecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_case(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__15;
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_modifyBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedParam;
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__23;
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_instBEqIRType;
LEAN_EXPORT lean_object* lean_ir_mk_ctor_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isUnion___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LitVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqLitVal;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_modifyJPs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__6;
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__8;
lean_object* l_Lean_RBNode_appendTrees___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isIrrelevant(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Index_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object*);
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__1;
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object*);
LEAN_EXPORT uint64_t l_Lean_IR_instHashableVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedDecl;
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedVarIdSet;
LEAN_EXPORT lean_object* lean_ir_mk_unreachable(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_Decl_updateBody_x21___spec__1(lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__7;
LEAN_EXPORT uint8_t l_Lean_IR_instBEqJoinPointId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_LocalContext_addParams___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__21;
static lean_object* l_Lean_IR_instToStringVarId___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_vdecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object*);
static lean_object* l_Lean_IR_getUnboxOpName___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instInhabitedParam___closed__1;
LEAN_EXPORT uint8_t l_Lean_IR_Arg_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_num_expr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__4;
static lean_object* l_Lean_IR_getUnboxOpName___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__18;
static lean_object* l_Lean_IR_instInhabitedDecl___closed__1;
LEAN_EXPORT lean_object* lean_ir_mk_sset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqFnBody;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedJoinPointId;
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedIRType;
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_modifyJPs___spec__1(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedArg;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedIndexSet;
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_uproj_expr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedVarId;
static lean_object* l_Lean_IR_mkIf___closed__8;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqVarId___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_FnBody_flatten___closed__1;
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__24;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_body___boxed(lean_object*);
static lean_object* l_Lean_IR_instAlphaEqvArrayArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_IR_instHashableJoinPointId(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_papp_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1(lean_object*);
static lean_object* l_Lean_IR_instBEqArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringJoinPointId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_ret(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instHashableVarId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instAlphaEqvArg;
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__3;
static lean_object* l_Lean_IR_instToStringJoinPointId___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instAlphaEqvVarId___closed__1;
static lean_object* l_Lean_IR_reshapeAux___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_instBEqArg;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_mmodifyBody(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object*);
static lean_object* l_Lean_IR_instInhabitedArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getUnboxOpName___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_beq___boxed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__20;
LEAN_EXPORT lean_object* lean_ir_mk_uset(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isStruct___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_var_arg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_reshapeAux___spec__1(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__11;
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__13;
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_proj_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_DeclInfo_sorryDep_x3f___default;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatJoinPointId(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_body(lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__9;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_IR_addVarRename___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reshapeAux___closed__1;
uint8_t l_Lean_RBNode_isBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_IR_args_alphaEqv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_MData_empty;
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__6;
static lean_object* l_panic___at_Lean_IR_reshapeAux___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_Index_lt___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__1;
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__5;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isObj___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_contains(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__17;
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_instInhabitedAlt___closed__1;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_getUnboxOpName___closed__5;
static lean_object* l_Lean_IR_mkIf___closed__5;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_IR_args_alphaEqv___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_sproj_expr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_IR_addParamsRename___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_param(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_mmodifyBody___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_jmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_nil;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringVarId(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_dummy_extern_decl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reshapeAux___closed__2;
LEAN_EXPORT lean_object* lean_ir_mk_extern_decl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_LocalContext_addParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__10;
static lean_object* l_Lean_IR_getUnboxOpName___closed__3;
static lean_object* l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1;
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_IR_VarId_alphaEqv___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__19;
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instBEqFnBody___closed__1;
static lean_object* l_Lean_IR_instBEqLitVal___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_instBEqJoinPointId___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_instInhabitedVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedJoinPointId() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Index_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Index_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Index_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqVarId(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqVarId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_instBEqVarId(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instToStringVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x_", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_IR_instToStringVarId___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_IR_instToStringVarId___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_instHashableVarId(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instHashableVarId___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instHashableVarId(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_instBEqJoinPointId(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqJoinPointId___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_instBEqJoinPointId(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instToStringJoinPointId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("block_", 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringJoinPointId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_IR_instToStringJoinPointId___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatJoinPointId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_IR_instToStringJoinPointId___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_instHashableJoinPointId(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instHashableJoinPointId___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instHashableJoinPointId(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_MData_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedIRType() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1123____at_Lean_IR_IRType_beq___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_name_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_IR_IRType_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_IR_IRType_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
case 9:
{
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1123____at_Lean_IR_IRType_beq___spec__1(x_21, x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_22);
x_28 = lean_array_get_size(x_24);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__2(x_22, x_24, lean_box(0), x_22, x_24, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = 0;
return x_33;
}
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_name_eq(x_34, x_36);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = 0;
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_array_get_size(x_35);
x_41 = lean_array_get_size(x_37);
x_42 = lean_nat_dec_eq(x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = 0;
return x_43;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__3(x_35, x_37, lean_box(0), x_35, x_37, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = 0;
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1123____at_Lean_IR_IRType_beq___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1123____at_Lean_IR_IRType_beq___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at_Lean_IR_IRType_beq___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_IRType_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_IRType_instBEqIRType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_IRType_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_IRType_instBEqIRType() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_IRType_instBEqIRType___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isScalar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 7:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 8:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
case 9:
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
case 10:
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
default: 
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isScalar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isScalar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isObj(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 8:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isObj___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isObj(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isIrrelevant(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isIrrelevant___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isIrrelevant(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isStruct(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isStruct___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isStruct(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isUnion(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isUnion___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isUnion(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedArg___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Arg_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instBEqArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Arg_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instBEqArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instBEqArg___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_var_arg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LitVal_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_string_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LitVal_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instBEqLitVal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_LitVal_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instBEqLitVal() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instBEqLitVal___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("name", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__3;
x_2 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cidx", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("size", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("usize", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ssize", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{ ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__19;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__20;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__19;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" }", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__23;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Name_reprPrec(x_3, x_4);
x_6 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__7;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__6;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__9;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__11;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = l_Nat_repr(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_8);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__13;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
x_32 = l_Nat_repr(x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_8);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_14);
x_39 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__15;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_18);
x_42 = lean_ctor_get(x_1, 3);
lean_inc(x_42);
x_43 = l_Nat_repr(x_42);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__16;
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_8);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_12);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_14);
x_51 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__18;
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_18);
x_54 = lean_ctor_get(x_1, 4);
lean_inc(x_54);
lean_dec(x_1);
x_55 = l_Nat_repr(x_54);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_8);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__22;
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__24;
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__21;
x_65 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_8);
return x_66;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instReprCtorInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instReprCtorInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instReprCtorInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_name_eq(x_3, x_8);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_4, x_9);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_5, x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_6, x_11);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_eq(x_7, x_12);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_CtorInfo_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instBEqCtorInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_CtorInfo_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instBEqCtorInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instBEqCtorInfo___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_nat_dec_lt(x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isRef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_CtorInfo_isRef(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_IR_CtorInfo_isRef(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_CtorInfo_isScalar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_ctor_expr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_proj_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_uproj_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_sproj_expr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_fapp_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_papp_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_app_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_num_expr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_str_expr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedParam___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedParam___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_param(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_ir_mk_param(x_1, x_4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedFnBody() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_FnBody_nil() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(13);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_vdecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_jdecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_uset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_sset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_case(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(7);
x_5 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_ret(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_jmp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_unreachable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(13);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_ctor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedAlt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(13);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedAlt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedAlt___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 10:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 11:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 12:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
case 13:
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
default: 
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_FnBody_isTerminal(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
case 5:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
return x_3;
}
case 6:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
return x_4;
}
case 7:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
return x_5;
}
case 8:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
return x_6;
}
case 9:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
return x_7;
}
case 10:
{
lean_inc(x_1);
return x_1;
}
case 11:
{
lean_inc(x_1);
return x_1;
}
case 12:
{
lean_inc(x_1);
return x_1;
}
case 13:
{
return x_1;
}
default: 
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_2);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 3);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_2);
return x_14;
}
}
case 2:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 3);
lean_dec(x_16);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_20 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_2);
return x_20;
}
}
case 3:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_2);
return x_25;
}
}
case 4:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 3);
lean_dec(x_27);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_31 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_2);
return x_31;
}
}
case 5:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_1, 5);
lean_dec(x_33);
lean_ctor_set(x_1, 5, x_2);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_ctor_get(x_1, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_1);
x_39 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_2);
return x_39;
}
}
case 6:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_1, 2);
lean_dec(x_41);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_1);
x_46 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_2);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_45);
return x_46;
}
}
case 7:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 2);
lean_dec(x_48);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_52 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_53 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_2);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*3 + 1, x_52);
return x_53;
}
}
case 8:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_1);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 1);
lean_dec(x_55);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_2);
return x_57;
}
}
case 9:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_1, 1);
lean_dec(x_59);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_2);
return x_61;
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(13);
x_3 = l_Lean_IR_FnBody_setBody(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_FnBody_body(x_1);
x_3 = lean_box(13);
x_4 = l_Lean_IR_FnBody_setBody(x_1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_body(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_body___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_AltCore_body(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_setBody(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_modifyBody(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Alt_default), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_mmodifyBody___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_IR_Alt_ctor), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_apply_1(x_2, x_5);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_1(x_2, x_12);
x_17 = l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1;
x_18 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_AltCore_mmodifyBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_AltCore_mmodifyBody___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Alt_isDefault(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(13);
x_4 = l_Lean_IR_FnBody_setBody(x_2, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_FnBody_body(x_1);
x_5 = l_Lean_IR_push(x_2, x_1);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
}
}
static lean_object* _init_l_Lean_IR_FnBody_flatten___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_FnBody_flatten___closed__1;
x_3 = l_Lean_IR_flattenAux(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_IR_reshapeAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(13);
x_2 = l_Lean_IR_FnBody_flatten___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_reshapeAux___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_IR_reshapeAux___spec__1___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reshapeAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reshapeAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" out of bounds", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reshapeAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Data.Array.Basic", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reshapeAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Array.swapAt!", 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
lean_inc(x_7);
x_10 = l_Nat_repr(x_7);
x_11 = l_Lean_IR_reshapeAux___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_IR_reshapeAux___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_IR_reshapeAux___closed__3;
x_16 = l_Lean_IR_reshapeAux___closed__4;
x_17 = lean_unsigned_to_nat(99u);
x_18 = lean_unsigned_to_nat(4u);
x_19 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_15, x_16, x_17, x_18, x_14);
lean_dec(x_14);
x_20 = l_panic___at_Lean_IR_reshapeAux___spec__1(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_IR_FnBody_setBody(x_21, x_3);
x_1 = x_22;
x_2 = x_7;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_array_fget(x_1, x_7);
x_26 = lean_box(13);
x_27 = lean_array_fset(x_1, x_7, x_26);
x_28 = l_Lean_IR_FnBody_setBody(x_25, x_3);
x_1 = x_27;
x_2 = x_7;
x_3 = x_28;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l_Lean_IR_reshapeAux(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_modifyJPs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_6, 2, x_13);
x_14 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
x_18 = lean_ctor_get(x_6, 2);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_1);
x_20 = lean_apply_1(x_1, x_18);
x_21 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_19);
x_22 = lean_array_uset(x_8, x_3, x_21);
x_3 = x_10;
x_4 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; 
x_24 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lean_IR_modifyJPs___spec__1(x_2, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_modifyJPs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_modifyJPs___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = lean_array_uset(x_2, x_1, x_6);
x_10 = l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_array_uget(x_5, x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_5, x_4, x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_box_usize(x_4);
x_15 = lean_box_usize(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_1);
lean_closure_set(x_16, 3, x_2);
lean_closure_set(x_16, 4, x_15);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 3);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_apply_1(x_2, x_19);
x_22 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_17);
lean_closure_set(x_22, 2, x_18);
lean_closure_set(x_22, 3, x_20);
lean_inc(x_13);
x_23 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_21, x_22);
x_24 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_23, x_16);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_2(x_26, lean_box(0), x_10);
x_28 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_27, x_16);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg(x_1, x_3, x_5, x_6, x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_mmodifyJPs___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_mmodifyJPs___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_alt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_IR_DeclInfo_sorryDep_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_FnBody_flatten___closed__1;
x_3 = lean_box(0);
x_4 = l_Lean_IR_instInhabitedDecl___closed__1;
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedDecl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedDecl___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Decl_name(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Decl_params(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Decl_resultType(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Decl_isExtern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Decl_getInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_IR_Decl_updateBody_x21___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedDecl;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.IR.Basic", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.IR.Decl.updateBody!", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected definition", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Decl_updateBody_x21___closed__1;
x_2 = l_Lean_IR_Decl_updateBody_x21___closed__2;
x_3 = lean_unsigned_to_nat(429u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_IR_Decl_updateBody_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_2);
lean_ctor_set(x_9, 4, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lean_IR_Decl_updateBody_x21___closed__4;
x_11 = l_panic___at_Lean_IR_Decl_updateBody_x21___spec__1(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lean_ir_mk_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_extern_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lean_ir_mk_dummy_extern_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = lean_box(13);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set(x_6, 4, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedIndexSet() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_nat_dec_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_2, x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_12, x_2, x_3);
x_16 = 0;
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_nat_dec_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_2, x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_23, x_2, x_3);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_21);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_nat_dec_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_nat_dec_eq(x_2, x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_38, x_2, x_3);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_41, 3);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_41, 3);
lean_dec(x_46);
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
lean_ctor_set(x_41, 0, x_44);
x_48 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_42);
x_52 = 1;
lean_ctor_set(x_1, 3, x_51);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
}
else
{
uint8_t x_53; 
x_53 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_41, 1);
x_56 = lean_ctor_get(x_41, 2);
x_57 = lean_ctor_get(x_41, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_41, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
x_62 = lean_ctor_get(x_44, 2);
x_63 = lean_ctor_get(x_44, 3);
x_64 = 1;
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_64);
lean_ctor_set(x_41, 3, x_63);
lean_ctor_set(x_41, 2, x_62);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_60);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_64);
x_65 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
return x_1;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; 
x_66 = lean_ctor_get(x_44, 0);
x_67 = lean_ctor_get(x_44, 1);
x_68 = lean_ctor_get(x_44, 2);
x_69 = lean_ctor_get(x_44, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_44);
x_70 = 1;
x_71 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_71, 0, x_35);
lean_ctor_set(x_71, 1, x_36);
lean_ctor_set(x_71, 2, x_37);
lean_ctor_set(x_71, 3, x_43);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_70);
lean_ctor_set(x_41, 3, x_69);
lean_ctor_set(x_41, 2, x_68);
lean_ctor_set(x_41, 1, x_67);
lean_ctor_set(x_41, 0, x_66);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_70);
x_72 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_71);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_72);
return x_1;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_73 = lean_ctor_get(x_41, 1);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_41);
x_75 = lean_ctor_get(x_44, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_44, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_44, 3);
lean_inc(x_78);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_79 = x_44;
} else {
 lean_dec_ref(x_44);
 x_79 = lean_box(0);
}
x_80 = 1;
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(1, 4, 1);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_35);
lean_ctor_set(x_81, 1, x_36);
lean_ctor_set(x_81, 2, x_37);
lean_ctor_set(x_81, 3, x_43);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_80);
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_80);
x_83 = 0;
lean_ctor_set(x_1, 3, x_82);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_81);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_83);
return x_1;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_1);
x_84 = !lean_is_exclusive(x_44);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_44, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_44, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_44, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_44, 0);
lean_dec(x_88);
x_89 = 1;
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_89);
return x_44;
}
else
{
uint8_t x_90; lean_object* x_91; 
lean_dec(x_44);
x_90 = 1;
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_35);
lean_ctor_set(x_91, 1, x_36);
lean_ctor_set(x_91, 2, x_37);
lean_ctor_set(x_91, 3, x_41);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_41);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_41, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_43);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_43, 0);
x_97 = lean_ctor_get(x_43, 1);
x_98 = lean_ctor_get(x_43, 2);
x_99 = lean_ctor_get(x_43, 3);
x_100 = 1;
lean_ctor_set(x_43, 3, x_96);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_100);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_100);
x_101 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_101);
return x_1;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; 
x_102 = lean_ctor_get(x_43, 0);
x_103 = lean_ctor_get(x_43, 1);
x_104 = lean_ctor_get(x_43, 2);
x_105 = lean_ctor_get(x_43, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_43);
x_106 = 1;
x_107 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_107, 0, x_35);
lean_ctor_set(x_107, 1, x_36);
lean_ctor_set(x_107, 2, x_37);
lean_ctor_set(x_107, 3, x_102);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_106);
lean_ctor_set(x_41, 0, x_105);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_106);
x_108 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_107);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_109 = lean_ctor_get(x_41, 1);
x_110 = lean_ctor_get(x_41, 2);
x_111 = lean_ctor_get(x_41, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_41);
x_112 = lean_ctor_get(x_43, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_43, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_43, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_43, 3);
lean_inc(x_115);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_116 = x_43;
} else {
 lean_dec_ref(x_43);
 x_116 = lean_box(0);
}
x_117 = 1;
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(1, 4, 1);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_35);
lean_ctor_set(x_118, 1, x_36);
lean_ctor_set(x_118, 2, x_37);
lean_ctor_set(x_118, 3, x_112);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_117);
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_109);
lean_ctor_set(x_119, 2, x_110);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_117);
x_120 = 0;
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set(x_1, 2, x_114);
lean_ctor_set(x_1, 1, x_113);
lean_ctor_set(x_1, 0, x_118);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_41, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_free_object(x_1);
x_122 = !lean_is_exclusive(x_43);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_43, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_43, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_43, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_43, 0);
lean_dec(x_126);
x_127 = 1;
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
else
{
uint8_t x_128; lean_object* x_129; 
lean_dec(x_43);
x_128 = 1;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_35);
lean_ctor_set(x_129, 1, x_36);
lean_ctor_set(x_129, 2, x_37);
lean_ctor_set(x_129, 3, x_41);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_41);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_41, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_41, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
x_139 = 1;
lean_inc(x_43);
lean_ctor_set(x_121, 3, x_43);
lean_ctor_set(x_121, 2, x_37);
lean_ctor_set(x_121, 1, x_36);
lean_ctor_set(x_121, 0, x_35);
x_140 = !lean_is_exclusive(x_43);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_141 = lean_ctor_get(x_43, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_43, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_43, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_43, 0);
lean_dec(x_144);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_139);
lean_ctor_set(x_43, 3, x_138);
lean_ctor_set(x_43, 2, x_137);
lean_ctor_set(x_43, 1, x_136);
lean_ctor_set(x_43, 0, x_135);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_139);
x_145 = 0;
lean_ctor_set(x_41, 3, x_43);
lean_ctor_set(x_41, 0, x_121);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_145);
return x_41;
}
else
{
lean_object* x_146; uint8_t x_147; 
lean_dec(x_43);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_139);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_136);
lean_ctor_set(x_146, 2, x_137);
lean_ctor_set(x_146, 3, x_138);
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_139);
x_147 = 0;
lean_ctor_set(x_41, 3, x_146);
lean_ctor_set(x_41, 0, x_121);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_147);
return x_41;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_148 = lean_ctor_get(x_121, 0);
x_149 = lean_ctor_get(x_121, 1);
x_150 = lean_ctor_get(x_121, 2);
x_151 = lean_ctor_get(x_121, 3);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_121);
x_152 = 1;
lean_inc(x_43);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_35);
lean_ctor_set(x_153, 1, x_36);
lean_ctor_set(x_153, 2, x_37);
lean_ctor_set(x_153, 3, x_43);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_154 = x_43;
} else {
 lean_dec_ref(x_43);
 x_154 = lean_box(0);
}
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_152);
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 4, 1);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_148);
lean_ctor_set(x_155, 1, x_149);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_151);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_152);
x_156 = 0;
lean_ctor_set(x_41, 3, x_155);
lean_ctor_set(x_41, 0, x_153);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_156);
return x_41;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; 
x_157 = lean_ctor_get(x_41, 1);
x_158 = lean_ctor_get(x_41, 2);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_41);
x_159 = lean_ctor_get(x_121, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_121, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_121, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_121, 3);
lean_inc(x_162);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_163 = x_121;
} else {
 lean_dec_ref(x_121);
 x_163 = lean_box(0);
}
x_164 = 1;
lean_inc(x_43);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_35);
lean_ctor_set(x_165, 1, x_36);
lean_ctor_set(x_165, 2, x_37);
lean_ctor_set(x_165, 3, x_43);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_166 = x_43;
} else {
 lean_dec_ref(x_43);
 x_166 = lean_box(0);
}
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_164);
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 4, 1);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set(x_167, 3, x_162);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_164);
x_168 = 0;
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_157);
lean_ctor_set(x_169, 2, x_158);
lean_ctor_set(x_169, 3, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_168);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_41);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_41, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_41, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_43);
if (x_173 == 0)
{
uint8_t x_174; 
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_130);
x_174 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_174);
return x_1;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_43, 0);
x_176 = lean_ctor_get(x_43, 1);
x_177 = lean_ctor_get(x_43, 2);
x_178 = lean_ctor_get(x_43, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_43);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_130);
lean_ctor_set(x_41, 0, x_179);
x_180 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_180);
return x_1;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_181 = lean_ctor_get(x_41, 1);
x_182 = lean_ctor_get(x_41, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_41);
x_183 = lean_ctor_get(x_43, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_43, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_43, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_43, 3);
lean_inc(x_186);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_187 = x_43;
} else {
 lean_dec_ref(x_43);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 4, 1);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_130);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_181);
lean_ctor_set(x_189, 2, x_182);
lean_ctor_set(x_189, 3, x_121);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_42);
x_190 = 1;
lean_ctor_set(x_1, 3, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_191; 
x_191 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
uint8_t x_192; 
lean_dec(x_37);
lean_dec(x_36);
x_192 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_192);
return x_1;
}
}
else
{
lean_object* x_193; uint8_t x_194; 
x_193 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_35, x_2, x_3);
x_194 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_193, 3);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_193);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_ctor_get(x_193, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_193, 0);
lean_dec(x_199);
lean_ctor_set(x_193, 0, x_196);
x_200 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_193, 1);
x_202 = lean_ctor_get(x_193, 2);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_193);
x_203 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_201);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_196);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_194);
x_204 = 1;
lean_ctor_set(x_1, 0, x_203);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_204);
return x_1;
}
}
else
{
uint8_t x_205; 
x_205 = lean_ctor_get_uint8(x_196, sizeof(void*)*4);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_193);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_193, 1);
x_208 = lean_ctor_get(x_193, 2);
x_209 = lean_ctor_get(x_193, 3);
lean_dec(x_209);
x_210 = lean_ctor_get(x_193, 0);
lean_dec(x_210);
x_211 = !lean_is_exclusive(x_196);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; 
x_212 = lean_ctor_get(x_196, 0);
x_213 = lean_ctor_get(x_196, 1);
x_214 = lean_ctor_get(x_196, 2);
x_215 = lean_ctor_get(x_196, 3);
x_216 = 1;
lean_ctor_set(x_196, 3, x_212);
lean_ctor_set(x_196, 2, x_208);
lean_ctor_set(x_196, 1, x_207);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_216);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_215);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_216);
x_217 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_214);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_1, 0, x_196);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_217);
return x_1;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; uint8_t x_224; 
x_218 = lean_ctor_get(x_196, 0);
x_219 = lean_ctor_get(x_196, 1);
x_220 = lean_ctor_get(x_196, 2);
x_221 = lean_ctor_get(x_196, 3);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_196);
x_222 = 1;
x_223 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_223, 0, x_195);
lean_ctor_set(x_223, 1, x_207);
lean_ctor_set(x_223, 2, x_208);
lean_ctor_set(x_223, 3, x_218);
lean_ctor_set_uint8(x_223, sizeof(void*)*4, x_222);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_221);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_222);
x_224 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_223);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_224);
return x_1;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_225 = lean_ctor_get(x_193, 1);
x_226 = lean_ctor_get(x_193, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_193);
x_227 = lean_ctor_get(x_196, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_196, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_196, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_196, 3);
lean_inc(x_230);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 x_231 = x_196;
} else {
 lean_dec_ref(x_196);
 x_231 = lean_box(0);
}
x_232 = 1;
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 4, 1);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_195);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_226);
lean_ctor_set(x_233, 3, x_227);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_36);
lean_ctor_set(x_234, 2, x_37);
lean_ctor_set(x_234, 3, x_38);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_232);
x_235 = 0;
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_229);
lean_ctor_set(x_1, 1, x_228);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8_t x_236; 
lean_free_object(x_1);
x_236 = !lean_is_exclusive(x_196);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_196, 3);
lean_dec(x_237);
x_238 = lean_ctor_get(x_196, 2);
lean_dec(x_238);
x_239 = lean_ctor_get(x_196, 1);
lean_dec(x_239);
x_240 = lean_ctor_get(x_196, 0);
lean_dec(x_240);
x_241 = 1;
lean_ctor_set(x_196, 3, x_38);
lean_ctor_set(x_196, 2, x_37);
lean_ctor_set(x_196, 1, x_36);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_241);
return x_196;
}
else
{
uint8_t x_242; lean_object* x_243; 
lean_dec(x_196);
x_242 = 1;
x_243 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_243, 0, x_193);
lean_ctor_set(x_243, 1, x_36);
lean_ctor_set(x_243, 2, x_37);
lean_ctor_set(x_243, 3, x_38);
lean_ctor_set_uint8(x_243, sizeof(void*)*4, x_242);
return x_243;
}
}
}
}
else
{
uint8_t x_244; 
x_244 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_246 = lean_ctor_get(x_193, 1);
x_247 = lean_ctor_get(x_193, 2);
x_248 = lean_ctor_get(x_193, 3);
x_249 = lean_ctor_get(x_193, 0);
lean_dec(x_249);
x_250 = !lean_is_exclusive(x_195);
if (x_250 == 0)
{
uint8_t x_251; uint8_t x_252; 
x_251 = 1;
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_251);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_248);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_251);
x_252 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_246);
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_253 = lean_ctor_get(x_195, 0);
x_254 = lean_ctor_get(x_195, 1);
x_255 = lean_ctor_get(x_195, 2);
x_256 = lean_ctor_get(x_195, 3);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_195);
x_257 = 1;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_253);
lean_ctor_set(x_258, 1, x_254);
lean_ctor_set(x_258, 2, x_255);
lean_ctor_set(x_258, 3, x_256);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_248);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_257);
x_259 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_246);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_260 = lean_ctor_get(x_193, 1);
x_261 = lean_ctor_get(x_193, 2);
x_262 = lean_ctor_get(x_193, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_193);
x_263 = lean_ctor_get(x_195, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_195, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_195, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_195, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_267 = x_195;
} else {
 lean_dec_ref(x_195);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_264);
lean_ctor_set(x_269, 2, x_265);
lean_ctor_set(x_269, 3, x_266);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_36);
lean_ctor_set(x_270, 2, x_37);
lean_ctor_set(x_270, 3, x_38);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
x_271 = 0;
lean_ctor_set(x_1, 3, x_270);
lean_ctor_set(x_1, 2, x_261);
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_271);
return x_1;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_193, 3);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
lean_free_object(x_1);
x_273 = !lean_is_exclusive(x_195);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_195, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_195, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_195, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_195, 0);
lean_dec(x_277);
x_278 = 1;
lean_ctor_set(x_195, 3, x_38);
lean_ctor_set(x_195, 2, x_37);
lean_ctor_set(x_195, 1, x_36);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_278);
return x_195;
}
else
{
uint8_t x_279; lean_object* x_280; 
lean_dec(x_195);
x_279 = 1;
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_193);
lean_ctor_set(x_280, 1, x_36);
lean_ctor_set(x_280, 2, x_37);
lean_ctor_set(x_280, 3, x_38);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_279);
return x_280;
}
}
else
{
uint8_t x_281; 
x_281 = lean_ctor_get_uint8(x_272, sizeof(void*)*4);
if (x_281 == 0)
{
uint8_t x_282; 
lean_free_object(x_1);
x_282 = !lean_is_exclusive(x_193);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_283 = lean_ctor_get(x_193, 1);
x_284 = lean_ctor_get(x_193, 2);
x_285 = lean_ctor_get(x_193, 3);
lean_dec(x_285);
x_286 = lean_ctor_get(x_193, 0);
lean_dec(x_286);
x_287 = !lean_is_exclusive(x_272);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_288 = lean_ctor_get(x_272, 0);
x_289 = lean_ctor_get(x_272, 1);
x_290 = lean_ctor_get(x_272, 2);
x_291 = lean_ctor_get(x_272, 3);
x_292 = 1;
lean_inc(x_195);
lean_ctor_set(x_272, 3, x_288);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_283);
lean_ctor_set(x_272, 0, x_195);
x_293 = !lean_is_exclusive(x_195);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_195, 3);
lean_dec(x_294);
x_295 = lean_ctor_get(x_195, 2);
lean_dec(x_295);
x_296 = lean_ctor_get(x_195, 1);
lean_dec(x_296);
x_297 = lean_ctor_get(x_195, 0);
lean_dec(x_297);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_292);
lean_ctor_set(x_195, 3, x_38);
lean_ctor_set(x_195, 2, x_37);
lean_ctor_set(x_195, 1, x_36);
lean_ctor_set(x_195, 0, x_291);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_292);
x_298 = 0;
lean_ctor_set(x_193, 3, x_195);
lean_ctor_set(x_193, 2, x_290);
lean_ctor_set(x_193, 1, x_289);
lean_ctor_set(x_193, 0, x_272);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_298);
return x_193;
}
else
{
lean_object* x_299; uint8_t x_300; 
lean_dec(x_195);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_292);
x_299 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_299, 0, x_291);
lean_ctor_set(x_299, 1, x_36);
lean_ctor_set(x_299, 2, x_37);
lean_ctor_set(x_299, 3, x_38);
lean_ctor_set_uint8(x_299, sizeof(void*)*4, x_292);
x_300 = 0;
lean_ctor_set(x_193, 3, x_299);
lean_ctor_set(x_193, 2, x_290);
lean_ctor_set(x_193, 1, x_289);
lean_ctor_set(x_193, 0, x_272);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_300);
return x_193;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_301 = lean_ctor_get(x_272, 0);
x_302 = lean_ctor_get(x_272, 1);
x_303 = lean_ctor_get(x_272, 2);
x_304 = lean_ctor_get(x_272, 3);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_272);
x_305 = 1;
lean_inc(x_195);
x_306 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_306, 0, x_195);
lean_ctor_set(x_306, 1, x_283);
lean_ctor_set(x_306, 2, x_284);
lean_ctor_set(x_306, 3, x_301);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_307 = x_195;
} else {
 lean_dec_ref(x_195);
 x_307 = lean_box(0);
}
lean_ctor_set_uint8(x_306, sizeof(void*)*4, x_305);
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 4, 1);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_36);
lean_ctor_set(x_308, 2, x_37);
lean_ctor_set(x_308, 3, x_38);
lean_ctor_set_uint8(x_308, sizeof(void*)*4, x_305);
x_309 = 0;
lean_ctor_set(x_193, 3, x_308);
lean_ctor_set(x_193, 2, x_303);
lean_ctor_set(x_193, 1, x_302);
lean_ctor_set(x_193, 0, x_306);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_309);
return x_193;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
x_310 = lean_ctor_get(x_193, 1);
x_311 = lean_ctor_get(x_193, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_193);
x_312 = lean_ctor_get(x_272, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_272, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_272, 2);
lean_inc(x_314);
x_315 = lean_ctor_get(x_272, 3);
lean_inc(x_315);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_316 = x_272;
} else {
 lean_dec_ref(x_272);
 x_316 = lean_box(0);
}
x_317 = 1;
lean_inc(x_195);
if (lean_is_scalar(x_316)) {
 x_318 = lean_alloc_ctor(1, 4, 1);
} else {
 x_318 = x_316;
}
lean_ctor_set(x_318, 0, x_195);
lean_ctor_set(x_318, 1, x_310);
lean_ctor_set(x_318, 2, x_311);
lean_ctor_set(x_318, 3, x_312);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_319 = x_195;
} else {
 lean_dec_ref(x_195);
 x_319 = lean_box(0);
}
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_317);
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 4, 1);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_36);
lean_ctor_set(x_320, 2, x_37);
lean_ctor_set(x_320, 3, x_38);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_317);
x_321 = 0;
x_322 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_322, 0, x_318);
lean_ctor_set(x_322, 1, x_313);
lean_ctor_set(x_322, 2, x_314);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_321);
return x_322;
}
}
else
{
uint8_t x_323; 
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_324 = lean_ctor_get(x_193, 3);
lean_dec(x_324);
x_325 = lean_ctor_get(x_193, 0);
lean_dec(x_325);
x_326 = !lean_is_exclusive(x_195);
if (x_326 == 0)
{
uint8_t x_327; 
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_281);
x_327 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_327);
return x_1;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_328 = lean_ctor_get(x_195, 0);
x_329 = lean_ctor_get(x_195, 1);
x_330 = lean_ctor_get(x_195, 2);
x_331 = lean_ctor_get(x_195, 3);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_195);
x_332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_332, 0, x_328);
lean_ctor_set(x_332, 1, x_329);
lean_ctor_set(x_332, 2, x_330);
lean_ctor_set(x_332, 3, x_331);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_281);
lean_ctor_set(x_193, 0, x_332);
x_333 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_333);
return x_1;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_334 = lean_ctor_get(x_193, 1);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_193);
x_336 = lean_ctor_get(x_195, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_195, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_195, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_195, 3);
lean_inc(x_339);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_340 = x_195;
} else {
 lean_dec_ref(x_195);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 4, 1);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_336);
lean_ctor_set(x_341, 1, x_337);
lean_ctor_set(x_341, 2, x_338);
lean_ctor_set(x_341, 3, x_339);
lean_ctor_set_uint8(x_341, sizeof(void*)*4, x_281);
x_342 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_334);
lean_ctor_set(x_342, 2, x_335);
lean_ctor_set(x_342, 3, x_272);
lean_ctor_set_uint8(x_342, sizeof(void*)*4, x_194);
x_343 = 1;
lean_ctor_set(x_1, 0, x_342);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_344; 
x_344 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_344);
return x_1;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_345 = lean_ctor_get(x_1, 0);
x_346 = lean_ctor_get(x_1, 1);
x_347 = lean_ctor_get(x_1, 2);
x_348 = lean_ctor_get(x_1, 3);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_1);
x_349 = lean_nat_dec_lt(x_2, x_346);
if (x_349 == 0)
{
uint8_t x_350; 
x_350 = lean_nat_dec_eq(x_2, x_346);
if (x_350 == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_348, x_2, x_3);
x_352 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_351, 3);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; 
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_351, 2);
lean_inc(x_356);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_357 = x_351;
} else {
 lean_dec_ref(x_351);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_354);
lean_ctor_set(x_358, 1, x_355);
lean_ctor_set(x_358, 2, x_356);
lean_ctor_set(x_358, 3, x_354);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_352);
x_359 = 1;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_345);
lean_ctor_set(x_360, 1, x_346);
lean_ctor_set(x_360, 2, x_347);
lean_ctor_set(x_360, 3, x_358);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
return x_360;
}
else
{
uint8_t x_361; 
x_361 = lean_ctor_get_uint8(x_354, sizeof(void*)*4);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_362 = lean_ctor_get(x_351, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_351, 2);
lean_inc(x_363);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_364 = x_351;
} else {
 lean_dec_ref(x_351);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_354, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_354, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_354, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_354, 3);
lean_inc(x_368);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_369 = x_354;
} else {
 lean_dec_ref(x_354);
 x_369 = lean_box(0);
}
x_370 = 1;
if (lean_is_scalar(x_369)) {
 x_371 = lean_alloc_ctor(1, 4, 1);
} else {
 x_371 = x_369;
}
lean_ctor_set(x_371, 0, x_345);
lean_ctor_set(x_371, 1, x_346);
lean_ctor_set(x_371, 2, x_347);
lean_ctor_set(x_371, 3, x_353);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_370);
if (lean_is_scalar(x_364)) {
 x_372 = lean_alloc_ctor(1, 4, 1);
} else {
 x_372 = x_364;
}
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_366);
lean_ctor_set(x_372, 2, x_367);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_370);
x_373 = 0;
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_362);
lean_ctor_set(x_374, 2, x_363);
lean_ctor_set(x_374, 3, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
else
{
lean_object* x_375; uint8_t x_376; lean_object* x_377; 
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_375 = x_354;
} else {
 lean_dec_ref(x_354);
 x_375 = lean_box(0);
}
x_376 = 1;
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_345);
lean_ctor_set(x_377, 1, x_346);
lean_ctor_set(x_377, 2, x_347);
lean_ctor_set(x_377, 3, x_351);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_376);
return x_377;
}
}
}
else
{
uint8_t x_378; 
x_378 = lean_ctor_get_uint8(x_353, sizeof(void*)*4);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; 
x_379 = lean_ctor_get(x_351, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_351, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_351, 3);
lean_inc(x_381);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_382 = x_351;
} else {
 lean_dec_ref(x_351);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_353, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_353, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_353, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_353, 3);
lean_inc(x_386);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_387 = x_353;
} else {
 lean_dec_ref(x_353);
 x_387 = lean_box(0);
}
x_388 = 1;
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_345);
lean_ctor_set(x_389, 1, x_346);
lean_ctor_set(x_389, 2, x_347);
lean_ctor_set(x_389, 3, x_383);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(1, 4, 1);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_379);
lean_ctor_set(x_390, 2, x_380);
lean_ctor_set(x_390, 3, x_381);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_388);
x_391 = 0;
x_392 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_384);
lean_ctor_set(x_392, 2, x_385);
lean_ctor_set(x_392, 3, x_390);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_351, 3);
lean_inc(x_393);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; uint8_t x_395; lean_object* x_396; 
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_394 = x_353;
} else {
 lean_dec_ref(x_353);
 x_394 = lean_box(0);
}
x_395 = 1;
if (lean_is_scalar(x_394)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_394;
}
lean_ctor_set(x_396, 0, x_345);
lean_ctor_set(x_396, 1, x_346);
lean_ctor_set(x_396, 2, x_347);
lean_ctor_set(x_396, 3, x_351);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_395);
return x_396;
}
else
{
uint8_t x_397; 
x_397 = lean_ctor_get_uint8(x_393, sizeof(void*)*4);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; 
x_398 = lean_ctor_get(x_351, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_351, 2);
lean_inc(x_399);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_400 = x_351;
} else {
 lean_dec_ref(x_351);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_393, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_393, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_393, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_393, 3);
lean_inc(x_404);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 lean_ctor_release(x_393, 2);
 lean_ctor_release(x_393, 3);
 x_405 = x_393;
} else {
 lean_dec_ref(x_393);
 x_405 = lean_box(0);
}
x_406 = 1;
lean_inc(x_353);
if (lean_is_scalar(x_405)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_405;
}
lean_ctor_set(x_407, 0, x_345);
lean_ctor_set(x_407, 1, x_346);
lean_ctor_set(x_407, 2, x_347);
lean_ctor_set(x_407, 3, x_353);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_408 = x_353;
} else {
 lean_dec_ref(x_353);
 x_408 = lean_box(0);
}
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_401);
lean_ctor_set(x_409, 1, x_402);
lean_ctor_set(x_409, 2, x_403);
lean_ctor_set(x_409, 3, x_404);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_406);
x_410 = 0;
if (lean_is_scalar(x_400)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_400;
}
lean_ctor_set(x_411, 0, x_407);
lean_ctor_set(x_411, 1, x_398);
lean_ctor_set(x_411, 2, x_399);
lean_ctor_set(x_411, 3, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_410);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; 
x_412 = lean_ctor_get(x_351, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_351, 2);
lean_inc(x_413);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_414 = x_351;
} else {
 lean_dec_ref(x_351);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_353, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_353, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_353, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_353, 3);
lean_inc(x_418);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_419 = x_353;
} else {
 lean_dec_ref(x_353);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_415);
lean_ctor_set(x_420, 1, x_416);
lean_ctor_set(x_420, 2, x_417);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_397);
if (lean_is_scalar(x_414)) {
 x_421 = lean_alloc_ctor(1, 4, 1);
} else {
 x_421 = x_414;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_412);
lean_ctor_set(x_421, 2, x_413);
lean_ctor_set(x_421, 3, x_393);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_352);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_345);
lean_ctor_set(x_423, 1, x_346);
lean_ctor_set(x_423, 2, x_347);
lean_ctor_set(x_423, 3, x_421);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
}
}
}
}
else
{
uint8_t x_424; lean_object* x_425; 
x_424 = 1;
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_345);
lean_ctor_set(x_425, 1, x_346);
lean_ctor_set(x_425, 2, x_347);
lean_ctor_set(x_425, 3, x_351);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_424);
return x_425;
}
}
else
{
uint8_t x_426; lean_object* x_427; 
lean_dec(x_347);
lean_dec(x_346);
x_426 = 1;
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_345);
lean_ctor_set(x_427, 1, x_2);
lean_ctor_set(x_427, 2, x_3);
lean_ctor_set(x_427, 3, x_348);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_426);
return x_427;
}
}
else
{
lean_object* x_428; uint8_t x_429; 
x_428 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_345, x_2, x_3);
x_429 = lean_ctor_get_uint8(x_428, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_428, 3);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_428, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_434 = x_428;
} else {
 lean_dec_ref(x_428);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_431);
lean_ctor_set(x_435, 1, x_432);
lean_ctor_set(x_435, 2, x_433);
lean_ctor_set(x_435, 3, x_431);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_429);
x_436 = 1;
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_346);
lean_ctor_set(x_437, 2, x_347);
lean_ctor_set(x_437, 3, x_348);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_436);
return x_437;
}
else
{
uint8_t x_438; 
x_438 = lean_ctor_get_uint8(x_431, sizeof(void*)*4);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; 
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_441 = x_428;
} else {
 lean_dec_ref(x_428);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_431, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_431, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_431, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_431, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_446 = x_431;
} else {
 lean_dec_ref(x_431);
 x_446 = lean_box(0);
}
x_447 = 1;
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_430);
lean_ctor_set(x_448, 1, x_439);
lean_ctor_set(x_448, 2, x_440);
lean_ctor_set(x_448, 3, x_442);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(1, 4, 1);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_346);
lean_ctor_set(x_449, 2, x_347);
lean_ctor_set(x_449, 3, x_348);
lean_ctor_set_uint8(x_449, sizeof(void*)*4, x_447);
x_450 = 0;
x_451 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_443);
lean_ctor_set(x_451, 2, x_444);
lean_ctor_set(x_451, 3, x_449);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
return x_451;
}
else
{
lean_object* x_452; uint8_t x_453; lean_object* x_454; 
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_452 = x_431;
} else {
 lean_dec_ref(x_431);
 x_452 = lean_box(0);
}
x_453 = 1;
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_428);
lean_ctor_set(x_454, 1, x_346);
lean_ctor_set(x_454, 2, x_347);
lean_ctor_set(x_454, 3, x_348);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
}
}
else
{
uint8_t x_455; 
x_455 = lean_ctor_get_uint8(x_430, sizeof(void*)*4);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; 
x_456 = lean_ctor_get(x_428, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_428, 2);
lean_inc(x_457);
x_458 = lean_ctor_get(x_428, 3);
lean_inc(x_458);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_459 = x_428;
} else {
 lean_dec_ref(x_428);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_430, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_430, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_430, 2);
lean_inc(x_462);
x_463 = lean_ctor_get(x_430, 3);
lean_inc(x_463);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_464 = x_430;
} else {
 lean_dec_ref(x_430);
 x_464 = lean_box(0);
}
x_465 = 1;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_460);
lean_ctor_set(x_466, 1, x_461);
lean_ctor_set(x_466, 2, x_462);
lean_ctor_set(x_466, 3, x_463);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
if (lean_is_scalar(x_459)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_459;
}
lean_ctor_set(x_467, 0, x_458);
lean_ctor_set(x_467, 1, x_346);
lean_ctor_set(x_467, 2, x_347);
lean_ctor_set(x_467, 3, x_348);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_465);
x_468 = 0;
x_469 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_456);
lean_ctor_set(x_469, 2, x_457);
lean_ctor_set(x_469, 3, x_467);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_428, 3);
lean_inc(x_470);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; uint8_t x_472; lean_object* x_473; 
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_471 = x_430;
} else {
 lean_dec_ref(x_430);
 x_471 = lean_box(0);
}
x_472 = 1;
if (lean_is_scalar(x_471)) {
 x_473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_473 = x_471;
}
lean_ctor_set(x_473, 0, x_428);
lean_ctor_set(x_473, 1, x_346);
lean_ctor_set(x_473, 2, x_347);
lean_ctor_set(x_473, 3, x_348);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_472);
return x_473;
}
else
{
uint8_t x_474; 
x_474 = lean_ctor_get_uint8(x_470, sizeof(void*)*4);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; 
x_475 = lean_ctor_get(x_428, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_428, 2);
lean_inc(x_476);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_477 = x_428;
} else {
 lean_dec_ref(x_428);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_470, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_470, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_470, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_470, 3);
lean_inc(x_481);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 lean_ctor_release(x_470, 2);
 lean_ctor_release(x_470, 3);
 x_482 = x_470;
} else {
 lean_dec_ref(x_470);
 x_482 = lean_box(0);
}
x_483 = 1;
lean_inc(x_430);
if (lean_is_scalar(x_482)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_482;
}
lean_ctor_set(x_484, 0, x_430);
lean_ctor_set(x_484, 1, x_475);
lean_ctor_set(x_484, 2, x_476);
lean_ctor_set(x_484, 3, x_478);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_485 = x_430;
} else {
 lean_dec_ref(x_430);
 x_485 = lean_box(0);
}
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 4, 1);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_346);
lean_ctor_set(x_486, 2, x_347);
lean_ctor_set(x_486, 3, x_348);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_483);
x_487 = 0;
if (lean_is_scalar(x_477)) {
 x_488 = lean_alloc_ctor(1, 4, 1);
} else {
 x_488 = x_477;
}
lean_ctor_set(x_488, 0, x_484);
lean_ctor_set(x_488, 1, x_479);
lean_ctor_set(x_488, 2, x_480);
lean_ctor_set(x_488, 3, x_486);
lean_ctor_set_uint8(x_488, sizeof(void*)*4, x_487);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; lean_object* x_500; 
x_489 = lean_ctor_get(x_428, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_428, 2);
lean_inc(x_490);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_491 = x_428;
} else {
 lean_dec_ref(x_428);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_430, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_430, 1);
lean_inc(x_493);
x_494 = lean_ctor_get(x_430, 2);
lean_inc(x_494);
x_495 = lean_ctor_get(x_430, 3);
lean_inc(x_495);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_496 = x_430;
} else {
 lean_dec_ref(x_430);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 4, 1);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_492);
lean_ctor_set(x_497, 1, x_493);
lean_ctor_set(x_497, 2, x_494);
lean_ctor_set(x_497, 3, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_474);
if (lean_is_scalar(x_491)) {
 x_498 = lean_alloc_ctor(1, 4, 1);
} else {
 x_498 = x_491;
}
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_489);
lean_ctor_set(x_498, 2, x_490);
lean_ctor_set(x_498, 3, x_470);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_429);
x_499 = 1;
x_500 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_346);
lean_ctor_set(x_500, 2, x_347);
lean_ctor_set(x_500, 3, x_348);
lean_ctor_set_uint8(x_500, sizeof(void*)*4, x_499);
return x_500;
}
}
}
}
}
else
{
uint8_t x_501; lean_object* x_502; 
x_501 = 1;
x_502 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_502, 0, x_428);
lean_ctor_set(x_502, 1, x_346);
lean_ctor_set(x_502, 2, x_347);
lean_ctor_set(x_502, 3, x_348);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_501);
return x_502;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_IR_mkIndexSet___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_nat_dec_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_2, x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_12, x_2, x_3);
x_16 = 0;
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_nat_dec_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_2, x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_23, x_2, x_3);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_21);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_nat_dec_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_nat_dec_eq(x_2, x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_38, x_2, x_3);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_41, 3);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_41, 3);
lean_dec(x_46);
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
lean_ctor_set(x_41, 0, x_44);
x_48 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_42);
x_52 = 1;
lean_ctor_set(x_1, 3, x_51);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
}
else
{
uint8_t x_53; 
x_53 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_41, 1);
x_56 = lean_ctor_get(x_41, 2);
x_57 = lean_ctor_get(x_41, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_41, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
x_62 = lean_ctor_get(x_44, 2);
x_63 = lean_ctor_get(x_44, 3);
x_64 = 1;
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_64);
lean_ctor_set(x_41, 3, x_63);
lean_ctor_set(x_41, 2, x_62);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_60);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_64);
x_65 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
return x_1;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; 
x_66 = lean_ctor_get(x_44, 0);
x_67 = lean_ctor_get(x_44, 1);
x_68 = lean_ctor_get(x_44, 2);
x_69 = lean_ctor_get(x_44, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_44);
x_70 = 1;
x_71 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_71, 0, x_35);
lean_ctor_set(x_71, 1, x_36);
lean_ctor_set(x_71, 2, x_37);
lean_ctor_set(x_71, 3, x_43);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_70);
lean_ctor_set(x_41, 3, x_69);
lean_ctor_set(x_41, 2, x_68);
lean_ctor_set(x_41, 1, x_67);
lean_ctor_set(x_41, 0, x_66);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_70);
x_72 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_71);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_72);
return x_1;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_73 = lean_ctor_get(x_41, 1);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_41);
x_75 = lean_ctor_get(x_44, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_44, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_44, 3);
lean_inc(x_78);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_79 = x_44;
} else {
 lean_dec_ref(x_44);
 x_79 = lean_box(0);
}
x_80 = 1;
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(1, 4, 1);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_35);
lean_ctor_set(x_81, 1, x_36);
lean_ctor_set(x_81, 2, x_37);
lean_ctor_set(x_81, 3, x_43);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_80);
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_80);
x_83 = 0;
lean_ctor_set(x_1, 3, x_82);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_81);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_83);
return x_1;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_1);
x_84 = !lean_is_exclusive(x_44);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_44, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_44, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_44, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_44, 0);
lean_dec(x_88);
x_89 = 1;
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_89);
return x_44;
}
else
{
uint8_t x_90; lean_object* x_91; 
lean_dec(x_44);
x_90 = 1;
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_35);
lean_ctor_set(x_91, 1, x_36);
lean_ctor_set(x_91, 2, x_37);
lean_ctor_set(x_91, 3, x_41);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_41);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_41, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_43);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_43, 0);
x_97 = lean_ctor_get(x_43, 1);
x_98 = lean_ctor_get(x_43, 2);
x_99 = lean_ctor_get(x_43, 3);
x_100 = 1;
lean_ctor_set(x_43, 3, x_96);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_100);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_100);
x_101 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_101);
return x_1;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; 
x_102 = lean_ctor_get(x_43, 0);
x_103 = lean_ctor_get(x_43, 1);
x_104 = lean_ctor_get(x_43, 2);
x_105 = lean_ctor_get(x_43, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_43);
x_106 = 1;
x_107 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_107, 0, x_35);
lean_ctor_set(x_107, 1, x_36);
lean_ctor_set(x_107, 2, x_37);
lean_ctor_set(x_107, 3, x_102);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_106);
lean_ctor_set(x_41, 0, x_105);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_106);
x_108 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_107);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_109 = lean_ctor_get(x_41, 1);
x_110 = lean_ctor_get(x_41, 2);
x_111 = lean_ctor_get(x_41, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_41);
x_112 = lean_ctor_get(x_43, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_43, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_43, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_43, 3);
lean_inc(x_115);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_116 = x_43;
} else {
 lean_dec_ref(x_43);
 x_116 = lean_box(0);
}
x_117 = 1;
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(1, 4, 1);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_35);
lean_ctor_set(x_118, 1, x_36);
lean_ctor_set(x_118, 2, x_37);
lean_ctor_set(x_118, 3, x_112);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_117);
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_109);
lean_ctor_set(x_119, 2, x_110);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_117);
x_120 = 0;
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set(x_1, 2, x_114);
lean_ctor_set(x_1, 1, x_113);
lean_ctor_set(x_1, 0, x_118);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_41, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_free_object(x_1);
x_122 = !lean_is_exclusive(x_43);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_43, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_43, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_43, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_43, 0);
lean_dec(x_126);
x_127 = 1;
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
else
{
uint8_t x_128; lean_object* x_129; 
lean_dec(x_43);
x_128 = 1;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_35);
lean_ctor_set(x_129, 1, x_36);
lean_ctor_set(x_129, 2, x_37);
lean_ctor_set(x_129, 3, x_41);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_41);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_41, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_41, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
x_139 = 1;
lean_inc(x_43);
lean_ctor_set(x_121, 3, x_43);
lean_ctor_set(x_121, 2, x_37);
lean_ctor_set(x_121, 1, x_36);
lean_ctor_set(x_121, 0, x_35);
x_140 = !lean_is_exclusive(x_43);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_141 = lean_ctor_get(x_43, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_43, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_43, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_43, 0);
lean_dec(x_144);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_139);
lean_ctor_set(x_43, 3, x_138);
lean_ctor_set(x_43, 2, x_137);
lean_ctor_set(x_43, 1, x_136);
lean_ctor_set(x_43, 0, x_135);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_139);
x_145 = 0;
lean_ctor_set(x_41, 3, x_43);
lean_ctor_set(x_41, 0, x_121);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_145);
return x_41;
}
else
{
lean_object* x_146; uint8_t x_147; 
lean_dec(x_43);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_139);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_136);
lean_ctor_set(x_146, 2, x_137);
lean_ctor_set(x_146, 3, x_138);
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_139);
x_147 = 0;
lean_ctor_set(x_41, 3, x_146);
lean_ctor_set(x_41, 0, x_121);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_147);
return x_41;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_148 = lean_ctor_get(x_121, 0);
x_149 = lean_ctor_get(x_121, 1);
x_150 = lean_ctor_get(x_121, 2);
x_151 = lean_ctor_get(x_121, 3);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_121);
x_152 = 1;
lean_inc(x_43);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_35);
lean_ctor_set(x_153, 1, x_36);
lean_ctor_set(x_153, 2, x_37);
lean_ctor_set(x_153, 3, x_43);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_154 = x_43;
} else {
 lean_dec_ref(x_43);
 x_154 = lean_box(0);
}
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_152);
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 4, 1);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_148);
lean_ctor_set(x_155, 1, x_149);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_151);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_152);
x_156 = 0;
lean_ctor_set(x_41, 3, x_155);
lean_ctor_set(x_41, 0, x_153);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_156);
return x_41;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; 
x_157 = lean_ctor_get(x_41, 1);
x_158 = lean_ctor_get(x_41, 2);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_41);
x_159 = lean_ctor_get(x_121, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_121, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_121, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_121, 3);
lean_inc(x_162);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_163 = x_121;
} else {
 lean_dec_ref(x_121);
 x_163 = lean_box(0);
}
x_164 = 1;
lean_inc(x_43);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_35);
lean_ctor_set(x_165, 1, x_36);
lean_ctor_set(x_165, 2, x_37);
lean_ctor_set(x_165, 3, x_43);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_166 = x_43;
} else {
 lean_dec_ref(x_43);
 x_166 = lean_box(0);
}
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_164);
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 4, 1);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set(x_167, 3, x_162);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_164);
x_168 = 0;
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_157);
lean_ctor_set(x_169, 2, x_158);
lean_ctor_set(x_169, 3, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_168);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_41);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_41, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_41, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_43);
if (x_173 == 0)
{
uint8_t x_174; 
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_130);
x_174 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_174);
return x_1;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_43, 0);
x_176 = lean_ctor_get(x_43, 1);
x_177 = lean_ctor_get(x_43, 2);
x_178 = lean_ctor_get(x_43, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_43);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_130);
lean_ctor_set(x_41, 0, x_179);
x_180 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_180);
return x_1;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_181 = lean_ctor_get(x_41, 1);
x_182 = lean_ctor_get(x_41, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_41);
x_183 = lean_ctor_get(x_43, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_43, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_43, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_43, 3);
lean_inc(x_186);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_187 = x_43;
} else {
 lean_dec_ref(x_43);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 4, 1);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_130);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_181);
lean_ctor_set(x_189, 2, x_182);
lean_ctor_set(x_189, 3, x_121);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_42);
x_190 = 1;
lean_ctor_set(x_1, 3, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_191; 
x_191 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
uint8_t x_192; 
lean_dec(x_37);
lean_dec(x_36);
x_192 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_192);
return x_1;
}
}
else
{
lean_object* x_193; uint8_t x_194; 
x_193 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_35, x_2, x_3);
x_194 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_193, 3);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_193);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_ctor_get(x_193, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_193, 0);
lean_dec(x_199);
lean_ctor_set(x_193, 0, x_196);
x_200 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_193, 1);
x_202 = lean_ctor_get(x_193, 2);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_193);
x_203 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_201);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_196);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_194);
x_204 = 1;
lean_ctor_set(x_1, 0, x_203);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_204);
return x_1;
}
}
else
{
uint8_t x_205; 
x_205 = lean_ctor_get_uint8(x_196, sizeof(void*)*4);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_193);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_193, 1);
x_208 = lean_ctor_get(x_193, 2);
x_209 = lean_ctor_get(x_193, 3);
lean_dec(x_209);
x_210 = lean_ctor_get(x_193, 0);
lean_dec(x_210);
x_211 = !lean_is_exclusive(x_196);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; 
x_212 = lean_ctor_get(x_196, 0);
x_213 = lean_ctor_get(x_196, 1);
x_214 = lean_ctor_get(x_196, 2);
x_215 = lean_ctor_get(x_196, 3);
x_216 = 1;
lean_ctor_set(x_196, 3, x_212);
lean_ctor_set(x_196, 2, x_208);
lean_ctor_set(x_196, 1, x_207);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_216);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_215);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_216);
x_217 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_214);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_1, 0, x_196);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_217);
return x_1;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; uint8_t x_224; 
x_218 = lean_ctor_get(x_196, 0);
x_219 = lean_ctor_get(x_196, 1);
x_220 = lean_ctor_get(x_196, 2);
x_221 = lean_ctor_get(x_196, 3);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_196);
x_222 = 1;
x_223 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_223, 0, x_195);
lean_ctor_set(x_223, 1, x_207);
lean_ctor_set(x_223, 2, x_208);
lean_ctor_set(x_223, 3, x_218);
lean_ctor_set_uint8(x_223, sizeof(void*)*4, x_222);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_221);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_222);
x_224 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_223);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_224);
return x_1;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_225 = lean_ctor_get(x_193, 1);
x_226 = lean_ctor_get(x_193, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_193);
x_227 = lean_ctor_get(x_196, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_196, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_196, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_196, 3);
lean_inc(x_230);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 x_231 = x_196;
} else {
 lean_dec_ref(x_196);
 x_231 = lean_box(0);
}
x_232 = 1;
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 4, 1);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_195);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_226);
lean_ctor_set(x_233, 3, x_227);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_36);
lean_ctor_set(x_234, 2, x_37);
lean_ctor_set(x_234, 3, x_38);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_232);
x_235 = 0;
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_229);
lean_ctor_set(x_1, 1, x_228);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8_t x_236; 
lean_free_object(x_1);
x_236 = !lean_is_exclusive(x_196);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_196, 3);
lean_dec(x_237);
x_238 = lean_ctor_get(x_196, 2);
lean_dec(x_238);
x_239 = lean_ctor_get(x_196, 1);
lean_dec(x_239);
x_240 = lean_ctor_get(x_196, 0);
lean_dec(x_240);
x_241 = 1;
lean_ctor_set(x_196, 3, x_38);
lean_ctor_set(x_196, 2, x_37);
lean_ctor_set(x_196, 1, x_36);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_241);
return x_196;
}
else
{
uint8_t x_242; lean_object* x_243; 
lean_dec(x_196);
x_242 = 1;
x_243 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_243, 0, x_193);
lean_ctor_set(x_243, 1, x_36);
lean_ctor_set(x_243, 2, x_37);
lean_ctor_set(x_243, 3, x_38);
lean_ctor_set_uint8(x_243, sizeof(void*)*4, x_242);
return x_243;
}
}
}
}
else
{
uint8_t x_244; 
x_244 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_246 = lean_ctor_get(x_193, 1);
x_247 = lean_ctor_get(x_193, 2);
x_248 = lean_ctor_get(x_193, 3);
x_249 = lean_ctor_get(x_193, 0);
lean_dec(x_249);
x_250 = !lean_is_exclusive(x_195);
if (x_250 == 0)
{
uint8_t x_251; uint8_t x_252; 
x_251 = 1;
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_251);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_248);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_251);
x_252 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_246);
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_253 = lean_ctor_get(x_195, 0);
x_254 = lean_ctor_get(x_195, 1);
x_255 = lean_ctor_get(x_195, 2);
x_256 = lean_ctor_get(x_195, 3);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_195);
x_257 = 1;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_253);
lean_ctor_set(x_258, 1, x_254);
lean_ctor_set(x_258, 2, x_255);
lean_ctor_set(x_258, 3, x_256);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_248);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_257);
x_259 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_246);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_260 = lean_ctor_get(x_193, 1);
x_261 = lean_ctor_get(x_193, 2);
x_262 = lean_ctor_get(x_193, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_193);
x_263 = lean_ctor_get(x_195, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_195, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_195, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_195, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_267 = x_195;
} else {
 lean_dec_ref(x_195);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_264);
lean_ctor_set(x_269, 2, x_265);
lean_ctor_set(x_269, 3, x_266);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_36);
lean_ctor_set(x_270, 2, x_37);
lean_ctor_set(x_270, 3, x_38);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
x_271 = 0;
lean_ctor_set(x_1, 3, x_270);
lean_ctor_set(x_1, 2, x_261);
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_271);
return x_1;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_193, 3);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
lean_free_object(x_1);
x_273 = !lean_is_exclusive(x_195);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_195, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_195, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_195, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_195, 0);
lean_dec(x_277);
x_278 = 1;
lean_ctor_set(x_195, 3, x_38);
lean_ctor_set(x_195, 2, x_37);
lean_ctor_set(x_195, 1, x_36);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_278);
return x_195;
}
else
{
uint8_t x_279; lean_object* x_280; 
lean_dec(x_195);
x_279 = 1;
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_193);
lean_ctor_set(x_280, 1, x_36);
lean_ctor_set(x_280, 2, x_37);
lean_ctor_set(x_280, 3, x_38);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_279);
return x_280;
}
}
else
{
uint8_t x_281; 
x_281 = lean_ctor_get_uint8(x_272, sizeof(void*)*4);
if (x_281 == 0)
{
uint8_t x_282; 
lean_free_object(x_1);
x_282 = !lean_is_exclusive(x_193);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_283 = lean_ctor_get(x_193, 1);
x_284 = lean_ctor_get(x_193, 2);
x_285 = lean_ctor_get(x_193, 3);
lean_dec(x_285);
x_286 = lean_ctor_get(x_193, 0);
lean_dec(x_286);
x_287 = !lean_is_exclusive(x_272);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_288 = lean_ctor_get(x_272, 0);
x_289 = lean_ctor_get(x_272, 1);
x_290 = lean_ctor_get(x_272, 2);
x_291 = lean_ctor_get(x_272, 3);
x_292 = 1;
lean_inc(x_195);
lean_ctor_set(x_272, 3, x_288);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_283);
lean_ctor_set(x_272, 0, x_195);
x_293 = !lean_is_exclusive(x_195);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_195, 3);
lean_dec(x_294);
x_295 = lean_ctor_get(x_195, 2);
lean_dec(x_295);
x_296 = lean_ctor_get(x_195, 1);
lean_dec(x_296);
x_297 = lean_ctor_get(x_195, 0);
lean_dec(x_297);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_292);
lean_ctor_set(x_195, 3, x_38);
lean_ctor_set(x_195, 2, x_37);
lean_ctor_set(x_195, 1, x_36);
lean_ctor_set(x_195, 0, x_291);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_292);
x_298 = 0;
lean_ctor_set(x_193, 3, x_195);
lean_ctor_set(x_193, 2, x_290);
lean_ctor_set(x_193, 1, x_289);
lean_ctor_set(x_193, 0, x_272);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_298);
return x_193;
}
else
{
lean_object* x_299; uint8_t x_300; 
lean_dec(x_195);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_292);
x_299 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_299, 0, x_291);
lean_ctor_set(x_299, 1, x_36);
lean_ctor_set(x_299, 2, x_37);
lean_ctor_set(x_299, 3, x_38);
lean_ctor_set_uint8(x_299, sizeof(void*)*4, x_292);
x_300 = 0;
lean_ctor_set(x_193, 3, x_299);
lean_ctor_set(x_193, 2, x_290);
lean_ctor_set(x_193, 1, x_289);
lean_ctor_set(x_193, 0, x_272);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_300);
return x_193;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_301 = lean_ctor_get(x_272, 0);
x_302 = lean_ctor_get(x_272, 1);
x_303 = lean_ctor_get(x_272, 2);
x_304 = lean_ctor_get(x_272, 3);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_272);
x_305 = 1;
lean_inc(x_195);
x_306 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_306, 0, x_195);
lean_ctor_set(x_306, 1, x_283);
lean_ctor_set(x_306, 2, x_284);
lean_ctor_set(x_306, 3, x_301);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_307 = x_195;
} else {
 lean_dec_ref(x_195);
 x_307 = lean_box(0);
}
lean_ctor_set_uint8(x_306, sizeof(void*)*4, x_305);
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 4, 1);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_36);
lean_ctor_set(x_308, 2, x_37);
lean_ctor_set(x_308, 3, x_38);
lean_ctor_set_uint8(x_308, sizeof(void*)*4, x_305);
x_309 = 0;
lean_ctor_set(x_193, 3, x_308);
lean_ctor_set(x_193, 2, x_303);
lean_ctor_set(x_193, 1, x_302);
lean_ctor_set(x_193, 0, x_306);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_309);
return x_193;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
x_310 = lean_ctor_get(x_193, 1);
x_311 = lean_ctor_get(x_193, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_193);
x_312 = lean_ctor_get(x_272, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_272, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_272, 2);
lean_inc(x_314);
x_315 = lean_ctor_get(x_272, 3);
lean_inc(x_315);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_316 = x_272;
} else {
 lean_dec_ref(x_272);
 x_316 = lean_box(0);
}
x_317 = 1;
lean_inc(x_195);
if (lean_is_scalar(x_316)) {
 x_318 = lean_alloc_ctor(1, 4, 1);
} else {
 x_318 = x_316;
}
lean_ctor_set(x_318, 0, x_195);
lean_ctor_set(x_318, 1, x_310);
lean_ctor_set(x_318, 2, x_311);
lean_ctor_set(x_318, 3, x_312);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_319 = x_195;
} else {
 lean_dec_ref(x_195);
 x_319 = lean_box(0);
}
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_317);
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 4, 1);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_36);
lean_ctor_set(x_320, 2, x_37);
lean_ctor_set(x_320, 3, x_38);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_317);
x_321 = 0;
x_322 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_322, 0, x_318);
lean_ctor_set(x_322, 1, x_313);
lean_ctor_set(x_322, 2, x_314);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_321);
return x_322;
}
}
else
{
uint8_t x_323; 
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_324 = lean_ctor_get(x_193, 3);
lean_dec(x_324);
x_325 = lean_ctor_get(x_193, 0);
lean_dec(x_325);
x_326 = !lean_is_exclusive(x_195);
if (x_326 == 0)
{
uint8_t x_327; 
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_281);
x_327 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_327);
return x_1;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_328 = lean_ctor_get(x_195, 0);
x_329 = lean_ctor_get(x_195, 1);
x_330 = lean_ctor_get(x_195, 2);
x_331 = lean_ctor_get(x_195, 3);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_195);
x_332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_332, 0, x_328);
lean_ctor_set(x_332, 1, x_329);
lean_ctor_set(x_332, 2, x_330);
lean_ctor_set(x_332, 3, x_331);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_281);
lean_ctor_set(x_193, 0, x_332);
x_333 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_333);
return x_1;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_334 = lean_ctor_get(x_193, 1);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_193);
x_336 = lean_ctor_get(x_195, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_195, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_195, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_195, 3);
lean_inc(x_339);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_340 = x_195;
} else {
 lean_dec_ref(x_195);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 4, 1);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_336);
lean_ctor_set(x_341, 1, x_337);
lean_ctor_set(x_341, 2, x_338);
lean_ctor_set(x_341, 3, x_339);
lean_ctor_set_uint8(x_341, sizeof(void*)*4, x_281);
x_342 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_334);
lean_ctor_set(x_342, 2, x_335);
lean_ctor_set(x_342, 3, x_272);
lean_ctor_set_uint8(x_342, sizeof(void*)*4, x_194);
x_343 = 1;
lean_ctor_set(x_1, 0, x_342);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_344; 
x_344 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_344);
return x_1;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_345 = lean_ctor_get(x_1, 0);
x_346 = lean_ctor_get(x_1, 1);
x_347 = lean_ctor_get(x_1, 2);
x_348 = lean_ctor_get(x_1, 3);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_1);
x_349 = lean_nat_dec_lt(x_2, x_346);
if (x_349 == 0)
{
uint8_t x_350; 
x_350 = lean_nat_dec_eq(x_2, x_346);
if (x_350 == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_348, x_2, x_3);
x_352 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_351, 3);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; 
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_351, 2);
lean_inc(x_356);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_357 = x_351;
} else {
 lean_dec_ref(x_351);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_354);
lean_ctor_set(x_358, 1, x_355);
lean_ctor_set(x_358, 2, x_356);
lean_ctor_set(x_358, 3, x_354);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_352);
x_359 = 1;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_345);
lean_ctor_set(x_360, 1, x_346);
lean_ctor_set(x_360, 2, x_347);
lean_ctor_set(x_360, 3, x_358);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
return x_360;
}
else
{
uint8_t x_361; 
x_361 = lean_ctor_get_uint8(x_354, sizeof(void*)*4);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_362 = lean_ctor_get(x_351, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_351, 2);
lean_inc(x_363);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_364 = x_351;
} else {
 lean_dec_ref(x_351);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_354, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_354, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_354, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_354, 3);
lean_inc(x_368);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_369 = x_354;
} else {
 lean_dec_ref(x_354);
 x_369 = lean_box(0);
}
x_370 = 1;
if (lean_is_scalar(x_369)) {
 x_371 = lean_alloc_ctor(1, 4, 1);
} else {
 x_371 = x_369;
}
lean_ctor_set(x_371, 0, x_345);
lean_ctor_set(x_371, 1, x_346);
lean_ctor_set(x_371, 2, x_347);
lean_ctor_set(x_371, 3, x_353);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_370);
if (lean_is_scalar(x_364)) {
 x_372 = lean_alloc_ctor(1, 4, 1);
} else {
 x_372 = x_364;
}
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_366);
lean_ctor_set(x_372, 2, x_367);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_370);
x_373 = 0;
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_362);
lean_ctor_set(x_374, 2, x_363);
lean_ctor_set(x_374, 3, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
else
{
lean_object* x_375; uint8_t x_376; lean_object* x_377; 
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_375 = x_354;
} else {
 lean_dec_ref(x_354);
 x_375 = lean_box(0);
}
x_376 = 1;
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_345);
lean_ctor_set(x_377, 1, x_346);
lean_ctor_set(x_377, 2, x_347);
lean_ctor_set(x_377, 3, x_351);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_376);
return x_377;
}
}
}
else
{
uint8_t x_378; 
x_378 = lean_ctor_get_uint8(x_353, sizeof(void*)*4);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; 
x_379 = lean_ctor_get(x_351, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_351, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_351, 3);
lean_inc(x_381);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_382 = x_351;
} else {
 lean_dec_ref(x_351);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_353, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_353, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_353, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_353, 3);
lean_inc(x_386);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_387 = x_353;
} else {
 lean_dec_ref(x_353);
 x_387 = lean_box(0);
}
x_388 = 1;
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_345);
lean_ctor_set(x_389, 1, x_346);
lean_ctor_set(x_389, 2, x_347);
lean_ctor_set(x_389, 3, x_383);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(1, 4, 1);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_379);
lean_ctor_set(x_390, 2, x_380);
lean_ctor_set(x_390, 3, x_381);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_388);
x_391 = 0;
x_392 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_384);
lean_ctor_set(x_392, 2, x_385);
lean_ctor_set(x_392, 3, x_390);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_351, 3);
lean_inc(x_393);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; uint8_t x_395; lean_object* x_396; 
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_394 = x_353;
} else {
 lean_dec_ref(x_353);
 x_394 = lean_box(0);
}
x_395 = 1;
if (lean_is_scalar(x_394)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_394;
}
lean_ctor_set(x_396, 0, x_345);
lean_ctor_set(x_396, 1, x_346);
lean_ctor_set(x_396, 2, x_347);
lean_ctor_set(x_396, 3, x_351);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_395);
return x_396;
}
else
{
uint8_t x_397; 
x_397 = lean_ctor_get_uint8(x_393, sizeof(void*)*4);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; 
x_398 = lean_ctor_get(x_351, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_351, 2);
lean_inc(x_399);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_400 = x_351;
} else {
 lean_dec_ref(x_351);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_393, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_393, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_393, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_393, 3);
lean_inc(x_404);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 lean_ctor_release(x_393, 2);
 lean_ctor_release(x_393, 3);
 x_405 = x_393;
} else {
 lean_dec_ref(x_393);
 x_405 = lean_box(0);
}
x_406 = 1;
lean_inc(x_353);
if (lean_is_scalar(x_405)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_405;
}
lean_ctor_set(x_407, 0, x_345);
lean_ctor_set(x_407, 1, x_346);
lean_ctor_set(x_407, 2, x_347);
lean_ctor_set(x_407, 3, x_353);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_408 = x_353;
} else {
 lean_dec_ref(x_353);
 x_408 = lean_box(0);
}
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_401);
lean_ctor_set(x_409, 1, x_402);
lean_ctor_set(x_409, 2, x_403);
lean_ctor_set(x_409, 3, x_404);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_406);
x_410 = 0;
if (lean_is_scalar(x_400)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_400;
}
lean_ctor_set(x_411, 0, x_407);
lean_ctor_set(x_411, 1, x_398);
lean_ctor_set(x_411, 2, x_399);
lean_ctor_set(x_411, 3, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_410);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; 
x_412 = lean_ctor_get(x_351, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_351, 2);
lean_inc(x_413);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_414 = x_351;
} else {
 lean_dec_ref(x_351);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_353, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_353, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_353, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_353, 3);
lean_inc(x_418);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_419 = x_353;
} else {
 lean_dec_ref(x_353);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_415);
lean_ctor_set(x_420, 1, x_416);
lean_ctor_set(x_420, 2, x_417);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_397);
if (lean_is_scalar(x_414)) {
 x_421 = lean_alloc_ctor(1, 4, 1);
} else {
 x_421 = x_414;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_412);
lean_ctor_set(x_421, 2, x_413);
lean_ctor_set(x_421, 3, x_393);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_352);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_345);
lean_ctor_set(x_423, 1, x_346);
lean_ctor_set(x_423, 2, x_347);
lean_ctor_set(x_423, 3, x_421);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
}
}
}
}
else
{
uint8_t x_424; lean_object* x_425; 
x_424 = 1;
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_345);
lean_ctor_set(x_425, 1, x_346);
lean_ctor_set(x_425, 2, x_347);
lean_ctor_set(x_425, 3, x_351);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_424);
return x_425;
}
}
else
{
uint8_t x_426; lean_object* x_427; 
lean_dec(x_347);
lean_dec(x_346);
x_426 = 1;
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_345);
lean_ctor_set(x_427, 1, x_2);
lean_ctor_set(x_427, 2, x_3);
lean_ctor_set(x_427, 3, x_348);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_426);
return x_427;
}
}
else
{
lean_object* x_428; uint8_t x_429; 
x_428 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_345, x_2, x_3);
x_429 = lean_ctor_get_uint8(x_428, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_428, 3);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_428, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_434 = x_428;
} else {
 lean_dec_ref(x_428);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_431);
lean_ctor_set(x_435, 1, x_432);
lean_ctor_set(x_435, 2, x_433);
lean_ctor_set(x_435, 3, x_431);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_429);
x_436 = 1;
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_346);
lean_ctor_set(x_437, 2, x_347);
lean_ctor_set(x_437, 3, x_348);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_436);
return x_437;
}
else
{
uint8_t x_438; 
x_438 = lean_ctor_get_uint8(x_431, sizeof(void*)*4);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; 
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_441 = x_428;
} else {
 lean_dec_ref(x_428);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_431, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_431, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_431, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_431, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_446 = x_431;
} else {
 lean_dec_ref(x_431);
 x_446 = lean_box(0);
}
x_447 = 1;
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_430);
lean_ctor_set(x_448, 1, x_439);
lean_ctor_set(x_448, 2, x_440);
lean_ctor_set(x_448, 3, x_442);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(1, 4, 1);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_346);
lean_ctor_set(x_449, 2, x_347);
lean_ctor_set(x_449, 3, x_348);
lean_ctor_set_uint8(x_449, sizeof(void*)*4, x_447);
x_450 = 0;
x_451 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_443);
lean_ctor_set(x_451, 2, x_444);
lean_ctor_set(x_451, 3, x_449);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
return x_451;
}
else
{
lean_object* x_452; uint8_t x_453; lean_object* x_454; 
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_452 = x_431;
} else {
 lean_dec_ref(x_431);
 x_452 = lean_box(0);
}
x_453 = 1;
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_428);
lean_ctor_set(x_454, 1, x_346);
lean_ctor_set(x_454, 2, x_347);
lean_ctor_set(x_454, 3, x_348);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
}
}
else
{
uint8_t x_455; 
x_455 = lean_ctor_get_uint8(x_430, sizeof(void*)*4);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; 
x_456 = lean_ctor_get(x_428, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_428, 2);
lean_inc(x_457);
x_458 = lean_ctor_get(x_428, 3);
lean_inc(x_458);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_459 = x_428;
} else {
 lean_dec_ref(x_428);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_430, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_430, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_430, 2);
lean_inc(x_462);
x_463 = lean_ctor_get(x_430, 3);
lean_inc(x_463);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_464 = x_430;
} else {
 lean_dec_ref(x_430);
 x_464 = lean_box(0);
}
x_465 = 1;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_460);
lean_ctor_set(x_466, 1, x_461);
lean_ctor_set(x_466, 2, x_462);
lean_ctor_set(x_466, 3, x_463);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
if (lean_is_scalar(x_459)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_459;
}
lean_ctor_set(x_467, 0, x_458);
lean_ctor_set(x_467, 1, x_346);
lean_ctor_set(x_467, 2, x_347);
lean_ctor_set(x_467, 3, x_348);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_465);
x_468 = 0;
x_469 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_456);
lean_ctor_set(x_469, 2, x_457);
lean_ctor_set(x_469, 3, x_467);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_428, 3);
lean_inc(x_470);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; uint8_t x_472; lean_object* x_473; 
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_471 = x_430;
} else {
 lean_dec_ref(x_430);
 x_471 = lean_box(0);
}
x_472 = 1;
if (lean_is_scalar(x_471)) {
 x_473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_473 = x_471;
}
lean_ctor_set(x_473, 0, x_428);
lean_ctor_set(x_473, 1, x_346);
lean_ctor_set(x_473, 2, x_347);
lean_ctor_set(x_473, 3, x_348);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_472);
return x_473;
}
else
{
uint8_t x_474; 
x_474 = lean_ctor_get_uint8(x_470, sizeof(void*)*4);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; 
x_475 = lean_ctor_get(x_428, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_428, 2);
lean_inc(x_476);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_477 = x_428;
} else {
 lean_dec_ref(x_428);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_470, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_470, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_470, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_470, 3);
lean_inc(x_481);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 lean_ctor_release(x_470, 2);
 lean_ctor_release(x_470, 3);
 x_482 = x_470;
} else {
 lean_dec_ref(x_470);
 x_482 = lean_box(0);
}
x_483 = 1;
lean_inc(x_430);
if (lean_is_scalar(x_482)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_482;
}
lean_ctor_set(x_484, 0, x_430);
lean_ctor_set(x_484, 1, x_475);
lean_ctor_set(x_484, 2, x_476);
lean_ctor_set(x_484, 3, x_478);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_485 = x_430;
} else {
 lean_dec_ref(x_430);
 x_485 = lean_box(0);
}
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 4, 1);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_346);
lean_ctor_set(x_486, 2, x_347);
lean_ctor_set(x_486, 3, x_348);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_483);
x_487 = 0;
if (lean_is_scalar(x_477)) {
 x_488 = lean_alloc_ctor(1, 4, 1);
} else {
 x_488 = x_477;
}
lean_ctor_set(x_488, 0, x_484);
lean_ctor_set(x_488, 1, x_479);
lean_ctor_set(x_488, 2, x_480);
lean_ctor_set(x_488, 3, x_486);
lean_ctor_set_uint8(x_488, sizeof(void*)*4, x_487);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; lean_object* x_500; 
x_489 = lean_ctor_get(x_428, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_428, 2);
lean_inc(x_490);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_491 = x_428;
} else {
 lean_dec_ref(x_428);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_430, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_430, 1);
lean_inc(x_493);
x_494 = lean_ctor_get(x_430, 2);
lean_inc(x_494);
x_495 = lean_ctor_get(x_430, 3);
lean_inc(x_495);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_496 = x_430;
} else {
 lean_dec_ref(x_430);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 4, 1);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_492);
lean_ctor_set(x_497, 1, x_493);
lean_ctor_set(x_497, 2, x_494);
lean_ctor_set(x_497, 3, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_474);
if (lean_is_scalar(x_491)) {
 x_498 = lean_alloc_ctor(1, 4, 1);
} else {
 x_498 = x_491;
}
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_489);
lean_ctor_set(x_498, 2, x_490);
lean_ctor_set(x_498, 3, x_470);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_429);
x_499 = 1;
x_500 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_346);
lean_ctor_set(x_500, 2, x_347);
lean_ctor_set(x_500, 3, x_348);
lean_ctor_set_uint8(x_500, sizeof(void*)*4, x_499);
return x_500;
}
}
}
}
}
else
{
uint8_t x_501; lean_object* x_502; 
x_501 = 1;
x_502 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_502, 0, x_428);
lean_ctor_set(x_502, 1, x_346);
lean_ctor_set(x_502, 2, x_347);
lean_ctor_set(x_502, 3, x_348);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_501);
return x_502;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_IR_LocalContext_addLocal___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_1, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_LocalContext_addParams___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_IR_LocalContext_addParam(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_IR_LocalContext_addParams___spec__1(x_2, x_7, x_8, x_1);
lean_dec(x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_LocalContext_addParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LocalContext_isJP(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_getJPBody(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_getJPParams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LocalContext_isParam(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LocalContext_isLocalVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LocalContext_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = lean_nat_dec_lt(x_1, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_1, x_6);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_RBNode_isBlack___rarg(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_8);
x_13 = 0;
lean_ctor_set(x_2, 3, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_2);
x_14 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_8);
x_15 = l_Lean_RBNode_balRight___rarg(x_5, x_6, x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_free_object(x_2);
lean_dec(x_7);
lean_dec(x_6);
x_16 = l_Lean_RBNode_appendTrees___rarg(x_5, x_8);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = l_Lean_RBNode_isBlack___rarg(x_5);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_5);
x_19 = 0;
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_2);
x_20 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_5);
x_21 = l_Lean_RBNode_balLeft___rarg(x_20, x_6, x_7, x_8);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
x_25 = lean_ctor_get(x_2, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_26 = lean_nat_dec_lt(x_1, x_23);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_1, x_23);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_RBNode_isBlack___rarg(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_25);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_25);
x_33 = l_Lean_RBNode_balRight___rarg(x_22, x_23, x_24, x_32);
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_23);
x_34 = l_Lean_RBNode_appendTrees___rarg(x_22, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = l_Lean_RBNode_isBlack___rarg(x_22);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_22);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_23);
lean_ctor_set(x_38, 2, x_24);
lean_ctor_set(x_38, 3, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_22);
x_40 = l_Lean_RBNode_balLeft___rarg(x_39, x_23, x_24, x_25);
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(x_2, x_1);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; 
lean_free_object(x_3);
lean_dec(x_6);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; 
lean_dec(x_9);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_getType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_getValue(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_IR_VarId_alphaEqv___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_2, x_5);
if (x_9 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
lean_object* x_11; 
lean_inc(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at_Lean_IR_VarId_alphaEqv___spec__1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_eq(x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at_Lean_IR_VarId_alphaEqv___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_VarId_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instAlphaEqvVarId___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_VarId_alphaEqv___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instAlphaEqvVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instAlphaEqvVarId___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_VarId_alphaEqv(x_1, x_4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Arg_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instAlphaEqvArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Arg_alphaEqv___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instAlphaEqvArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instAlphaEqvArg___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_IR_args_alphaEqv___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_fget(x_5, x_7);
x_12 = lean_array_fget(x_6, x_7);
x_13 = l_Lean_IR_Arg_alphaEqv(x_1, x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_4 = lean_box(0);
x_7 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_isEqvAux___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_2, x_3, lean_box(0), x_2, x_3, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_IR_args_alphaEqv___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_args_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instAlphaEqvArrayArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_args_alphaEqv___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instAlphaEqvArrayArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instAlphaEqvArrayArg___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_IR_CtorInfo_beq(x_4, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_IR_args_alphaEqv(x_1, x_5, x_7);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_nat_dec_eq(x_12, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_IR_VarId_alphaEqv(x_1, x_13, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_27 = lean_ctor_get(x_3, 2);
x_28 = l_Lean_IR_VarId_alphaEqv(x_1, x_20, x_24);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
else
{
uint8_t x_30; 
x_30 = l_Lean_IR_CtorInfo_beq(x_21, x_25);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
if (x_22 == 0)
{
if (x_26 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_IR_args_alphaEqv(x_1, x_23, x_27);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = 0;
return x_33;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_IR_args_alphaEqv(x_1, x_23, x_27);
return x_35;
}
}
}
}
}
else
{
uint8_t x_36; 
x_36 = 0;
return x_36;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_nat_dec_eq(x_37, x_39);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 0;
return x_42;
}
else
{
uint8_t x_43; 
x_43 = l_Lean_IR_VarId_alphaEqv(x_1, x_38, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = 0;
return x_44;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_nat_dec_eq(x_45, x_47);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = 0;
return x_50;
}
else
{
uint8_t x_51; 
x_51 = l_Lean_IR_VarId_alphaEqv(x_1, x_46, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = 0;
return x_52;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_ctor_get(x_3, 0);
x_57 = lean_ctor_get(x_3, 1);
x_58 = lean_ctor_get(x_3, 2);
x_59 = lean_nat_dec_eq(x_53, x_56);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = 0;
return x_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_eq(x_54, x_57);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = 0;
return x_62;
}
else
{
uint8_t x_63; 
x_63 = l_Lean_IR_VarId_alphaEqv(x_1, x_55, x_58);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = 0;
return x_64;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_ctor_get(x_3, 0);
x_68 = lean_ctor_get(x_3, 1);
x_69 = lean_name_eq(x_65, x_67);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = 0;
return x_70;
}
else
{
uint8_t x_71; 
x_71 = l_Lean_IR_args_alphaEqv(x_1, x_66, x_68);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = 0;
return x_72;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get(x_3, 0);
x_76 = lean_ctor_get(x_3, 1);
x_77 = lean_name_eq(x_73, x_75);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = 0;
return x_78;
}
else
{
uint8_t x_79; 
x_79 = l_Lean_IR_args_alphaEqv(x_1, x_74, x_76);
return x_79;
}
}
else
{
uint8_t x_80; 
x_80 = 0;
return x_80;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_2, 0);
x_82 = lean_ctor_get(x_2, 1);
x_83 = lean_ctor_get(x_3, 0);
x_84 = lean_ctor_get(x_3, 1);
x_85 = l_Lean_IR_VarId_alphaEqv(x_1, x_81, x_83);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = 0;
return x_86;
}
else
{
uint8_t x_87; 
x_87 = l_Lean_IR_args_alphaEqv(x_1, x_82, x_84);
return x_87;
}
}
else
{
uint8_t x_88; 
x_88 = 0;
return x_88;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_2, 0);
x_90 = lean_ctor_get(x_2, 1);
x_91 = lean_ctor_get(x_3, 0);
x_92 = lean_ctor_get(x_3, 1);
x_93 = l_Lean_IR_IRType_beq(x_89, x_91);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = 0;
return x_94;
}
else
{
uint8_t x_95; 
x_95 = l_Lean_IR_VarId_alphaEqv(x_1, x_90, x_92);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = 0;
return x_96;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_2, 0);
x_98 = lean_ctor_get(x_3, 0);
x_99 = l_Lean_IR_VarId_alphaEqv(x_1, x_97, x_98);
return x_99;
}
else
{
uint8_t x_100; 
x_100 = 0;
return x_100;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_2, 0);
x_102 = lean_ctor_get(x_3, 0);
x_103 = l_Lean_IR_LitVal_beq(x_101, x_102);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = 0;
return x_104;
}
}
default: 
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_2, 0);
x_106 = lean_ctor_get(x_3, 0);
x_107 = l_Lean_IR_VarId_alphaEqv(x_1, x_105, x_106);
return x_107;
}
else
{
uint8_t x_108; 
x_108 = 0;
return x_108;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Expr_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instAlphaEqvExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Expr_alphaEqv___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instAlphaEqvExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instAlphaEqvExpr___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_nat_dec_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_2, x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_12, x_2, x_3);
x_16 = 0;
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_nat_dec_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_2, x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_23, x_2, x_3);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_21);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_nat_dec_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_nat_dec_eq(x_2, x_36);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_38, x_2, x_3);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_41, 3);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_41, 3);
lean_dec(x_46);
x_47 = lean_ctor_get(x_41, 0);
lean_dec(x_47);
lean_ctor_set(x_41, 0, x_44);
x_48 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_48);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_41, 1);
x_50 = lean_ctor_get(x_41, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_44);
lean_ctor_set_uint8(x_51, sizeof(void*)*4, x_42);
x_52 = 1;
lean_ctor_set(x_1, 3, x_51);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_52);
return x_1;
}
}
else
{
uint8_t x_53; 
x_53 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_41, 1);
x_56 = lean_ctor_get(x_41, 2);
x_57 = lean_ctor_get(x_41, 3);
lean_dec(x_57);
x_58 = lean_ctor_get(x_41, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
x_62 = lean_ctor_get(x_44, 2);
x_63 = lean_ctor_get(x_44, 3);
x_64 = 1;
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_64);
lean_ctor_set(x_41, 3, x_63);
lean_ctor_set(x_41, 2, x_62);
lean_ctor_set(x_41, 1, x_61);
lean_ctor_set(x_41, 0, x_60);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_64);
x_65 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_65);
return x_1;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; 
x_66 = lean_ctor_get(x_44, 0);
x_67 = lean_ctor_get(x_44, 1);
x_68 = lean_ctor_get(x_44, 2);
x_69 = lean_ctor_get(x_44, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_44);
x_70 = 1;
x_71 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_71, 0, x_35);
lean_ctor_set(x_71, 1, x_36);
lean_ctor_set(x_71, 2, x_37);
lean_ctor_set(x_71, 3, x_43);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_70);
lean_ctor_set(x_41, 3, x_69);
lean_ctor_set(x_41, 2, x_68);
lean_ctor_set(x_41, 1, x_67);
lean_ctor_set(x_41, 0, x_66);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_70);
x_72 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_56);
lean_ctor_set(x_1, 1, x_55);
lean_ctor_set(x_1, 0, x_71);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_72);
return x_1;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_73 = lean_ctor_get(x_41, 1);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_41);
x_75 = lean_ctor_get(x_44, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_44, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_44, 3);
lean_inc(x_78);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_79 = x_44;
} else {
 lean_dec_ref(x_44);
 x_79 = lean_box(0);
}
x_80 = 1;
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(1, 4, 1);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_35);
lean_ctor_set(x_81, 1, x_36);
lean_ctor_set(x_81, 2, x_37);
lean_ctor_set(x_81, 3, x_43);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_80);
x_82 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_80);
x_83 = 0;
lean_ctor_set(x_1, 3, x_82);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_81);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_83);
return x_1;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_1);
x_84 = !lean_is_exclusive(x_44);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_44, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_44, 2);
lean_dec(x_86);
x_87 = lean_ctor_get(x_44, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_44, 0);
lean_dec(x_88);
x_89 = 1;
lean_ctor_set(x_44, 3, x_41);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_89);
return x_44;
}
else
{
uint8_t x_90; lean_object* x_91; 
lean_dec(x_44);
x_90 = 1;
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_35);
lean_ctor_set(x_91, 1, x_36);
lean_ctor_set(x_91, 2, x_37);
lean_ctor_set(x_91, 3, x_41);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_43, sizeof(void*)*4);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_41);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_41, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_43);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_43, 0);
x_97 = lean_ctor_get(x_43, 1);
x_98 = lean_ctor_get(x_43, 2);
x_99 = lean_ctor_get(x_43, 3);
x_100 = 1;
lean_ctor_set(x_43, 3, x_96);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_100);
lean_ctor_set(x_41, 0, x_99);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_100);
x_101 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_101);
return x_1;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; 
x_102 = lean_ctor_get(x_43, 0);
x_103 = lean_ctor_get(x_43, 1);
x_104 = lean_ctor_get(x_43, 2);
x_105 = lean_ctor_get(x_43, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_43);
x_106 = 1;
x_107 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_107, 0, x_35);
lean_ctor_set(x_107, 1, x_36);
lean_ctor_set(x_107, 2, x_37);
lean_ctor_set(x_107, 3, x_102);
lean_ctor_set_uint8(x_107, sizeof(void*)*4, x_106);
lean_ctor_set(x_41, 0, x_105);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_106);
x_108 = 0;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_107);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_108);
return x_1;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_109 = lean_ctor_get(x_41, 1);
x_110 = lean_ctor_get(x_41, 2);
x_111 = lean_ctor_get(x_41, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_41);
x_112 = lean_ctor_get(x_43, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_43, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_43, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_43, 3);
lean_inc(x_115);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_116 = x_43;
} else {
 lean_dec_ref(x_43);
 x_116 = lean_box(0);
}
x_117 = 1;
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(1, 4, 1);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_35);
lean_ctor_set(x_118, 1, x_36);
lean_ctor_set(x_118, 2, x_37);
lean_ctor_set(x_118, 3, x_112);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_117);
x_119 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_109);
lean_ctor_set(x_119, 2, x_110);
lean_ctor_set(x_119, 3, x_111);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_117);
x_120 = 0;
lean_ctor_set(x_1, 3, x_119);
lean_ctor_set(x_1, 2, x_114);
lean_ctor_set(x_1, 1, x_113);
lean_ctor_set(x_1, 0, x_118);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_120);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_41, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_free_object(x_1);
x_122 = !lean_is_exclusive(x_43);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_123 = lean_ctor_get(x_43, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_43, 2);
lean_dec(x_124);
x_125 = lean_ctor_get(x_43, 1);
lean_dec(x_125);
x_126 = lean_ctor_get(x_43, 0);
lean_dec(x_126);
x_127 = 1;
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
else
{
uint8_t x_128; lean_object* x_129; 
lean_dec(x_43);
x_128 = 1;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_35);
lean_ctor_set(x_129, 1, x_36);
lean_ctor_set(x_129, 2, x_37);
lean_ctor_set(x_129, 3, x_41);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_41);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_41, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_41, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
x_139 = 1;
lean_inc(x_43);
lean_ctor_set(x_121, 3, x_43);
lean_ctor_set(x_121, 2, x_37);
lean_ctor_set(x_121, 1, x_36);
lean_ctor_set(x_121, 0, x_35);
x_140 = !lean_is_exclusive(x_43);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_141 = lean_ctor_get(x_43, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_43, 2);
lean_dec(x_142);
x_143 = lean_ctor_get(x_43, 1);
lean_dec(x_143);
x_144 = lean_ctor_get(x_43, 0);
lean_dec(x_144);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_139);
lean_ctor_set(x_43, 3, x_138);
lean_ctor_set(x_43, 2, x_137);
lean_ctor_set(x_43, 1, x_136);
lean_ctor_set(x_43, 0, x_135);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_139);
x_145 = 0;
lean_ctor_set(x_41, 3, x_43);
lean_ctor_set(x_41, 0, x_121);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_145);
return x_41;
}
else
{
lean_object* x_146; uint8_t x_147; 
lean_dec(x_43);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_139);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_136);
lean_ctor_set(x_146, 2, x_137);
lean_ctor_set(x_146, 3, x_138);
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_139);
x_147 = 0;
lean_ctor_set(x_41, 3, x_146);
lean_ctor_set(x_41, 0, x_121);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_147);
return x_41;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_148 = lean_ctor_get(x_121, 0);
x_149 = lean_ctor_get(x_121, 1);
x_150 = lean_ctor_get(x_121, 2);
x_151 = lean_ctor_get(x_121, 3);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_121);
x_152 = 1;
lean_inc(x_43);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_35);
lean_ctor_set(x_153, 1, x_36);
lean_ctor_set(x_153, 2, x_37);
lean_ctor_set(x_153, 3, x_43);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_154 = x_43;
} else {
 lean_dec_ref(x_43);
 x_154 = lean_box(0);
}
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_152);
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 4, 1);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_148);
lean_ctor_set(x_155, 1, x_149);
lean_ctor_set(x_155, 2, x_150);
lean_ctor_set(x_155, 3, x_151);
lean_ctor_set_uint8(x_155, sizeof(void*)*4, x_152);
x_156 = 0;
lean_ctor_set(x_41, 3, x_155);
lean_ctor_set(x_41, 0, x_153);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_156);
return x_41;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; 
x_157 = lean_ctor_get(x_41, 1);
x_158 = lean_ctor_get(x_41, 2);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_41);
x_159 = lean_ctor_get(x_121, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_121, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_121, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_121, 3);
lean_inc(x_162);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_163 = x_121;
} else {
 lean_dec_ref(x_121);
 x_163 = lean_box(0);
}
x_164 = 1;
lean_inc(x_43);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_35);
lean_ctor_set(x_165, 1, x_36);
lean_ctor_set(x_165, 2, x_37);
lean_ctor_set(x_165, 3, x_43);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_166 = x_43;
} else {
 lean_dec_ref(x_43);
 x_166 = lean_box(0);
}
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_164);
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 4, 1);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set(x_167, 3, x_162);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_164);
x_168 = 0;
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_157);
lean_ctor_set(x_169, 2, x_158);
lean_ctor_set(x_169, 3, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_168);
return x_169;
}
}
else
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_41);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_41, 3);
lean_dec(x_171);
x_172 = lean_ctor_get(x_41, 0);
lean_dec(x_172);
x_173 = !lean_is_exclusive(x_43);
if (x_173 == 0)
{
uint8_t x_174; 
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_130);
x_174 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_174);
return x_1;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_43, 0);
x_176 = lean_ctor_get(x_43, 1);
x_177 = lean_ctor_get(x_43, 2);
x_178 = lean_ctor_get(x_43, 3);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_43);
x_179 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_176);
lean_ctor_set(x_179, 2, x_177);
lean_ctor_set(x_179, 3, x_178);
lean_ctor_set_uint8(x_179, sizeof(void*)*4, x_130);
lean_ctor_set(x_41, 0, x_179);
x_180 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_180);
return x_1;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_181 = lean_ctor_get(x_41, 1);
x_182 = lean_ctor_get(x_41, 2);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_41);
x_183 = lean_ctor_get(x_43, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_43, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_43, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_43, 3);
lean_inc(x_186);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 lean_ctor_release(x_43, 3);
 x_187 = x_43;
} else {
 lean_dec_ref(x_43);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 4, 1);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_130);
x_189 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_181);
lean_ctor_set(x_189, 2, x_182);
lean_ctor_set(x_189, 3, x_121);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_42);
x_190 = 1;
lean_ctor_set(x_1, 3, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_191; 
x_191 = 1;
lean_ctor_set(x_1, 3, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
}
else
{
uint8_t x_192; 
lean_dec(x_37);
lean_dec(x_36);
x_192 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_192);
return x_1;
}
}
else
{
lean_object* x_193; uint8_t x_194; 
x_193 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_35, x_2, x_3);
x_194 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_193, 3);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_193);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_198 = lean_ctor_get(x_193, 3);
lean_dec(x_198);
x_199 = lean_ctor_get(x_193, 0);
lean_dec(x_199);
lean_ctor_set(x_193, 0, x_196);
x_200 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_193, 1);
x_202 = lean_ctor_get(x_193, 2);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_193);
x_203 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_201);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_196);
lean_ctor_set_uint8(x_203, sizeof(void*)*4, x_194);
x_204 = 1;
lean_ctor_set(x_1, 0, x_203);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_204);
return x_1;
}
}
else
{
uint8_t x_205; 
x_205 = lean_ctor_get_uint8(x_196, sizeof(void*)*4);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_193);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_193, 1);
x_208 = lean_ctor_get(x_193, 2);
x_209 = lean_ctor_get(x_193, 3);
lean_dec(x_209);
x_210 = lean_ctor_get(x_193, 0);
lean_dec(x_210);
x_211 = !lean_is_exclusive(x_196);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; 
x_212 = lean_ctor_get(x_196, 0);
x_213 = lean_ctor_get(x_196, 1);
x_214 = lean_ctor_get(x_196, 2);
x_215 = lean_ctor_get(x_196, 3);
x_216 = 1;
lean_ctor_set(x_196, 3, x_212);
lean_ctor_set(x_196, 2, x_208);
lean_ctor_set(x_196, 1, x_207);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_216);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_215);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_216);
x_217 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_214);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_1, 0, x_196);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_217);
return x_1;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; uint8_t x_224; 
x_218 = lean_ctor_get(x_196, 0);
x_219 = lean_ctor_get(x_196, 1);
x_220 = lean_ctor_get(x_196, 2);
x_221 = lean_ctor_get(x_196, 3);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_196);
x_222 = 1;
x_223 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_223, 0, x_195);
lean_ctor_set(x_223, 1, x_207);
lean_ctor_set(x_223, 2, x_208);
lean_ctor_set(x_223, 3, x_218);
lean_ctor_set_uint8(x_223, sizeof(void*)*4, x_222);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_221);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_222);
x_224 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_220);
lean_ctor_set(x_1, 1, x_219);
lean_ctor_set(x_1, 0, x_223);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_224);
return x_1;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_225 = lean_ctor_get(x_193, 1);
x_226 = lean_ctor_get(x_193, 2);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_193);
x_227 = lean_ctor_get(x_196, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_196, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_196, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_196, 3);
lean_inc(x_230);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 lean_ctor_release(x_196, 2);
 lean_ctor_release(x_196, 3);
 x_231 = x_196;
} else {
 lean_dec_ref(x_196);
 x_231 = lean_box(0);
}
x_232 = 1;
if (lean_is_scalar(x_231)) {
 x_233 = lean_alloc_ctor(1, 4, 1);
} else {
 x_233 = x_231;
}
lean_ctor_set(x_233, 0, x_195);
lean_ctor_set(x_233, 1, x_225);
lean_ctor_set(x_233, 2, x_226);
lean_ctor_set(x_233, 3, x_227);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_232);
x_234 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_234, 0, x_230);
lean_ctor_set(x_234, 1, x_36);
lean_ctor_set(x_234, 2, x_37);
lean_ctor_set(x_234, 3, x_38);
lean_ctor_set_uint8(x_234, sizeof(void*)*4, x_232);
x_235 = 0;
lean_ctor_set(x_1, 3, x_234);
lean_ctor_set(x_1, 2, x_229);
lean_ctor_set(x_1, 1, x_228);
lean_ctor_set(x_1, 0, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_235);
return x_1;
}
}
else
{
uint8_t x_236; 
lean_free_object(x_1);
x_236 = !lean_is_exclusive(x_196);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_237 = lean_ctor_get(x_196, 3);
lean_dec(x_237);
x_238 = lean_ctor_get(x_196, 2);
lean_dec(x_238);
x_239 = lean_ctor_get(x_196, 1);
lean_dec(x_239);
x_240 = lean_ctor_get(x_196, 0);
lean_dec(x_240);
x_241 = 1;
lean_ctor_set(x_196, 3, x_38);
lean_ctor_set(x_196, 2, x_37);
lean_ctor_set(x_196, 1, x_36);
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_241);
return x_196;
}
else
{
uint8_t x_242; lean_object* x_243; 
lean_dec(x_196);
x_242 = 1;
x_243 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_243, 0, x_193);
lean_ctor_set(x_243, 1, x_36);
lean_ctor_set(x_243, 2, x_37);
lean_ctor_set(x_243, 3, x_38);
lean_ctor_set_uint8(x_243, sizeof(void*)*4, x_242);
return x_243;
}
}
}
}
else
{
uint8_t x_244; 
x_244 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_244 == 0)
{
uint8_t x_245; 
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_246 = lean_ctor_get(x_193, 1);
x_247 = lean_ctor_get(x_193, 2);
x_248 = lean_ctor_get(x_193, 3);
x_249 = lean_ctor_get(x_193, 0);
lean_dec(x_249);
x_250 = !lean_is_exclusive(x_195);
if (x_250 == 0)
{
uint8_t x_251; uint8_t x_252; 
x_251 = 1;
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_251);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_248);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_251);
x_252 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_246);
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_252);
return x_1;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_253 = lean_ctor_get(x_195, 0);
x_254 = lean_ctor_get(x_195, 1);
x_255 = lean_ctor_get(x_195, 2);
x_256 = lean_ctor_get(x_195, 3);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_195);
x_257 = 1;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_253);
lean_ctor_set(x_258, 1, x_254);
lean_ctor_set(x_258, 2, x_255);
lean_ctor_set(x_258, 3, x_256);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_193, 3, x_38);
lean_ctor_set(x_193, 2, x_37);
lean_ctor_set(x_193, 1, x_36);
lean_ctor_set(x_193, 0, x_248);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_257);
x_259 = 0;
lean_ctor_set(x_1, 3, x_193);
lean_ctor_set(x_1, 2, x_247);
lean_ctor_set(x_1, 1, x_246);
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_260 = lean_ctor_get(x_193, 1);
x_261 = lean_ctor_get(x_193, 2);
x_262 = lean_ctor_get(x_193, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_193);
x_263 = lean_ctor_get(x_195, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_195, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_195, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_195, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_267 = x_195;
} else {
 lean_dec_ref(x_195);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_263);
lean_ctor_set(x_269, 1, x_264);
lean_ctor_set(x_269, 2, x_265);
lean_ctor_set(x_269, 3, x_266);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_36);
lean_ctor_set(x_270, 2, x_37);
lean_ctor_set(x_270, 3, x_38);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
x_271 = 0;
lean_ctor_set(x_1, 3, x_270);
lean_ctor_set(x_1, 2, x_261);
lean_ctor_set(x_1, 1, x_260);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_271);
return x_1;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_193, 3);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
lean_free_object(x_1);
x_273 = !lean_is_exclusive(x_195);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_195, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_195, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_195, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_195, 0);
lean_dec(x_277);
x_278 = 1;
lean_ctor_set(x_195, 3, x_38);
lean_ctor_set(x_195, 2, x_37);
lean_ctor_set(x_195, 1, x_36);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_278);
return x_195;
}
else
{
uint8_t x_279; lean_object* x_280; 
lean_dec(x_195);
x_279 = 1;
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_193);
lean_ctor_set(x_280, 1, x_36);
lean_ctor_set(x_280, 2, x_37);
lean_ctor_set(x_280, 3, x_38);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_279);
return x_280;
}
}
else
{
uint8_t x_281; 
x_281 = lean_ctor_get_uint8(x_272, sizeof(void*)*4);
if (x_281 == 0)
{
uint8_t x_282; 
lean_free_object(x_1);
x_282 = !lean_is_exclusive(x_193);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_283 = lean_ctor_get(x_193, 1);
x_284 = lean_ctor_get(x_193, 2);
x_285 = lean_ctor_get(x_193, 3);
lean_dec(x_285);
x_286 = lean_ctor_get(x_193, 0);
lean_dec(x_286);
x_287 = !lean_is_exclusive(x_272);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_288 = lean_ctor_get(x_272, 0);
x_289 = lean_ctor_get(x_272, 1);
x_290 = lean_ctor_get(x_272, 2);
x_291 = lean_ctor_get(x_272, 3);
x_292 = 1;
lean_inc(x_195);
lean_ctor_set(x_272, 3, x_288);
lean_ctor_set(x_272, 2, x_284);
lean_ctor_set(x_272, 1, x_283);
lean_ctor_set(x_272, 0, x_195);
x_293 = !lean_is_exclusive(x_195);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_195, 3);
lean_dec(x_294);
x_295 = lean_ctor_get(x_195, 2);
lean_dec(x_295);
x_296 = lean_ctor_get(x_195, 1);
lean_dec(x_296);
x_297 = lean_ctor_get(x_195, 0);
lean_dec(x_297);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_292);
lean_ctor_set(x_195, 3, x_38);
lean_ctor_set(x_195, 2, x_37);
lean_ctor_set(x_195, 1, x_36);
lean_ctor_set(x_195, 0, x_291);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_292);
x_298 = 0;
lean_ctor_set(x_193, 3, x_195);
lean_ctor_set(x_193, 2, x_290);
lean_ctor_set(x_193, 1, x_289);
lean_ctor_set(x_193, 0, x_272);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_298);
return x_193;
}
else
{
lean_object* x_299; uint8_t x_300; 
lean_dec(x_195);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_292);
x_299 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_299, 0, x_291);
lean_ctor_set(x_299, 1, x_36);
lean_ctor_set(x_299, 2, x_37);
lean_ctor_set(x_299, 3, x_38);
lean_ctor_set_uint8(x_299, sizeof(void*)*4, x_292);
x_300 = 0;
lean_ctor_set(x_193, 3, x_299);
lean_ctor_set(x_193, 2, x_290);
lean_ctor_set(x_193, 1, x_289);
lean_ctor_set(x_193, 0, x_272);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_300);
return x_193;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_301 = lean_ctor_get(x_272, 0);
x_302 = lean_ctor_get(x_272, 1);
x_303 = lean_ctor_get(x_272, 2);
x_304 = lean_ctor_get(x_272, 3);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_272);
x_305 = 1;
lean_inc(x_195);
x_306 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_306, 0, x_195);
lean_ctor_set(x_306, 1, x_283);
lean_ctor_set(x_306, 2, x_284);
lean_ctor_set(x_306, 3, x_301);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_307 = x_195;
} else {
 lean_dec_ref(x_195);
 x_307 = lean_box(0);
}
lean_ctor_set_uint8(x_306, sizeof(void*)*4, x_305);
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 4, 1);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_304);
lean_ctor_set(x_308, 1, x_36);
lean_ctor_set(x_308, 2, x_37);
lean_ctor_set(x_308, 3, x_38);
lean_ctor_set_uint8(x_308, sizeof(void*)*4, x_305);
x_309 = 0;
lean_ctor_set(x_193, 3, x_308);
lean_ctor_set(x_193, 2, x_303);
lean_ctor_set(x_193, 1, x_302);
lean_ctor_set(x_193, 0, x_306);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_309);
return x_193;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
x_310 = lean_ctor_get(x_193, 1);
x_311 = lean_ctor_get(x_193, 2);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_193);
x_312 = lean_ctor_get(x_272, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_272, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_272, 2);
lean_inc(x_314);
x_315 = lean_ctor_get(x_272, 3);
lean_inc(x_315);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_316 = x_272;
} else {
 lean_dec_ref(x_272);
 x_316 = lean_box(0);
}
x_317 = 1;
lean_inc(x_195);
if (lean_is_scalar(x_316)) {
 x_318 = lean_alloc_ctor(1, 4, 1);
} else {
 x_318 = x_316;
}
lean_ctor_set(x_318, 0, x_195);
lean_ctor_set(x_318, 1, x_310);
lean_ctor_set(x_318, 2, x_311);
lean_ctor_set(x_318, 3, x_312);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_319 = x_195;
} else {
 lean_dec_ref(x_195);
 x_319 = lean_box(0);
}
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_317);
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 4, 1);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_36);
lean_ctor_set(x_320, 2, x_37);
lean_ctor_set(x_320, 3, x_38);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_317);
x_321 = 0;
x_322 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_322, 0, x_318);
lean_ctor_set(x_322, 1, x_313);
lean_ctor_set(x_322, 2, x_314);
lean_ctor_set(x_322, 3, x_320);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_321);
return x_322;
}
}
else
{
uint8_t x_323; 
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_324 = lean_ctor_get(x_193, 3);
lean_dec(x_324);
x_325 = lean_ctor_get(x_193, 0);
lean_dec(x_325);
x_326 = !lean_is_exclusive(x_195);
if (x_326 == 0)
{
uint8_t x_327; 
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_281);
x_327 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_327);
return x_1;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_328 = lean_ctor_get(x_195, 0);
x_329 = lean_ctor_get(x_195, 1);
x_330 = lean_ctor_get(x_195, 2);
x_331 = lean_ctor_get(x_195, 3);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_195);
x_332 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_332, 0, x_328);
lean_ctor_set(x_332, 1, x_329);
lean_ctor_set(x_332, 2, x_330);
lean_ctor_set(x_332, 3, x_331);
lean_ctor_set_uint8(x_332, sizeof(void*)*4, x_281);
lean_ctor_set(x_193, 0, x_332);
x_333 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_333);
return x_1;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_334 = lean_ctor_get(x_193, 1);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_193);
x_336 = lean_ctor_get(x_195, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_195, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_195, 2);
lean_inc(x_338);
x_339 = lean_ctor_get(x_195, 3);
lean_inc(x_339);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_340 = x_195;
} else {
 lean_dec_ref(x_195);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 4, 1);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_336);
lean_ctor_set(x_341, 1, x_337);
lean_ctor_set(x_341, 2, x_338);
lean_ctor_set(x_341, 3, x_339);
lean_ctor_set_uint8(x_341, sizeof(void*)*4, x_281);
x_342 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_334);
lean_ctor_set(x_342, 2, x_335);
lean_ctor_set(x_342, 3, x_272);
lean_ctor_set_uint8(x_342, sizeof(void*)*4, x_194);
x_343 = 1;
lean_ctor_set(x_1, 0, x_342);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_343);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_344; 
x_344 = 1;
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_344);
return x_1;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_345 = lean_ctor_get(x_1, 0);
x_346 = lean_ctor_get(x_1, 1);
x_347 = lean_ctor_get(x_1, 2);
x_348 = lean_ctor_get(x_1, 3);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_1);
x_349 = lean_nat_dec_lt(x_2, x_346);
if (x_349 == 0)
{
uint8_t x_350; 
x_350 = lean_nat_dec_eq(x_2, x_346);
if (x_350 == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_348, x_2, x_3);
x_352 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_352 == 0)
{
lean_object* x_353; 
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_351, 3);
lean_inc(x_354);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; 
x_355 = lean_ctor_get(x_351, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_351, 2);
lean_inc(x_356);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_357 = x_351;
} else {
 lean_dec_ref(x_351);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 4, 1);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_354);
lean_ctor_set(x_358, 1, x_355);
lean_ctor_set(x_358, 2, x_356);
lean_ctor_set(x_358, 3, x_354);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_352);
x_359 = 1;
x_360 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_360, 0, x_345);
lean_ctor_set(x_360, 1, x_346);
lean_ctor_set(x_360, 2, x_347);
lean_ctor_set(x_360, 3, x_358);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
return x_360;
}
else
{
uint8_t x_361; 
x_361 = lean_ctor_get_uint8(x_354, sizeof(void*)*4);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_362 = lean_ctor_get(x_351, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_351, 2);
lean_inc(x_363);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_364 = x_351;
} else {
 lean_dec_ref(x_351);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_354, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_354, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_354, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_354, 3);
lean_inc(x_368);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_369 = x_354;
} else {
 lean_dec_ref(x_354);
 x_369 = lean_box(0);
}
x_370 = 1;
if (lean_is_scalar(x_369)) {
 x_371 = lean_alloc_ctor(1, 4, 1);
} else {
 x_371 = x_369;
}
lean_ctor_set(x_371, 0, x_345);
lean_ctor_set(x_371, 1, x_346);
lean_ctor_set(x_371, 2, x_347);
lean_ctor_set(x_371, 3, x_353);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_370);
if (lean_is_scalar(x_364)) {
 x_372 = lean_alloc_ctor(1, 4, 1);
} else {
 x_372 = x_364;
}
lean_ctor_set(x_372, 0, x_365);
lean_ctor_set(x_372, 1, x_366);
lean_ctor_set(x_372, 2, x_367);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set_uint8(x_372, sizeof(void*)*4, x_370);
x_373 = 0;
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_362);
lean_ctor_set(x_374, 2, x_363);
lean_ctor_set(x_374, 3, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
else
{
lean_object* x_375; uint8_t x_376; lean_object* x_377; 
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 lean_ctor_release(x_354, 2);
 lean_ctor_release(x_354, 3);
 x_375 = x_354;
} else {
 lean_dec_ref(x_354);
 x_375 = lean_box(0);
}
x_376 = 1;
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_345);
lean_ctor_set(x_377, 1, x_346);
lean_ctor_set(x_377, 2, x_347);
lean_ctor_set(x_377, 3, x_351);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_376);
return x_377;
}
}
}
else
{
uint8_t x_378; 
x_378 = lean_ctor_get_uint8(x_353, sizeof(void*)*4);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; 
x_379 = lean_ctor_get(x_351, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_351, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_351, 3);
lean_inc(x_381);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_382 = x_351;
} else {
 lean_dec_ref(x_351);
 x_382 = lean_box(0);
}
x_383 = lean_ctor_get(x_353, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_353, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_353, 2);
lean_inc(x_385);
x_386 = lean_ctor_get(x_353, 3);
lean_inc(x_386);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_387 = x_353;
} else {
 lean_dec_ref(x_353);
 x_387 = lean_box(0);
}
x_388 = 1;
if (lean_is_scalar(x_387)) {
 x_389 = lean_alloc_ctor(1, 4, 1);
} else {
 x_389 = x_387;
}
lean_ctor_set(x_389, 0, x_345);
lean_ctor_set(x_389, 1, x_346);
lean_ctor_set(x_389, 2, x_347);
lean_ctor_set(x_389, 3, x_383);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
if (lean_is_scalar(x_382)) {
 x_390 = lean_alloc_ctor(1, 4, 1);
} else {
 x_390 = x_382;
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_379);
lean_ctor_set(x_390, 2, x_380);
lean_ctor_set(x_390, 3, x_381);
lean_ctor_set_uint8(x_390, sizeof(void*)*4, x_388);
x_391 = 0;
x_392 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_384);
lean_ctor_set(x_392, 2, x_385);
lean_ctor_set(x_392, 3, x_390);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
lean_object* x_393; 
x_393 = lean_ctor_get(x_351, 3);
lean_inc(x_393);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; uint8_t x_395; lean_object* x_396; 
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_394 = x_353;
} else {
 lean_dec_ref(x_353);
 x_394 = lean_box(0);
}
x_395 = 1;
if (lean_is_scalar(x_394)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_394;
}
lean_ctor_set(x_396, 0, x_345);
lean_ctor_set(x_396, 1, x_346);
lean_ctor_set(x_396, 2, x_347);
lean_ctor_set(x_396, 3, x_351);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_395);
return x_396;
}
else
{
uint8_t x_397; 
x_397 = lean_ctor_get_uint8(x_393, sizeof(void*)*4);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; lean_object* x_411; 
x_398 = lean_ctor_get(x_351, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_351, 2);
lean_inc(x_399);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_400 = x_351;
} else {
 lean_dec_ref(x_351);
 x_400 = lean_box(0);
}
x_401 = lean_ctor_get(x_393, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_393, 1);
lean_inc(x_402);
x_403 = lean_ctor_get(x_393, 2);
lean_inc(x_403);
x_404 = lean_ctor_get(x_393, 3);
lean_inc(x_404);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 lean_ctor_release(x_393, 2);
 lean_ctor_release(x_393, 3);
 x_405 = x_393;
} else {
 lean_dec_ref(x_393);
 x_405 = lean_box(0);
}
x_406 = 1;
lean_inc(x_353);
if (lean_is_scalar(x_405)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_405;
}
lean_ctor_set(x_407, 0, x_345);
lean_ctor_set(x_407, 1, x_346);
lean_ctor_set(x_407, 2, x_347);
lean_ctor_set(x_407, 3, x_353);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_408 = x_353;
} else {
 lean_dec_ref(x_353);
 x_408 = lean_box(0);
}
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_401);
lean_ctor_set(x_409, 1, x_402);
lean_ctor_set(x_409, 2, x_403);
lean_ctor_set(x_409, 3, x_404);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_406);
x_410 = 0;
if (lean_is_scalar(x_400)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_400;
}
lean_ctor_set(x_411, 0, x_407);
lean_ctor_set(x_411, 1, x_398);
lean_ctor_set(x_411, 2, x_399);
lean_ctor_set(x_411, 3, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_410);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; 
x_412 = lean_ctor_get(x_351, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_351, 2);
lean_inc(x_413);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_414 = x_351;
} else {
 lean_dec_ref(x_351);
 x_414 = lean_box(0);
}
x_415 = lean_ctor_get(x_353, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_353, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_353, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_353, 3);
lean_inc(x_418);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 lean_ctor_release(x_353, 2);
 lean_ctor_release(x_353, 3);
 x_419 = x_353;
} else {
 lean_dec_ref(x_353);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 4, 1);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_415);
lean_ctor_set(x_420, 1, x_416);
lean_ctor_set(x_420, 2, x_417);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_397);
if (lean_is_scalar(x_414)) {
 x_421 = lean_alloc_ctor(1, 4, 1);
} else {
 x_421 = x_414;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_412);
lean_ctor_set(x_421, 2, x_413);
lean_ctor_set(x_421, 3, x_393);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_352);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_345);
lean_ctor_set(x_423, 1, x_346);
lean_ctor_set(x_423, 2, x_347);
lean_ctor_set(x_423, 3, x_421);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
}
}
}
}
else
{
uint8_t x_424; lean_object* x_425; 
x_424 = 1;
x_425 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_425, 0, x_345);
lean_ctor_set(x_425, 1, x_346);
lean_ctor_set(x_425, 2, x_347);
lean_ctor_set(x_425, 3, x_351);
lean_ctor_set_uint8(x_425, sizeof(void*)*4, x_424);
return x_425;
}
}
else
{
uint8_t x_426; lean_object* x_427; 
lean_dec(x_347);
lean_dec(x_346);
x_426 = 1;
x_427 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_427, 0, x_345);
lean_ctor_set(x_427, 1, x_2);
lean_ctor_set(x_427, 2, x_3);
lean_ctor_set(x_427, 3, x_348);
lean_ctor_set_uint8(x_427, sizeof(void*)*4, x_426);
return x_427;
}
}
else
{
lean_object* x_428; uint8_t x_429; 
x_428 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_345, x_2, x_3);
x_429 = lean_ctor_get_uint8(x_428, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_428, 0);
lean_inc(x_430);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_428, 3);
lean_inc(x_431);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; 
x_432 = lean_ctor_get(x_428, 1);
lean_inc(x_432);
x_433 = lean_ctor_get(x_428, 2);
lean_inc(x_433);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_434 = x_428;
} else {
 lean_dec_ref(x_428);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_431);
lean_ctor_set(x_435, 1, x_432);
lean_ctor_set(x_435, 2, x_433);
lean_ctor_set(x_435, 3, x_431);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_429);
x_436 = 1;
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_346);
lean_ctor_set(x_437, 2, x_347);
lean_ctor_set(x_437, 3, x_348);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_436);
return x_437;
}
else
{
uint8_t x_438; 
x_438 = lean_ctor_get_uint8(x_431, sizeof(void*)*4);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; 
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 2);
lean_inc(x_440);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_441 = x_428;
} else {
 lean_dec_ref(x_428);
 x_441 = lean_box(0);
}
x_442 = lean_ctor_get(x_431, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_431, 1);
lean_inc(x_443);
x_444 = lean_ctor_get(x_431, 2);
lean_inc(x_444);
x_445 = lean_ctor_get(x_431, 3);
lean_inc(x_445);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_446 = x_431;
} else {
 lean_dec_ref(x_431);
 x_446 = lean_box(0);
}
x_447 = 1;
if (lean_is_scalar(x_446)) {
 x_448 = lean_alloc_ctor(1, 4, 1);
} else {
 x_448 = x_446;
}
lean_ctor_set(x_448, 0, x_430);
lean_ctor_set(x_448, 1, x_439);
lean_ctor_set(x_448, 2, x_440);
lean_ctor_set(x_448, 3, x_442);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(1, 4, 1);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_445);
lean_ctor_set(x_449, 1, x_346);
lean_ctor_set(x_449, 2, x_347);
lean_ctor_set(x_449, 3, x_348);
lean_ctor_set_uint8(x_449, sizeof(void*)*4, x_447);
x_450 = 0;
x_451 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_443);
lean_ctor_set(x_451, 2, x_444);
lean_ctor_set(x_451, 3, x_449);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
return x_451;
}
else
{
lean_object* x_452; uint8_t x_453; lean_object* x_454; 
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 lean_ctor_release(x_431, 2);
 lean_ctor_release(x_431, 3);
 x_452 = x_431;
} else {
 lean_dec_ref(x_431);
 x_452 = lean_box(0);
}
x_453 = 1;
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_428);
lean_ctor_set(x_454, 1, x_346);
lean_ctor_set(x_454, 2, x_347);
lean_ctor_set(x_454, 3, x_348);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
return x_454;
}
}
}
else
{
uint8_t x_455; 
x_455 = lean_ctor_get_uint8(x_430, sizeof(void*)*4);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; lean_object* x_469; 
x_456 = lean_ctor_get(x_428, 1);
lean_inc(x_456);
x_457 = lean_ctor_get(x_428, 2);
lean_inc(x_457);
x_458 = lean_ctor_get(x_428, 3);
lean_inc(x_458);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_459 = x_428;
} else {
 lean_dec_ref(x_428);
 x_459 = lean_box(0);
}
x_460 = lean_ctor_get(x_430, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_430, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_430, 2);
lean_inc(x_462);
x_463 = lean_ctor_get(x_430, 3);
lean_inc(x_463);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_464 = x_430;
} else {
 lean_dec_ref(x_430);
 x_464 = lean_box(0);
}
x_465 = 1;
if (lean_is_scalar(x_464)) {
 x_466 = lean_alloc_ctor(1, 4, 1);
} else {
 x_466 = x_464;
}
lean_ctor_set(x_466, 0, x_460);
lean_ctor_set(x_466, 1, x_461);
lean_ctor_set(x_466, 2, x_462);
lean_ctor_set(x_466, 3, x_463);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
if (lean_is_scalar(x_459)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_459;
}
lean_ctor_set(x_467, 0, x_458);
lean_ctor_set(x_467, 1, x_346);
lean_ctor_set(x_467, 2, x_347);
lean_ctor_set(x_467, 3, x_348);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_465);
x_468 = 0;
x_469 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_456);
lean_ctor_set(x_469, 2, x_457);
lean_ctor_set(x_469, 3, x_467);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_428, 3);
lean_inc(x_470);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; uint8_t x_472; lean_object* x_473; 
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_471 = x_430;
} else {
 lean_dec_ref(x_430);
 x_471 = lean_box(0);
}
x_472 = 1;
if (lean_is_scalar(x_471)) {
 x_473 = lean_alloc_ctor(1, 4, 1);
} else {
 x_473 = x_471;
}
lean_ctor_set(x_473, 0, x_428);
lean_ctor_set(x_473, 1, x_346);
lean_ctor_set(x_473, 2, x_347);
lean_ctor_set(x_473, 3, x_348);
lean_ctor_set_uint8(x_473, sizeof(void*)*4, x_472);
return x_473;
}
else
{
uint8_t x_474; 
x_474 = lean_ctor_get_uint8(x_470, sizeof(void*)*4);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; 
x_475 = lean_ctor_get(x_428, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_428, 2);
lean_inc(x_476);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_477 = x_428;
} else {
 lean_dec_ref(x_428);
 x_477 = lean_box(0);
}
x_478 = lean_ctor_get(x_470, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_470, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_470, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_470, 3);
lean_inc(x_481);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 lean_ctor_release(x_470, 2);
 lean_ctor_release(x_470, 3);
 x_482 = x_470;
} else {
 lean_dec_ref(x_470);
 x_482 = lean_box(0);
}
x_483 = 1;
lean_inc(x_430);
if (lean_is_scalar(x_482)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_482;
}
lean_ctor_set(x_484, 0, x_430);
lean_ctor_set(x_484, 1, x_475);
lean_ctor_set(x_484, 2, x_476);
lean_ctor_set(x_484, 3, x_478);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_485 = x_430;
} else {
 lean_dec_ref(x_430);
 x_485 = lean_box(0);
}
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 4, 1);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_346);
lean_ctor_set(x_486, 2, x_347);
lean_ctor_set(x_486, 3, x_348);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_483);
x_487 = 0;
if (lean_is_scalar(x_477)) {
 x_488 = lean_alloc_ctor(1, 4, 1);
} else {
 x_488 = x_477;
}
lean_ctor_set(x_488, 0, x_484);
lean_ctor_set(x_488, 1, x_479);
lean_ctor_set(x_488, 2, x_480);
lean_ctor_set(x_488, 3, x_486);
lean_ctor_set_uint8(x_488, sizeof(void*)*4, x_487);
return x_488;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; lean_object* x_500; 
x_489 = lean_ctor_get(x_428, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_428, 2);
lean_inc(x_490);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_491 = x_428;
} else {
 lean_dec_ref(x_428);
 x_491 = lean_box(0);
}
x_492 = lean_ctor_get(x_430, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_430, 1);
lean_inc(x_493);
x_494 = lean_ctor_get(x_430, 2);
lean_inc(x_494);
x_495 = lean_ctor_get(x_430, 3);
lean_inc(x_495);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 x_496 = x_430;
} else {
 lean_dec_ref(x_430);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 4, 1);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_492);
lean_ctor_set(x_497, 1, x_493);
lean_ctor_set(x_497, 2, x_494);
lean_ctor_set(x_497, 3, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_474);
if (lean_is_scalar(x_491)) {
 x_498 = lean_alloc_ctor(1, 4, 1);
} else {
 x_498 = x_491;
}
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_489);
lean_ctor_set(x_498, 2, x_490);
lean_ctor_set(x_498, 3, x_470);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_429);
x_499 = 1;
x_500 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_346);
lean_ctor_set(x_500, 2, x_347);
lean_ctor_set(x_500, 3, x_348);
lean_ctor_set_uint8(x_500, sizeof(void*)*4, x_499);
return x_500;
}
}
}
}
}
else
{
uint8_t x_501; lean_object* x_502; 
x_501 = 1;
x_502 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_502, 0, x_428);
lean_ctor_set(x_502, 1, x_346);
lean_ctor_set(x_502, 2, x_347);
lean_ctor_set(x_502, 3, x_348);
lean_ctor_set_uint8(x_502, sizeof(void*)*4, x_501);
return x_502;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lean_IR_addVarRename___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at_Lean_IR_addVarRename___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_1, x_2, x_3);
return x_5;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = l_Lean_IR_IRType_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
x_4 = x_16;
goto block_9;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
x_4 = x_20;
goto block_9;
}
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Lean_IR_addVarRename(x_1, x_5, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_IR_addParamsRename___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_20; uint8_t x_21; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_5, x_13);
lean_dec(x_5);
x_20 = lean_nat_dec_lt(x_6, x_3);
x_21 = lean_nat_dec_lt(x_6, x_4);
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_IR_instInhabitedParam;
x_23 = l___private_Init_Util_0__outOfBounds___rarg(x_22);
if (x_21 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l___private_Init_Util_0__outOfBounds___rarg(x_22);
x_25 = l_Lean_IR_addParamRename(x_9, x_23, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_6);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_15 = x_28;
goto block_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_array_fget(x_2, x_6);
x_30 = l_Lean_IR_addParamRename(x_9, x_23, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_14);
lean_dec(x_6);
x_31 = lean_box(0);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_15 = x_33;
goto block_19;
}
}
}
else
{
lean_object* x_34; 
x_34 = lean_array_fget(x_1, x_6);
if (x_21 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lean_IR_instInhabitedParam;
x_36 = l___private_Init_Util_0__outOfBounds___rarg(x_35);
x_37 = l_Lean_IR_addParamRename(x_9, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_14);
lean_dec(x_6);
x_38 = lean_box(0);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_15 = x_40;
goto block_19;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_array_fget(x_2, x_6);
x_42 = l_Lean_IR_addParamRename(x_9, x_34, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec(x_14);
lean_dec(x_6);
x_43 = lean_box(0);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_15 = x_45;
goto block_19;
}
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_5 = x_14;
x_6 = x_17;
x_9 = x_16;
goto _start;
}
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_9);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_6);
lean_dec(x_5);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_9);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
x_10 = l_Std_Range_forIn_loop___at_Lean_IR_addParamsRename___spec__1(x_2, x_3, x_4, x_5, x_4, x_8, x_4, x_9, x_1);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_IR_addParamsRename___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Range_forIn_loop___at_Lean_IR_addParamsRename___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addParamsRename(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_IR_FnBody_alphaEqv___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_5, x_7);
x_12 = lean_array_fget(x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_IR_CtorInfo_beq(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
lean_inc(x_1);
x_19 = l_Lean_IR_FnBody_alphaEqv(x_1, x_14, x_16);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
x_4 = lean_box(0);
x_7 = x_22;
goto _start;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_24 = 0;
return x_24;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_25 = 0;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
lean_inc(x_1);
x_28 = l_Lean_IR_FnBody_alphaEqv(x_1, x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_1);
x_29 = 0;
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_7, x_30);
lean_dec(x_7);
x_4 = lean_box(0);
x_7 = x_31;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Lean_IR_IRType_beq(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_Lean_IR_Expr_alphaEqv(x_1, x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_15 = 0;
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_IR_addVarRename(x_1, x_4, x_8);
x_1 = x_16;
x_2 = x_7;
x_3 = x_11;
goto _start;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 3);
lean_inc(x_26);
lean_dec(x_3);
lean_inc(x_1);
x_27 = l_Lean_IR_addParamsRename(x_1, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
x_28 = 0;
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_IR_FnBody_alphaEqv(x_29, x_21, x_25);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_1);
x_31 = 0;
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_IR_addVarRename(x_1, x_19, x_23);
x_1 = x_32;
x_2 = x_22;
x_3 = x_26;
goto _start;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = 0;
return x_34;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 3);
lean_inc(x_42);
lean_dec(x_3);
x_43 = l_Lean_IR_VarId_alphaEqv(x_1, x_35, x_39);
lean_dec(x_39);
lean_dec(x_35);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_1);
x_44 = 0;
return x_44;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_eq(x_36, x_40);
lean_dec(x_40);
lean_dec(x_36);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
x_46 = 0;
return x_46;
}
else
{
uint8_t x_47; 
x_47 = l_Lean_IR_Arg_alphaEqv(x_1, x_37, x_41);
lean_dec(x_41);
lean_dec(x_37);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_1);
x_48 = 0;
return x_48;
}
else
{
x_2 = x_38;
x_3 = x_42;
goto _start;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = 0;
return x_50;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
lean_dec(x_2);
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 2);
lean_inc(x_56);
lean_dec(x_3);
x_57 = l_Lean_IR_VarId_alphaEqv(x_1, x_51, x_54);
lean_dec(x_54);
lean_dec(x_51);
if (x_57 == 0)
{
uint8_t x_58; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_58 = 0;
return x_58;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_eq(x_52, x_55);
lean_dec(x_55);
lean_dec(x_52);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_1);
x_60 = 0;
return x_60;
}
else
{
x_2 = x_53;
x_3 = x_56;
goto _start;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = 0;
return x_62;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 3);
lean_inc(x_66);
lean_dec(x_2);
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_dec(x_3);
x_71 = l_Lean_IR_VarId_alphaEqv(x_1, x_63, x_67);
lean_dec(x_67);
lean_dec(x_63);
if (x_71 == 0)
{
uint8_t x_72; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_1);
x_72 = 0;
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_eq(x_64, x_68);
lean_dec(x_68);
lean_dec(x_64);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_1);
x_74 = 0;
return x_74;
}
else
{
uint8_t x_75; 
x_75 = l_Lean_IR_VarId_alphaEqv(x_1, x_65, x_69);
lean_dec(x_69);
lean_dec(x_65);
if (x_75 == 0)
{
uint8_t x_76; 
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_1);
x_76 = 0;
return x_76;
}
else
{
x_2 = x_66;
x_3 = x_70;
goto _start;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = 0;
return x_78;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 5);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_3, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_3, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_3, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 5);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l_Lean_IR_VarId_alphaEqv(x_1, x_79, x_85);
lean_dec(x_85);
lean_dec(x_79);
if (x_91 == 0)
{
uint8_t x_92; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_1);
x_92 = 0;
return x_92;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_eq(x_80, x_86);
lean_dec(x_86);
lean_dec(x_80);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_1);
x_94 = 0;
return x_94;
}
else
{
uint8_t x_95; 
x_95 = lean_nat_dec_eq(x_81, x_87);
lean_dec(x_87);
lean_dec(x_81);
if (x_95 == 0)
{
uint8_t x_96; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_1);
x_96 = 0;
return x_96;
}
else
{
uint8_t x_97; 
x_97 = l_Lean_IR_VarId_alphaEqv(x_1, x_82, x_88);
lean_dec(x_88);
lean_dec(x_82);
if (x_97 == 0)
{
uint8_t x_98; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_1);
x_98 = 0;
return x_98;
}
else
{
uint8_t x_99; 
x_99 = l_Lean_IR_IRType_beq(x_83, x_89);
lean_dec(x_89);
lean_dec(x_83);
if (x_99 == 0)
{
uint8_t x_100; 
lean_dec(x_90);
lean_dec(x_84);
lean_dec(x_1);
x_100 = 0;
return x_100;
}
else
{
x_2 = x_84;
x_3 = x_90;
goto _start;
}
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = 0;
return x_102;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; uint8_t x_119; 
x_103 = lean_ctor_get(x_2, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_106 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
lean_dec(x_2);
x_108 = lean_ctor_get(x_3, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_3, 1);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_111 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_112 = lean_ctor_get(x_3, 2);
lean_inc(x_112);
lean_dec(x_3);
x_119 = l_Lean_IR_VarId_alphaEqv(x_1, x_103, x_108);
lean_dec(x_108);
lean_dec(x_103);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_112);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_1);
x_120 = 0;
return x_120;
}
else
{
uint8_t x_121; 
x_121 = lean_nat_dec_eq(x_104, x_109);
lean_dec(x_109);
lean_dec(x_104);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_122 = 0;
return x_122;
}
else
{
if (x_105 == 0)
{
if (x_110 == 0)
{
lean_object* x_123; 
x_123 = lean_box(0);
x_113 = x_123;
goto block_118;
}
else
{
uint8_t x_124; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_124 = 0;
return x_124;
}
}
else
{
if (x_110 == 0)
{
uint8_t x_125; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_125 = 0;
return x_125;
}
else
{
lean_object* x_126; 
x_126 = lean_box(0);
x_113 = x_126;
goto block_118;
}
}
}
}
block_118:
{
lean_dec(x_113);
if (x_106 == 0)
{
if (x_111 == 0)
{
x_2 = x_107;
x_3 = x_112;
goto _start;
}
else
{
uint8_t x_115; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_115 = 0;
return x_115;
}
}
else
{
if (x_111 == 0)
{
uint8_t x_116; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_116 = 0;
return x_116;
}
else
{
x_2 = x_107;
x_3 = x_112;
goto _start;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = 0;
return x_127;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; uint8_t x_144; 
x_128 = lean_ctor_get(x_2, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_132 = lean_ctor_get(x_2, 2);
lean_inc(x_132);
lean_dec(x_2);
x_133 = lean_ctor_get(x_3, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
x_135 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_136 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_137 = lean_ctor_get(x_3, 2);
lean_inc(x_137);
lean_dec(x_3);
x_144 = l_Lean_IR_VarId_alphaEqv(x_1, x_128, x_133);
lean_dec(x_133);
lean_dec(x_128);
if (x_144 == 0)
{
uint8_t x_145; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_1);
x_145 = 0;
return x_145;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_eq(x_129, x_134);
lean_dec(x_134);
lean_dec(x_129);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_137);
lean_dec(x_132);
lean_dec(x_1);
x_147 = 0;
return x_147;
}
else
{
if (x_130 == 0)
{
if (x_135 == 0)
{
lean_object* x_148; 
x_148 = lean_box(0);
x_138 = x_148;
goto block_143;
}
else
{
uint8_t x_149; 
lean_dec(x_137);
lean_dec(x_132);
lean_dec(x_1);
x_149 = 0;
return x_149;
}
}
else
{
if (x_135 == 0)
{
uint8_t x_150; 
lean_dec(x_137);
lean_dec(x_132);
lean_dec(x_1);
x_150 = 0;
return x_150;
}
else
{
lean_object* x_151; 
x_151 = lean_box(0);
x_138 = x_151;
goto block_143;
}
}
}
}
block_143:
{
lean_dec(x_138);
if (x_131 == 0)
{
if (x_136 == 0)
{
x_2 = x_132;
x_3 = x_137;
goto _start;
}
else
{
uint8_t x_140; 
lean_dec(x_137);
lean_dec(x_132);
lean_dec(x_1);
x_140 = 0;
return x_140;
}
}
else
{
if (x_136 == 0)
{
uint8_t x_141; 
lean_dec(x_137);
lean_dec(x_132);
lean_dec(x_1);
x_141 = 0;
return x_141;
}
else
{
x_2 = x_132;
x_3 = x_137;
goto _start;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = 0;
return x_152;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_153 = lean_ctor_get(x_2, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_2, 1);
lean_inc(x_154);
lean_dec(x_2);
x_155 = lean_ctor_get(x_3, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_3, 1);
lean_inc(x_156);
lean_dec(x_3);
x_157 = l_Lean_IR_VarId_alphaEqv(x_1, x_153, x_155);
lean_dec(x_155);
lean_dec(x_153);
if (x_157 == 0)
{
uint8_t x_158; 
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_1);
x_158 = 0;
return x_158;
}
else
{
x_2 = x_154;
x_3 = x_156;
goto _start;
}
}
else
{
uint8_t x_160; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = 0;
return x_160;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_161 = lean_ctor_get(x_2, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_2, 1);
lean_inc(x_162);
lean_dec(x_2);
x_163 = lean_ctor_get(x_3, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_3, 1);
lean_inc(x_164);
lean_dec(x_3);
x_165 = l_Lean_KVMap_eqv(x_161, x_163);
if (x_165 == 0)
{
uint8_t x_166; 
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_1);
x_166 = 0;
return x_166;
}
else
{
x_2 = x_162;
x_3 = x_164;
goto _start;
}
}
else
{
uint8_t x_168; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = 0;
return x_168;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_169 = lean_ctor_get(x_2, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_2, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_2, 3);
lean_inc(x_171);
lean_dec(x_2);
x_172 = lean_ctor_get(x_3, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_3, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_3, 3);
lean_inc(x_174);
lean_dec(x_3);
x_175 = lean_name_eq(x_169, x_172);
lean_dec(x_172);
lean_dec(x_169);
if (x_175 == 0)
{
uint8_t x_176; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_1);
x_176 = 0;
return x_176;
}
else
{
uint8_t x_177; 
x_177 = l_Lean_IR_VarId_alphaEqv(x_1, x_170, x_173);
lean_dec(x_173);
lean_dec(x_170);
if (x_177 == 0)
{
uint8_t x_178; 
lean_dec(x_174);
lean_dec(x_171);
lean_dec(x_1);
x_178 = 0;
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_array_get_size(x_171);
x_180 = lean_array_get_size(x_174);
x_181 = lean_nat_dec_eq(x_179, x_180);
lean_dec(x_180);
lean_dec(x_179);
if (x_181 == 0)
{
uint8_t x_182; 
lean_dec(x_174);
lean_dec(x_171);
lean_dec(x_1);
x_182 = 0;
return x_182;
}
else
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Array_isEqvAux___at_Lean_IR_FnBody_alphaEqv___spec__1(x_1, x_171, x_174, lean_box(0), x_171, x_174, x_183);
lean_dec(x_174);
lean_dec(x_171);
return x_184;
}
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = 0;
return x_185;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_2, 0);
lean_inc(x_186);
lean_dec(x_2);
x_187 = lean_ctor_get(x_3, 0);
lean_inc(x_187);
lean_dec(x_3);
x_188 = l_Lean_IR_Arg_alphaEqv(x_1, x_186, x_187);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_1);
return x_188;
}
else
{
uint8_t x_189; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = 0;
return x_189;
}
}
case 12:
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_190 = lean_ctor_get(x_2, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_2, 1);
lean_inc(x_191);
lean_dec(x_2);
x_192 = lean_ctor_get(x_3, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_3, 1);
lean_inc(x_193);
lean_dec(x_3);
x_194 = lean_nat_dec_eq(x_190, x_192);
lean_dec(x_192);
lean_dec(x_190);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_1);
x_195 = 0;
return x_195;
}
else
{
uint8_t x_196; 
x_196 = l_Lean_IR_args_alphaEqv(x_1, x_191, x_193);
lean_dec(x_193);
lean_dec(x_191);
lean_dec(x_1);
return x_196;
}
}
else
{
uint8_t x_197; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = 0;
return x_197;
}
}
default: 
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 13)
{
uint8_t x_198; 
x_198 = 1;
return x_198;
}
else
{
uint8_t x_199; 
lean_dec(x_3);
x_199 = 0;
return x_199;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_IR_FnBody_alphaEqv___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___at_Lean_IR_FnBody_alphaEqv___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_FnBody_alphaEqv(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_IR_FnBody_alphaEqv(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_FnBody_beq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instBEqFnBody___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_FnBody_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instBEqFnBody() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instBEqFnBody___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedVarIdSet() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_mkIf___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkIf___closed__1;
x_2 = l_Lean_IR_mkIf___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkIf___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkIf___closed__1;
x_2 = l_Lean_IR_mkIf___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_mkIf___closed__7;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lean_IR_mkIf___closed__5;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lean_IR_mkIf___closed__8;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Lean_IR_mkIf___closed__9;
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_IR_mkIf___closed__2;
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_float", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_uint32", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_uint64", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean_unbox_usize", 16);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_IR_getUnboxOpName___closed__1;
return x_2;
}
case 3:
{
lean_object* x_3; 
x_3 = l_Lean_IR_getUnboxOpName___closed__3;
return x_3;
}
case 4:
{
lean_object* x_4; 
x_4 = l_Lean_IR_getUnboxOpName___closed__4;
return x_4;
}
case 5:
{
lean_object* x_5; 
x_5 = l_Lean_IR_getUnboxOpName___closed__5;
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = l_Lean_IR_getUnboxOpName___closed__2;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_getUnboxOpName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_instInhabitedVarId = _init_l_Lean_IR_instInhabitedVarId();
lean_mark_persistent(l_Lean_IR_instInhabitedVarId);
l_Lean_IR_instInhabitedJoinPointId = _init_l_Lean_IR_instInhabitedJoinPointId();
lean_mark_persistent(l_Lean_IR_instInhabitedJoinPointId);
l_Lean_IR_instToStringVarId___closed__1 = _init_l_Lean_IR_instToStringVarId___closed__1();
lean_mark_persistent(l_Lean_IR_instToStringVarId___closed__1);
l_Lean_IR_instToStringJoinPointId___closed__1 = _init_l_Lean_IR_instToStringJoinPointId___closed__1();
lean_mark_persistent(l_Lean_IR_instToStringJoinPointId___closed__1);
l_Lean_IR_MData_empty = _init_l_Lean_IR_MData_empty();
lean_mark_persistent(l_Lean_IR_MData_empty);
l_Lean_IR_instInhabitedIRType = _init_l_Lean_IR_instInhabitedIRType();
lean_mark_persistent(l_Lean_IR_instInhabitedIRType);
l_Lean_IR_IRType_instBEqIRType___closed__1 = _init_l_Lean_IR_IRType_instBEqIRType___closed__1();
lean_mark_persistent(l_Lean_IR_IRType_instBEqIRType___closed__1);
l_Lean_IR_IRType_instBEqIRType = _init_l_Lean_IR_IRType_instBEqIRType();
lean_mark_persistent(l_Lean_IR_IRType_instBEqIRType);
l_Lean_IR_instInhabitedArg___closed__1 = _init_l_Lean_IR_instInhabitedArg___closed__1();
lean_mark_persistent(l_Lean_IR_instInhabitedArg___closed__1);
l_Lean_IR_instInhabitedArg = _init_l_Lean_IR_instInhabitedArg();
lean_mark_persistent(l_Lean_IR_instInhabitedArg);
l_Lean_IR_instBEqArg___closed__1 = _init_l_Lean_IR_instBEqArg___closed__1();
lean_mark_persistent(l_Lean_IR_instBEqArg___closed__1);
l_Lean_IR_instBEqArg = _init_l_Lean_IR_instBEqArg();
lean_mark_persistent(l_Lean_IR_instBEqArg);
l_Lean_IR_instBEqLitVal___closed__1 = _init_l_Lean_IR_instBEqLitVal___closed__1();
lean_mark_persistent(l_Lean_IR_instBEqLitVal___closed__1);
l_Lean_IR_instBEqLitVal = _init_l_Lean_IR_instBEqLitVal();
lean_mark_persistent(l_Lean_IR_instBEqLitVal);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__1 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__1);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__2 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__2);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__3 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__3);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__4 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__4();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__4);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__5 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__5();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__5);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__6 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__6();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__6);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__7 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__7();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__7);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__8 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__8();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__8);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__9 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__9();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__9);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__10 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__10();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__10);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__11 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__11();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__11);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__12 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__12();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__12);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__13 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__13();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__13);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__14 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__14();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__14);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__15 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__15();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__15);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__16 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__16();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__16);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__17 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__17();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__17);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__18 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__18();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__18);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__19 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__19();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__19);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__20 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__20();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__20);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__21 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__21();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__21);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__22 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__22();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__22);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__23 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__23();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__23);
l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__24 = _init_l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__24();
lean_mark_persistent(l___private_Lean_Compiler_IR_Basic_0__Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1031____closed__24);
l_Lean_IR_instReprCtorInfo___closed__1 = _init_l_Lean_IR_instReprCtorInfo___closed__1();
lean_mark_persistent(l_Lean_IR_instReprCtorInfo___closed__1);
l_Lean_IR_instReprCtorInfo = _init_l_Lean_IR_instReprCtorInfo();
lean_mark_persistent(l_Lean_IR_instReprCtorInfo);
l_Lean_IR_instBEqCtorInfo___closed__1 = _init_l_Lean_IR_instBEqCtorInfo___closed__1();
lean_mark_persistent(l_Lean_IR_instBEqCtorInfo___closed__1);
l_Lean_IR_instBEqCtorInfo = _init_l_Lean_IR_instBEqCtorInfo();
lean_mark_persistent(l_Lean_IR_instBEqCtorInfo);
l_Lean_IR_instInhabitedParam___closed__1 = _init_l_Lean_IR_instInhabitedParam___closed__1();
lean_mark_persistent(l_Lean_IR_instInhabitedParam___closed__1);
l_Lean_IR_instInhabitedParam = _init_l_Lean_IR_instInhabitedParam();
lean_mark_persistent(l_Lean_IR_instInhabitedParam);
l_Lean_IR_instInhabitedFnBody = _init_l_Lean_IR_instInhabitedFnBody();
lean_mark_persistent(l_Lean_IR_instInhabitedFnBody);
l_Lean_IR_FnBody_nil = _init_l_Lean_IR_FnBody_nil();
lean_mark_persistent(l_Lean_IR_FnBody_nil);
l_Lean_IR_instInhabitedAlt___closed__1 = _init_l_Lean_IR_instInhabitedAlt___closed__1();
lean_mark_persistent(l_Lean_IR_instInhabitedAlt___closed__1);
l_Lean_IR_instInhabitedAlt = _init_l_Lean_IR_instInhabitedAlt();
lean_mark_persistent(l_Lean_IR_instInhabitedAlt);
l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1 = _init_l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1();
lean_mark_persistent(l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1);
l_Lean_IR_FnBody_flatten___closed__1 = _init_l_Lean_IR_FnBody_flatten___closed__1();
lean_mark_persistent(l_Lean_IR_FnBody_flatten___closed__1);
l_panic___at_Lean_IR_reshapeAux___spec__1___closed__1 = _init_l_panic___at_Lean_IR_reshapeAux___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_IR_reshapeAux___spec__1___closed__1);
l_Lean_IR_reshapeAux___closed__1 = _init_l_Lean_IR_reshapeAux___closed__1();
lean_mark_persistent(l_Lean_IR_reshapeAux___closed__1);
l_Lean_IR_reshapeAux___closed__2 = _init_l_Lean_IR_reshapeAux___closed__2();
lean_mark_persistent(l_Lean_IR_reshapeAux___closed__2);
l_Lean_IR_reshapeAux___closed__3 = _init_l_Lean_IR_reshapeAux___closed__3();
lean_mark_persistent(l_Lean_IR_reshapeAux___closed__3);
l_Lean_IR_reshapeAux___closed__4 = _init_l_Lean_IR_reshapeAux___closed__4();
lean_mark_persistent(l_Lean_IR_reshapeAux___closed__4);
l_Lean_IR_DeclInfo_sorryDep_x3f___default = _init_l_Lean_IR_DeclInfo_sorryDep_x3f___default();
lean_mark_persistent(l_Lean_IR_DeclInfo_sorryDep_x3f___default);
l_Lean_IR_instInhabitedDecl___closed__1 = _init_l_Lean_IR_instInhabitedDecl___closed__1();
lean_mark_persistent(l_Lean_IR_instInhabitedDecl___closed__1);
l_Lean_IR_instInhabitedDecl___closed__2 = _init_l_Lean_IR_instInhabitedDecl___closed__2();
lean_mark_persistent(l_Lean_IR_instInhabitedDecl___closed__2);
l_Lean_IR_instInhabitedDecl = _init_l_Lean_IR_instInhabitedDecl();
lean_mark_persistent(l_Lean_IR_instInhabitedDecl);
l_Lean_IR_Decl_updateBody_x21___closed__1 = _init_l_Lean_IR_Decl_updateBody_x21___closed__1();
lean_mark_persistent(l_Lean_IR_Decl_updateBody_x21___closed__1);
l_Lean_IR_Decl_updateBody_x21___closed__2 = _init_l_Lean_IR_Decl_updateBody_x21___closed__2();
lean_mark_persistent(l_Lean_IR_Decl_updateBody_x21___closed__2);
l_Lean_IR_Decl_updateBody_x21___closed__3 = _init_l_Lean_IR_Decl_updateBody_x21___closed__3();
lean_mark_persistent(l_Lean_IR_Decl_updateBody_x21___closed__3);
l_Lean_IR_Decl_updateBody_x21___closed__4 = _init_l_Lean_IR_Decl_updateBody_x21___closed__4();
lean_mark_persistent(l_Lean_IR_Decl_updateBody_x21___closed__4);
l_Lean_IR_instInhabitedIndexSet = _init_l_Lean_IR_instInhabitedIndexSet();
lean_mark_persistent(l_Lean_IR_instInhabitedIndexSet);
l_Lean_IR_instAlphaEqvVarId___closed__1 = _init_l_Lean_IR_instAlphaEqvVarId___closed__1();
lean_mark_persistent(l_Lean_IR_instAlphaEqvVarId___closed__1);
l_Lean_IR_instAlphaEqvVarId = _init_l_Lean_IR_instAlphaEqvVarId();
lean_mark_persistent(l_Lean_IR_instAlphaEqvVarId);
l_Lean_IR_instAlphaEqvArg___closed__1 = _init_l_Lean_IR_instAlphaEqvArg___closed__1();
lean_mark_persistent(l_Lean_IR_instAlphaEqvArg___closed__1);
l_Lean_IR_instAlphaEqvArg = _init_l_Lean_IR_instAlphaEqvArg();
lean_mark_persistent(l_Lean_IR_instAlphaEqvArg);
l_Lean_IR_instAlphaEqvArrayArg___closed__1 = _init_l_Lean_IR_instAlphaEqvArrayArg___closed__1();
lean_mark_persistent(l_Lean_IR_instAlphaEqvArrayArg___closed__1);
l_Lean_IR_instAlphaEqvArrayArg = _init_l_Lean_IR_instAlphaEqvArrayArg();
lean_mark_persistent(l_Lean_IR_instAlphaEqvArrayArg);
l_Lean_IR_instAlphaEqvExpr___closed__1 = _init_l_Lean_IR_instAlphaEqvExpr___closed__1();
lean_mark_persistent(l_Lean_IR_instAlphaEqvExpr___closed__1);
l_Lean_IR_instAlphaEqvExpr = _init_l_Lean_IR_instAlphaEqvExpr();
lean_mark_persistent(l_Lean_IR_instAlphaEqvExpr);
l_Lean_IR_instBEqFnBody___closed__1 = _init_l_Lean_IR_instBEqFnBody___closed__1();
lean_mark_persistent(l_Lean_IR_instBEqFnBody___closed__1);
l_Lean_IR_instBEqFnBody = _init_l_Lean_IR_instBEqFnBody();
lean_mark_persistent(l_Lean_IR_instBEqFnBody);
l_Lean_IR_instInhabitedVarIdSet = _init_l_Lean_IR_instInhabitedVarIdSet();
lean_mark_persistent(l_Lean_IR_instInhabitedVarIdSet);
l_Lean_IR_mkIf___closed__1 = _init_l_Lean_IR_mkIf___closed__1();
lean_mark_persistent(l_Lean_IR_mkIf___closed__1);
l_Lean_IR_mkIf___closed__2 = _init_l_Lean_IR_mkIf___closed__2();
lean_mark_persistent(l_Lean_IR_mkIf___closed__2);
l_Lean_IR_mkIf___closed__3 = _init_l_Lean_IR_mkIf___closed__3();
lean_mark_persistent(l_Lean_IR_mkIf___closed__3);
l_Lean_IR_mkIf___closed__4 = _init_l_Lean_IR_mkIf___closed__4();
lean_mark_persistent(l_Lean_IR_mkIf___closed__4);
l_Lean_IR_mkIf___closed__5 = _init_l_Lean_IR_mkIf___closed__5();
lean_mark_persistent(l_Lean_IR_mkIf___closed__5);
l_Lean_IR_mkIf___closed__6 = _init_l_Lean_IR_mkIf___closed__6();
lean_mark_persistent(l_Lean_IR_mkIf___closed__6);
l_Lean_IR_mkIf___closed__7 = _init_l_Lean_IR_mkIf___closed__7();
lean_mark_persistent(l_Lean_IR_mkIf___closed__7);
l_Lean_IR_mkIf___closed__8 = _init_l_Lean_IR_mkIf___closed__8();
lean_mark_persistent(l_Lean_IR_mkIf___closed__8);
l_Lean_IR_mkIf___closed__9 = _init_l_Lean_IR_mkIf___closed__9();
lean_mark_persistent(l_Lean_IR_mkIf___closed__9);
l_Lean_IR_getUnboxOpName___closed__1 = _init_l_Lean_IR_getUnboxOpName___closed__1();
lean_mark_persistent(l_Lean_IR_getUnboxOpName___closed__1);
l_Lean_IR_getUnboxOpName___closed__2 = _init_l_Lean_IR_getUnboxOpName___closed__2();
lean_mark_persistent(l_Lean_IR_getUnboxOpName___closed__2);
l_Lean_IR_getUnboxOpName___closed__3 = _init_l_Lean_IR_getUnboxOpName___closed__3();
lean_mark_persistent(l_Lean_IR_getUnboxOpName___closed__3);
l_Lean_IR_getUnboxOpName___closed__4 = _init_l_Lean_IR_getUnboxOpName___closed__4();
lean_mark_persistent(l_Lean_IR_getUnboxOpName___closed__4);
l_Lean_IR_getUnboxOpName___closed__5 = _init_l_Lean_IR_getUnboxOpName___closed__5();
lean_mark_persistent(l_Lean_IR_getUnboxOpName___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
