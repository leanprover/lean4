// Lean compiler output
// Module: Lean.Compiler.IR.Basic
// Imports: Lean.Data.KVMap Lean.Data.Name Lean.Data.Format Lean.Compiler.ExternAttr
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__2____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprParam___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_2264_;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_mmodifyBody___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_app_expr(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instReprVarId___closed__0;
LEAN_EXPORT lean_object* lean_ir_mk_str_expr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedAlt;
LEAN_EXPORT lean_object* l_Lean_IR_instBEqCtorInfo;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__17____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Lean_IR_instInhabitedCtorInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_IRType_instBEq___closed__0;
LEAN_EXPORT lean_object* lean_ir_mk_fapp_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instAlphaEqvVarId;
LEAN_EXPORT lean_object* l_Lean_IR_mkParam___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_flattenAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedExpr;
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatVarId;
static lean_object* l_Lean_IR_reprVarId___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_38_;
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__3;
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Name_isMetaprogramming_spec__0(lean_object*, lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instToStringVarId___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isScalar___boxed(lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__11____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprParam___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_2264_;
LEAN_EXPORT lean_object* lean_ir_mk_alt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqVarId;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName___boxed(lean_object*);
static lean_object* l_Lean_IR_instReprIRType___closed__0;
static lean_object* l_Lean_IR_instInhabitedAlt___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_reprJoinPointId____x40_Lean_Compiler_IR_Basic___hyg_102____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instAlphaEqvExpr;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo___boxed(lean_object*);
static lean_object* l_Lean_IR_modifyJPs___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reshapeAux___closed__3;
static lean_object* l_Lean_IR_modifyJPs___closed__2;
static lean_object* l_Lean_IR_instReprParam___closed__0;
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_setBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instAlphaEqvArrayArg;
LEAN_EXPORT lean_object* l_Lean_IR_instReprVarId;
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isRef___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reprCtorInfo___redArg____x40_Lean_Compiler_IR_Basic___hyg_1557_(lean_object*);
static lean_object* l_Lean_IR_instInhabitedDecl___closed__2;
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__8;
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedFnBody;
static lean_object* l_Lean_IR_reprIRType___closed__3____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isIrrelevant___boxed(lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_jdecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_case(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshapeAux(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__12____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Lean_IR_instHashableVarId___lam__0___boxed(lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_1557_;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__10____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Lean_IR_FnBody_flatten___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedParam;
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_ctor_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isUnion___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LitVal_beq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__13____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
static lean_object* l_Lean_IR_instAlphaEqvExpr___closed__0;
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1557____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_IR_instBEqLitVal___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_reprJoinPointId___redArg____x40_Lean_Compiler_IR_Basic___hyg_102_(lean_object*);
static lean_object* l_Lean_IR_instHashableJoinPointId___closed__0;
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__13____x40_Lean_Compiler_IR_Basic___hyg_1557_;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqLitVal;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_1557_;
static lean_object* l_Lean_IR_mkIf___closed__6;
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_resetBody(lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__7____x40_Lean_Compiler_IR_Basic___hyg_358_;
lean_object* l_Lean_RBNode_appendTrees___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isIrrelevant(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Index_lt(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instBEqJoinPointId___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1557_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object*);
static lean_object* l_Lean_IR_instInhabitedArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_1557_;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params(lean_object*);
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_reprParam____x40_Lean_Compiler_IR_Basic___hyg_2264____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instHashableVarId;
static lean_object* l_Lean_IR_instInhabitedDecl___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedDecl;
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedVarIdSet;
LEAN_EXPORT lean_object* lean_ir_mk_unreachable(lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_38_;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_instToStringJoinPointId___lam__0___closed__0;
static lean_object* l_Lean_IR_reprParam___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_2264_;
static lean_object* l_Lean_IR_reprIRType___closed__18____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__6;
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_;
static lean_object* l_Lean_IR_mkIf___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedCtorInfo;
LEAN_EXPORT lean_object* l_Lean_IR_instBEqJoinPointId;
LEAN_EXPORT lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__1____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Lean_IR_reprIRType___closed__24____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Lean_IR_reprParam___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_2264_;
LEAN_EXPORT lean_object* l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358_(lean_object*, lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addVarRename(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_instInhabitedExpr___closed__0;
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instAlphaEqvVarId___closed__0;
LEAN_EXPORT lean_object* lean_ir_mk_vdecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name(lean_object*);
static lean_object* l_Lean_IR_getUnboxOpName___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Arg_beq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_38_;
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isObj(lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_num_expr(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprParam___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_2264_;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_name___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reprVarId____x40_Lean_Compiler_IR_Basic___hyg_38____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reprParam___redArg____x40_Lean_Compiler_IR_Basic___hyg_2264_(lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_split(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_mmodifyBody___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reshapeAux___closed__0;
static lean_object* l_Lean_IR_reprParam___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_2264_;
static lean_object* l_Lean_IR_getUnboxOpName___closed__4;
static lean_object* l_Lean_IR_reprIRType___closed__19____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_1557_;
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_;
static lean_object* l_Lean_IR_instInhabitedDecl___closed__1;
LEAN_EXPORT lean_object* lean_ir_mk_sset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqFnBody;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedJoinPointId;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__0____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__2;
static lean_object* l_Lean_IR_instInhabitedExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_instReprJoinPointId;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedIRType;
static lean_object* l_Lean_IR_instReprJoinPointId___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_instAlphaEqvArrayArg___closed__0;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBody(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_getUnboxOpName___closed__0;
static lean_object* l_Lean_IR_instReprCtorInfo___closed__0;
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedArg;
LEAN_EXPORT lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedIndexSet;
static lean_object* l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_modifyJPs___closed__7;
static lean_object* l_Lean_IR_reprIRType___closed__26____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Lean_IR_Alt_mmodifyBody(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_uproj_expr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_Decl_isExtern(lean_object*);
static lean_object* l_Lean_IR_instBEqFnBody___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedVarId;
lean_object* l_Array_mapMUnsafe_map___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_IR_mkIf___closed__8;
lean_object* l_Lean_RBNode_balRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprIRType;
LEAN_EXPORT lean_object* l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__22____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__9____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT uint8_t l_Lean_IR_Arg_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToStringVarId___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instHashableJoinPointId;
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__4;
LEAN_EXPORT uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_papp_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instToStringJoinPointId;
LEAN_EXPORT lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_ret(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object*);
static lean_object* l_Lean_IR_reprParam___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_2264_;
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprParam___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_2264_;
static lean_object* l_Lean_IR_reprIRType___closed__16____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instAlphaEqvArg;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LocalContext_addParams_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_1557_;
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instReprParam;
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqArg;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reprParam____x40_Lean_Compiler_IR_Basic___hyg_2264_(lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isBlack___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_params___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_getUnboxOpName___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_LitVal_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__25____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_1557_;
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatVarId___lam__0(lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_uset(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isStruct___boxed(lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_1557_;
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_IR_modifyJPs___closed__9;
LEAN_EXPORT lean_object* lean_ir_mk_var_arg(lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_1557_;
LEAN_EXPORT lean_object* l_Lean_IR_reprVarId___redArg____x40_Lean_Compiler_IR_Basic___hyg_38_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_getUnboxOpName(lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__5____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Lean_IR_instBEqCtorInfo___closed__0;
LEAN_EXPORT uint8_t l_Lean_IR_args_alphaEqv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_setBody(lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__7;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_modifyJPs___closed__3;
LEAN_EXPORT lean_object* lean_ir_mk_proj_expr(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_1557_;
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatJoinPointId;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0___lam__0(lean_object*);
static lean_object* l_Lean_IR_reprParam___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_2264_;
uint8_t l_Lean_RBNode_isRed___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_instBEqVarId___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reshapeAux___closed__1;
static lean_object* l_Lean_IR_mkIf___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_IRType_beq___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_1557_;
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__12____x40_Lean_Compiler_IR_Basic___hyg_1557_;
static lean_object* l_Lean_IR_reprIRType___closed__21____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Lean_IR_MData_empty;
lean_object* l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Index_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_modifyJPs___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
static lean_object* l_Lean_IR_mkIf___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_Decl_getInfo(lean_object*);
static lean_object* l_Lean_IR_modifyJPs___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_isObj___boxed(lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__15____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_;
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_IRType_instBEq;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_mmodifyBody___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__6____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Lean_IR_mkIf___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_modifyJPs___closed__8;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_addParamRename(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_IR_instHashableVarId___lam__0(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_getUnboxOpName___closed__5;
static lean_object* l_Lean_IR_mkIf___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instBEqArg___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_sproj_expr(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_38_;
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_param(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_modifyJPs___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_1557_;
static lean_object* l_Lean_IR_reprParam___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_2264_;
LEAN_EXPORT lean_object* lean_ir_mk_jmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_FnBody_nil;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringVarId;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Arg_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_dummy_extern_decl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__8____x40_Lean_Compiler_IR_Basic___hyg_358_;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_38_;
static lean_object* l_Lean_IR_reshapeAux___closed__2;
static lean_object* l_Lean_IR_instInhabitedParam___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_instToStringJoinPointId___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reprJoinPointId____x40_Lean_Compiler_IR_Basic___hyg_102_(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__4____x40_Lean_Compiler_IR_Basic___hyg_358_;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_ir_mk_extern_decl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_reprVarId____x40_Lean_Compiler_IR_Basic___hyg_38_(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
static lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__0;
static lean_object* l_Lean_IR_reprIRType___closed__23____x40_Lean_Compiler_IR_Basic___hyg_358_;
static lean_object* l_Lean_IR_reprCtorInfo___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_1557_;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprIRType___closed__14____x40_Lean_Compiler_IR_Basic___hyg_358_;
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatJoinPointId___lam__0(lean_object*);
lean_object* l_Lean_RBNode_balLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_getUnboxOpName___closed__3;
static lean_object* l_Lean_IR_modifyJPs___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_Decl_updateBody_x21___closed__0;
static lean_object* l_Lean_IR_reprVarId___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_38_;
LEAN_EXPORT lean_object* l_Lean_IR_instReprCtorInfo;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_instBEqVarId___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object*, lean_object*);
static lean_object* l_Lean_IR_instAlphaEqvArg___closed__0;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_reprParam___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_2264_;
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_IR_instInhabitedVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("idx", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprVarId___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_reprVarId___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprVarId___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_2 = l_Lean_IR_reprVarId___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprVarId___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprVarId___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprVarId___redArg____x40_Lean_Compiler_IR_Basic___hyg_38_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_2 = l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_3 = l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_12 = l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unbox(x_7);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprVarId____x40_Lean_Compiler_IR_Basic___hyg_38_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprVarId___redArg____x40_Lean_Compiler_IR_Basic___hyg_38_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprVarId____x40_Lean_Compiler_IR_Basic___hyg_38____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprVarId____x40_Lean_Compiler_IR_Basic___hyg_38_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instReprVarId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_reprVarId____x40_Lean_Compiler_IR_Basic___hyg_38____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instReprVarId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instReprVarId___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedJoinPointId() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprJoinPointId___redArg____x40_Lean_Compiler_IR_Basic___hyg_102_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_2 = l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_3 = l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_12 = l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_unbox(x_7);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprJoinPointId____x40_Lean_Compiler_IR_Basic___hyg_102_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprJoinPointId___redArg____x40_Lean_Compiler_IR_Basic___hyg_102_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprJoinPointId____x40_Lean_Compiler_IR_Basic___hyg_102____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprJoinPointId____x40_Lean_Compiler_IR_Basic___hyg_102_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instReprJoinPointId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_reprJoinPointId____x40_Lean_Compiler_IR_Basic___hyg_102____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instReprJoinPointId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instReprJoinPointId___closed__0;
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
LEAN_EXPORT uint8_t l_Lean_IR_instBEqVarId___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instBEqVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instBEqVarId___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instBEqVarId___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_instBEqVarId___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instToStringVarId___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x_", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringVarId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_instToStringVarId___lam__0___closed__0;
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instToStringVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToStringVarId___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatVarId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_instToStringVarId___lam__0___closed__0;
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instToFormatVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToFormatVarId___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_IR_instHashableVarId___lam__0(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_instHashableVarId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instHashableVarId___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instHashableVarId___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instBEqJoinPointId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instBEqVarId___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instBEqJoinPointId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instBEqJoinPointId___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instToStringJoinPointId___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("block_", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToStringJoinPointId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_instToStringJoinPointId___lam__0___closed__0;
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instToStringJoinPointId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToStringJoinPointId___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_instToFormatJoinPointId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_instToStringJoinPointId___lam__0___closed__0;
x_3 = l_Nat_reprFast(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_instToFormatJoinPointId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instToFormatJoinPointId___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instHashableJoinPointId___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_instHashableVarId___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instHashableJoinPointId() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instHashableJoinPointId___closed__0;
return x_1;
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
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_4, 5);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_3);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_6);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_3 = x_9;
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_1);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_11);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0___lam__0), 1, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
lean_dec(x_2);
x_7 = l_Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0___lam__0(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0___lam__0(x_4);
x_9 = l_List_foldl___at___Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0_spec__0(x_2, x_6, x_8, x_5);
return x_9;
}
}
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_array_to_list(x_1);
x_6 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__3;
x_7 = l_Std_Format_joinSep___at___Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0_spec__0(x_5, x_6);
x_8 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_9 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__5;
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__6;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Std_Format_fill(x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__8;
return x_15;
}
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__0____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.float", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__1____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__0____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__2____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.uint8", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__3____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__2____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__4____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.uint16", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__5____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__4____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__6____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.uint32", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__7____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__6____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__8____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.uint64", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__9____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__8____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__10____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.usize", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__11____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__10____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__12____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.irrelevant", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__13____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__12____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__14____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.object", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__15____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__14____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__16____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.tobject", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__17____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__16____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__18____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.float32", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__19____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__18____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__21____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.struct", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__22____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__21____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__23____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_IR_reprIRType___closed__22____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__24____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.IRType.union", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__25____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprIRType___closed__24____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprIRType___closed__26____x40_Lean_Compiler_IR_Basic___hyg_358_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_IR_reprIRType___closed__25____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_19; lean_object* x_27; lean_object* x_35; lean_object* x_43; lean_object* x_51; lean_object* x_59; lean_object* x_67; lean_object* x_75; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_unsigned_to_nat(1024u);
x_84 = lean_nat_dec_le(x_83, x_2);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_3 = x_85;
goto block_10;
}
else
{
lean_object* x_86; 
x_86 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_3 = x_86;
goto block_10;
}
}
case 1:
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_unsigned_to_nat(1024u);
x_88 = lean_nat_dec_le(x_87, x_2);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_11 = x_89;
goto block_18;
}
else
{
lean_object* x_90; 
x_90 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_11 = x_90;
goto block_18;
}
}
case 2:
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_unsigned_to_nat(1024u);
x_92 = lean_nat_dec_le(x_91, x_2);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_19 = x_93;
goto block_26;
}
else
{
lean_object* x_94; 
x_94 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_19 = x_94;
goto block_26;
}
}
case 3:
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_unsigned_to_nat(1024u);
x_96 = lean_nat_dec_le(x_95, x_2);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_27 = x_97;
goto block_34;
}
else
{
lean_object* x_98; 
x_98 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_27 = x_98;
goto block_34;
}
}
case 4:
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_unsigned_to_nat(1024u);
x_100 = lean_nat_dec_le(x_99, x_2);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_35 = x_101;
goto block_42;
}
else
{
lean_object* x_102; 
x_102 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_35 = x_102;
goto block_42;
}
}
case 5:
{
lean_object* x_103; uint8_t x_104; 
x_103 = lean_unsigned_to_nat(1024u);
x_104 = lean_nat_dec_le(x_103, x_2);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_43 = x_105;
goto block_50;
}
else
{
lean_object* x_106; 
x_106 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_43 = x_106;
goto block_50;
}
}
case 6:
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_unsigned_to_nat(1024u);
x_108 = lean_nat_dec_le(x_107, x_2);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_51 = x_109;
goto block_58;
}
else
{
lean_object* x_110; 
x_110 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_51 = x_110;
goto block_58;
}
}
case 7:
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_unsigned_to_nat(1024u);
x_112 = lean_nat_dec_le(x_111, x_2);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_59 = x_113;
goto block_66;
}
else
{
lean_object* x_114; 
x_114 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_59 = x_114;
goto block_66;
}
}
case 8:
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_unsigned_to_nat(1024u);
x_116 = lean_nat_dec_le(x_115, x_2);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_67 = x_117;
goto block_74;
}
else
{
lean_object* x_118; 
x_118 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_67 = x_118;
goto block_74;
}
}
case 9:
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_unsigned_to_nat(1024u);
x_120 = lean_nat_dec_le(x_119, x_2);
if (x_120 == 0)
{
lean_object* x_121; 
x_121 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_75 = x_121;
goto block_82;
}
else
{
lean_object* x_122; 
x_122 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_75 = x_122;
goto block_82;
}
}
case 10:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_141; uint8_t x_142; 
x_123 = lean_ctor_get(x_1, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_1, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_125 = x_1;
} else {
 lean_dec_ref(x_1);
 x_125 = lean_box(0);
}
x_141 = lean_unsigned_to_nat(1024u);
x_142 = lean_nat_dec_le(x_141, x_2);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_126 = x_143;
goto block_140;
}
else
{
lean_object* x_144; 
x_144 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_126 = x_144;
goto block_140;
}
block_140:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_127 = lean_box(1);
x_128 = l_Lean_IR_reprIRType___closed__23____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_129 = lean_unsigned_to_nat(1024u);
x_130 = l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(x_123, x_129);
if (lean_is_scalar(x_125)) {
 x_131 = lean_alloc_ctor(5, 2, 0);
} else {
 x_131 = x_125;
 lean_ctor_set_tag(x_131, 5);
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_127);
x_133 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0(x_124);
x_134 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_137, 0, x_135);
x_138 = lean_unbox(x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_138);
x_139 = l_Repr_addAppParen(x_137, x_2);
return x_139;
}
}
default: 
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_163; uint8_t x_164; 
x_145 = lean_ctor_get(x_1, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_147 = x_1;
} else {
 lean_dec_ref(x_1);
 x_147 = lean_box(0);
}
x_163 = lean_unsigned_to_nat(1024u);
x_164 = lean_nat_dec_le(x_163, x_2);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_148 = x_165;
goto block_162;
}
else
{
lean_object* x_166; 
x_166 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_148 = x_166;
goto block_162;
}
block_162:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; 
x_149 = lean_box(1);
x_150 = l_Lean_IR_reprIRType___closed__26____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_151 = lean_unsigned_to_nat(1024u);
x_152 = l_Lean_Name_reprPrec(x_145, x_151);
if (lean_is_scalar(x_147)) {
 x_153 = lean_alloc_ctor(5, 2, 0);
} else {
 x_153 = x_147;
 lean_ctor_set_tag(x_153, 5);
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
x_155 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0(x_146);
x_156 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_157, 0, x_148);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_159, 0, x_157);
x_160 = lean_unbox(x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_160);
x_161 = l_Repr_addAppParen(x_159, x_2);
return x_161;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lean_IR_reprIRType___closed__1____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_Lean_IR_reprIRType___closed__3____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = l_Lean_IR_reprIRType___closed__5____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = l_Repr_addAppParen(x_23, x_2);
return x_25;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = l_Lean_IR_reprIRType___closed__7____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_33 = l_Repr_addAppParen(x_31, x_2);
return x_33;
}
block_42:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = l_Lean_IR_reprIRType___closed__9____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_40);
x_41 = l_Repr_addAppParen(x_39, x_2);
return x_41;
}
block_50:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_44 = l_Lean_IR_reprIRType___closed__11____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = l_Repr_addAppParen(x_47, x_2);
return x_49;
}
block_58:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_52 = l_Lean_IR_reprIRType___closed__13____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_53 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = l_Repr_addAppParen(x_55, x_2);
return x_57;
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_60 = l_Lean_IR_reprIRType___closed__15____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_unbox(x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_64);
x_65 = l_Repr_addAppParen(x_63, x_2);
return x_65;
}
block_74:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = l_Lean_IR_reprIRType___closed__17____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_71, 0, x_69);
x_72 = lean_unbox(x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_72);
x_73 = l_Repr_addAppParen(x_71, x_2);
return x_73;
}
block_82:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_76 = l_Lean_IR_reprIRType___closed__19____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_77 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_79, 0, x_77);
x_80 = lean_unbox(x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_80);
x_81 = l_Repr_addAppParen(x_79, x_2);
return x_81;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instReprIRType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instReprIRType() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instReprIRType___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget(x_1, x_7);
x_9 = lean_array_fget(x_2, x_7);
x_10 = l_Lean_IR_IRType_beq(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg(x_1, x_2, x_4);
return x_6;
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
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
return x_22;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(1);
x_24 = lean_unbox(x_23);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
return x_30;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
return x_34;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(1);
x_36 = lean_unbox(x_35);
return x_36;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
return x_38;
}
}
case 9:
{
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
return x_42;
}
}
case 10:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at___Lean_Name_isMetaprogramming_spec__0(x_43, x_45);
if (x_47 == 0)
{
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_array_get_size(x_44);
x_49 = lean_array_get_size(x_46);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_dec(x_48);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg(x_44, x_46, x_48);
return x_51;
}
}
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
return x_53;
}
}
default: 
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_1, 0);
x_55 = lean_ctor_get(x_1, 1);
x_56 = lean_ctor_get(x_2, 0);
x_57 = lean_ctor_get(x_2, 1);
x_58 = lean_name_eq(x_54, x_56);
if (x_58 == 0)
{
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_array_get_size(x_55);
x_60 = lean_array_get_size(x_57);
x_61 = lean_nat_dec_eq(x_59, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_dec(x_59);
return x_61;
}
else
{
uint8_t x_62; 
x_62 = l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg(x_55, x_57, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_box(0);
x_64 = lean_unbox(x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
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
static lean_object* _init_l_Lean_IR_IRType_instBEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_IRType_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_IRType_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_IRType_instBEq___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_IRType_isScalar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
case 7:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
case 8:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
case 10:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
case 11:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
default: 
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
return x_13;
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
case 8:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
default: 
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
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
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
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
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
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
static lean_object* _init_l_Lean_IR_instInhabitedArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedArg___closed__0;
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
return x_11;
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
static lean_object* _init_l_Lean_IR_instBEqArg___closed__0() {
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
x_1 = l_Lean_IR_instBEqArg___closed__0;
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_string_dec_eq(x_10, x_11);
return x_12;
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
static lean_object* _init_l_Lean_IR_instBEqLitVal___closed__0() {
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
x_1 = l_Lean_IR_instBEqLitVal___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedCtorInfo___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedCtorInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedCtorInfo___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprCtorInfo___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_reprCtorInfo___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_2 = l_Lean_IR_reprCtorInfo___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cidx", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprCtorInfo___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("size", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprCtorInfo___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("usize", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprCtorInfo___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__12____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ssize", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprCtorInfo___redArg___closed__13____x40_Lean_Compiler_IR_Basic___hyg_1557_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprCtorInfo___redArg___closed__12____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprCtorInfo___redArg____x40_Lean_Compiler_IR_Basic___hyg_1557_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_8 = l_Lean_IR_reprCtorInfo___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_9 = l_Lean_IR_reprCtorInfo___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Name_reprPrec(x_2, x_10);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_IR_reprCtorInfo___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
x_24 = l_Nat_reprFast(x_3);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_unbox(x_13);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_17);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
x_32 = l_Lean_IR_reprCtorInfo___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
x_35 = l_Nat_reprFast(x_4);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unbox(x_13);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_17);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_19);
x_43 = l_Lean_IR_reprCtorInfo___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_7);
x_46 = l_Lean_IR_reprCtorInfo___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_47 = l_Nat_reprFast(x_5);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_unbox(x_13);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_51);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_17);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_19);
x_55 = l_Lean_IR_reprCtorInfo___redArg___closed__13____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_7);
x_58 = l_Nat_reprFast(x_6);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_46);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_unbox(x_13);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_62);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_65 = l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
x_67 = l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_unbox(x_13);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_71);
return x_70;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1557_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprCtorInfo___redArg____x40_Lean_Compiler_IR_Basic___hyg_1557_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1557____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1557_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instReprCtorInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_reprCtorInfo____x40_Lean_Compiler_IR_Basic___hyg_1557____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instReprCtorInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instReprCtorInfo___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
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
x_18 = lean_name_eq(x_3, x_8);
if (x_18 == 0)
{
x_13 = x_18;
goto block_17;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_4, x_9);
x_13 = x_19;
goto block_17;
}
block_17:
{
if (x_13 == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_5, x_10);
if (x_14 == 0)
{
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_6, x_11);
if (x_15 == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_7, x_12);
return x_16;
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
static lean_object* _init_l_Lean_IR_instBEqCtorInfo___closed__0() {
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
x_1 = l_Lean_IR_instBEqCtorInfo___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_CtorInfo_isRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_9; uint8_t x_10; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_1, 4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_2);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_9, x_3);
x_5 = x_11;
goto block_8;
}
else
{
x_5 = x_10;
goto block_8;
}
block_8:
{
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_4);
return x_7;
}
else
{
return x_5;
}
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
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
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
static lean_object* _init_l_Lean_IR_instInhabitedExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_instInhabitedExpr___closed__0;
x_2 = l_Lean_IR_instInhabitedCtorInfo___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedExpr___closed__1;
return x_1;
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
static lean_object* _init_l_Lean_IR_instInhabitedParam___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instInhabitedParam___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprParam___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_reprParam___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_2 = l_Lean_IR_reprParam___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("borrow", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprParam___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ty", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_reprParam___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_reprParam___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_2264_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprParam___redArg____x40_Lean_Compiler_IR_Basic___hyg_2264_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_6 = l_Lean_IR_reprParam___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_7 = l_Lean_IR_reprParam___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_IR_reprVarId___redArg____x40_Lean_Compiler_IR_Basic___hyg_38_(x_2);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_IR_reprParam___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
x_22 = l_Lean_IR_reprParam___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_23 = l_Bool_repr___redArg(x_3);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_unbox(x_11);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_15);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_17);
x_30 = l_Lean_IR_reprParam___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
x_33 = l_Lean_IR_reprParam___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_34 = l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358_(x_4, x_8);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_unbox(x_11);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_40 = l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_unbox(x_11);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
return x_45;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprParam____x40_Lean_Compiler_IR_Basic___hyg_2264_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprParam___redArg____x40_Lean_Compiler_IR_Basic___hyg_2264_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_reprParam____x40_Lean_Compiler_IR_Basic___hyg_2264____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_reprParam____x40_Lean_Compiler_IR_Basic___hyg_2264_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instReprParam___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_reprParam____x40_Lean_Compiler_IR_Basic___hyg_2264____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_instReprParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_instReprParam___closed__0;
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
static lean_object* _init_l_Lean_IR_instInhabitedAlt___closed__0() {
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
x_1 = l_Lean_IR_instInhabitedAlt___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_isTerminal(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 10:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(1);
x_3 = lean_unbox(x_2);
return x_3;
}
case 11:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
case 12:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
case 13:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
default: 
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
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
case 0:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 5);
lean_inc(x_7);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
return x_10;
}
case 9:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
return x_11;
}
default: 
{
lean_inc(x_1);
return x_1;
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
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_2 = x_7;
goto block_6;
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_2 = x_8;
goto block_6;
}
case 2:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_2 = x_9;
goto block_6;
}
case 3:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_2 = x_10;
goto block_6;
}
case 4:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_2 = x_11;
goto block_6;
}
case 5:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
x_2 = x_12;
goto block_6;
}
case 6:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_2 = x_13;
goto block_6;
}
case 7:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_2 = x_14;
goto block_6;
}
case 8:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_2 = x_15;
goto block_6;
}
case 9:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_2 = x_16;
goto block_6;
}
default: 
{
lean_inc(x_1);
x_2 = x_1;
goto block_6;
}
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(13);
x_4 = l_Lean_IR_FnBody_setBody(x_1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_IR_Alt_body___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Alt_body(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_setBody(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_Alt_modifyBody(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_IR_Alt_mmodifyBody___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_mmodifyBody___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_mmodifyBody___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_IR_Alt_mmodifyBody___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_apply_1(x_2, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_IR_Alt_mmodifyBody___redArg___lam__1), 1, 0);
x_16 = lean_apply_1(x_2, x_13);
x_17 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Alt_mmodifyBody(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_IR_Alt_mmodifyBody___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = lean_apply_1(x_3, x_8);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_IR_Alt_mmodifyBody___redArg___lam__1), 1, 0);
x_17 = lean_apply_1(x_3, x_14);
x_18 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Alt_isDefault(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
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
lean_object* x_3; uint8_t x_7; 
x_7 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_7 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_3 = x_8;
goto block_6;
}
case 1:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_3 = x_9;
goto block_6;
}
case 2:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_3 = x_10;
goto block_6;
}
case 3:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_3 = x_11;
goto block_6;
}
case 4:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_3 = x_12;
goto block_6;
}
case 5:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
x_3 = x_13;
goto block_6;
}
case 6:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_3 = x_14;
goto block_6;
}
case 7:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_3 = x_15;
goto block_6;
}
case 8:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_3 = x_16;
goto block_6;
}
case 9:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_3 = x_17;
goto block_6;
}
default: 
{
lean_inc(x_1);
x_3 = x_1;
goto block_6;
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_1);
return x_18;
}
block_6:
{
lean_object* x_4; 
x_4 = l_Lean_IR_push(x_2, x_1);
x_1 = x_3;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lean_IR_FnBody_flatten___closed__0() {
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
x_2 = l_Lean_IR_FnBody_flatten___closed__0;
x_3 = l_Lean_IR_flattenAux(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_reshapeAux___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Array.Basic", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reshapeAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array.swapAt!", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reshapeAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("index ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_reshapeAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" out of bounds", 14, 14);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_13 = lean_box(13);
x_14 = lean_array_get_size(x_1);
x_15 = lean_nat_dec_lt(x_7, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_1);
x_17 = l_Lean_IR_reshapeAux___closed__0;
x_18 = l_Lean_IR_reshapeAux___closed__1;
x_19 = lean_unsigned_to_nat(442u);
x_20 = lean_unsigned_to_nat(4u);
x_21 = l_Lean_IR_reshapeAux___closed__2;
lean_inc(x_7);
x_22 = l_Nat_reprFast(x_7);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = l_Lean_IR_reshapeAux___closed__3;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_mkPanicMessageWithDecl(x_17, x_18, x_19, x_20, x_25);
lean_dec(x_25);
x_27 = l_panic___redArg(x_16, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_8 = x_28;
x_9 = x_29;
goto block_12;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_array_fget(x_1, x_7);
x_31 = lean_array_fset(x_1, x_7, x_13);
x_8 = x_30;
x_9 = x_31;
goto block_12;
}
block_12:
{
lean_object* x_10; 
x_10 = l_Lean_IR_FnBody_setBody(x_8, x_3);
x_1 = x_9;
x_2 = x_7;
x_3 = x_10;
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
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 2, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_10 = lean_apply_1(x_1, x_8);
x_11 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_modifyJPs___closed__1;
x_2 = l_Lean_IR_modifyJPs___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_modifyJPs___closed__5;
x_2 = l_Lean_IR_modifyJPs___closed__4;
x_3 = l_Lean_IR_modifyJPs___closed__3;
x_4 = l_Lean_IR_modifyJPs___closed__2;
x_5 = l_Lean_IR_modifyJPs___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_modifyJPs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_modifyJPs___closed__6;
x_2 = l_Lean_IR_modifyJPs___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_modifyJPs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lean_IR_modifyJPs___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_IR_modifyJPs___closed__9;
x_5 = lean_array_size(x_1);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___redArg(x_4, x_3, x_5, x_6, x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_3);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_IR_mmodifyJPs___redArg___lam__0), 5, 4);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_1);
x_10 = lean_apply_1(x_2, x_7);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_2(x_1, lean_box(0), x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_IR_mmodifyJPs___redArg___lam__1), 4, 3);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
x_8 = lean_array_size(x_2);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___redArg(x_1, x_7, x_8, x_9, x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mmodifyJPs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_IR_mmodifyJPs___redArg___lam__1), 4, 3);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_6);
x_9 = lean_array_size(x_3);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___redArg(x_2, x_8, x_9, x_10, x_3);
return x_11;
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
static lean_object* _init_l_Lean_IR_instInhabitedDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
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
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_instInhabitedDecl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_instInhabitedDecl___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_IR_instInhabitedDecl___closed__0;
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedDecl;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.Basic", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.Decl.updateBody!", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected definition", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_Decl_updateBody_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_Decl_updateBody_x21___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(434u);
x_4 = l_Lean_IR_Decl_updateBody_x21___closed__1;
x_5 = l_Lean_IR_Decl_updateBody_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
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
x_10 = l_Lean_IR_Decl_updateBody_x21___closed__3;
x_11 = l_panic___at___Lean_IR_Decl_updateBody_x21_spec__0(x_10);
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
x_4 = lean_box(13);
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
static lean_object* _init_l_Lean_IR_instInhabitedIndexSet() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(2);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_6);
return x_5;
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
x_13 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_9, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
case 1:
{
lean_dec(x_11);
lean_dec(x_10);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
default: 
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_12, x_2, x_3);
lean_ctor_set(x_1, 3, x_15);
return x_1;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_20 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(x_2, x_17);
switch (x_20) {
case 0:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_16, x_2, x_3);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_7);
return x_22;
}
case 1:
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_2);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set_uint8(x_23, sizeof(void*)*4, x_7);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_19, x_2, x_3);
x_25 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*4, x_7);
return x_25;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_30 = x_1;
} else {
 lean_dec_ref(x_1);
 x_30 = lean_box(0);
}
x_31 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(x_2, x_27);
switch (x_31) {
case 0:
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_32 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_26, x_2, x_3);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*4);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 3);
lean_inc(x_37);
if (x_33 == 0)
{
if (lean_obj_tag(x_34) == 0)
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_52; 
lean_dec(x_30);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_32, 3);
lean_dec(x_53);
x_54 = lean_ctor_get(x_32, 2);
lean_dec(x_54);
x_55 = lean_ctor_get(x_32, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_32, 0);
lean_dec(x_56);
lean_ctor_set(x_32, 0, x_37);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_27);
lean_ctor_set(x_57, 2, x_28);
lean_ctor_set(x_57, 3, x_29);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_7);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_37);
lean_ctor_set(x_58, 1, x_35);
lean_ctor_set(x_58, 2, x_36);
lean_ctor_set(x_58, 3, x_37);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_33);
x_59 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_27);
lean_ctor_set(x_59, 2, x_28);
lean_ctor_set(x_59, 3, x_29);
lean_ctor_set_uint8(x_59, sizeof(void*)*4, x_7);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_32);
x_61 = lean_ctor_get(x_37, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_37, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_37, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_37, 3);
lean_inc(x_64);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_64;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_65; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_65 = !lean_is_exclusive(x_37);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_37, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_37, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_37, 0);
lean_dec(x_69);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_7);
return x_37;
}
else
{
lean_object* x_70; 
lean_dec(x_37);
x_70 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_70, 0, x_32);
lean_ctor_set(x_70, 1, x_27);
lean_ctor_set(x_70, 2, x_28);
lean_ctor_set(x_70, 3, x_29);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_7);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_32);
x_72 = lean_ctor_get(x_34, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_34, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_34, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_34, 3);
lean_inc(x_75);
lean_dec(x_34);
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_75;
x_42 = x_35;
x_43 = x_36;
x_44 = x_37;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_76; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_30);
x_76 = !lean_is_exclusive(x_34);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_34, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_34, 2);
lean_dec(x_78);
x_79 = lean_ctor_get(x_34, 1);
lean_dec(x_79);
x_80 = lean_ctor_get(x_34, 0);
lean_dec(x_80);
lean_ctor_set(x_34, 3, x_29);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 1, x_27);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_7);
return x_34;
}
else
{
lean_object* x_81; 
lean_dec(x_34);
x_81 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_81, 0, x_32);
lean_ctor_set(x_81, 1, x_27);
lean_ctor_set(x_81, 2, x_28);
lean_ctor_set(x_81, 3, x_29);
lean_ctor_set_uint8(x_81, sizeof(void*)*4, x_7);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_32);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_32, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_32, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_32, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_32, 0);
lean_dec(x_86);
x_87 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_32);
x_88 = lean_ctor_get(x_37, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_37, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_37, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_37, 3);
lean_inc(x_91);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_91;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
uint8_t x_92; 
lean_dec(x_30);
x_92 = !lean_is_exclusive(x_34);
if (x_92 == 0)
{
lean_object* x_93; 
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_87);
x_93 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_27);
lean_ctor_set(x_93, 2, x_28);
lean_ctor_set(x_93, 3, x_29);
lean_ctor_set_uint8(x_93, sizeof(void*)*4, x_7);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_34, 0);
x_95 = lean_ctor_get(x_34, 1);
x_96 = lean_ctor_get(x_34, 2);
x_97 = lean_ctor_get(x_34, 3);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_34);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
lean_ctor_set(x_98, 2, x_96);
lean_ctor_set(x_98, 3, x_97);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_87);
lean_ctor_set(x_32, 0, x_98);
x_99 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_99, 0, x_32);
lean_ctor_set(x_99, 1, x_27);
lean_ctor_set(x_99, 2, x_28);
lean_ctor_set(x_99, 3, x_29);
lean_ctor_set_uint8(x_99, sizeof(void*)*4, x_7);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_32);
x_100 = lean_ctor_get_uint8(x_37, sizeof(void*)*4);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_37, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_37, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_37, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_37, 3);
lean_inc(x_104);
lean_dec(x_37);
x_38 = x_34;
x_39 = x_35;
x_40 = x_36;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_104;
x_45 = x_27;
x_46 = x_28;
x_47 = x_29;
goto block_51;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_30);
x_105 = lean_ctor_get(x_34, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_34, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_34, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_34, 3);
lean_inc(x_108);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 lean_ctor_release(x_34, 3);
 x_109 = x_34;
} else {
 lean_dec_ref(x_34);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 4, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_100);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_35);
lean_ctor_set(x_111, 2, x_36);
lean_ctor_set(x_111, 3, x_37);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_33);
x_112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_27);
lean_ctor_set(x_112, 2, x_28);
lean_ctor_set(x_112, 3, x_29);
lean_ctor_set_uint8(x_112, sizeof(void*)*4, x_7);
return x_112;
}
}
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_30);
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_32);
lean_ctor_set(x_113, 1, x_27);
lean_ctor_set(x_113, 2, x_28);
lean_ctor_set(x_113, 3, x_29);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_7);
return x_113;
}
block_51:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_30)) {
 x_48 = lean_alloc_ctor(1, 4, 1);
} else {
 x_48 = x_30;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_40);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_7);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_7);
x_50 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_33);
return x_50;
}
}
case 1:
{
lean_object* x_114; 
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_30)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_30;
}
lean_ctor_set(x_114, 0, x_26);
lean_ctor_set(x_114, 1, x_2);
lean_ctor_set(x_114, 2, x_3);
lean_ctor_set(x_114, 3, x_29);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_7);
return x_114;
}
default: 
{
lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_115 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_29, x_2, x_3);
x_116 = lean_ctor_get_uint8(x_115, sizeof(void*)*4);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 3);
lean_inc(x_120);
if (x_116 == 0)
{
if (lean_obj_tag(x_117) == 0)
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_135; 
lean_dec(x_30);
x_135 = !lean_is_exclusive(x_115);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_115, 3);
lean_dec(x_136);
x_137 = lean_ctor_get(x_115, 2);
lean_dec(x_137);
x_138 = lean_ctor_get(x_115, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_115, 0);
lean_dec(x_139);
lean_ctor_set(x_115, 0, x_120);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_26);
lean_ctor_set(x_140, 1, x_27);
lean_ctor_set(x_140, 2, x_28);
lean_ctor_set(x_140, 3, x_115);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_7);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_115);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_120);
lean_ctor_set(x_141, 1, x_118);
lean_ctor_set(x_141, 2, x_119);
lean_ctor_set(x_141, 3, x_120);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_116);
x_142 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_142, 0, x_26);
lean_ctor_set(x_142, 1, x_27);
lean_ctor_set(x_142, 2, x_28);
lean_ctor_set(x_142, 3, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_7);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_115);
x_144 = lean_ctor_get(x_120, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_120, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_120, 2);
lean_inc(x_146);
x_147 = lean_ctor_get(x_120, 3);
lean_inc(x_147);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_144;
x_128 = x_145;
x_129 = x_146;
x_130 = x_147;
goto block_134;
}
else
{
uint8_t x_148; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_148 = !lean_is_exclusive(x_120);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_120, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_120, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_120, 0);
lean_dec(x_152);
lean_ctor_set(x_120, 3, x_115);
lean_ctor_set(x_120, 2, x_28);
lean_ctor_set(x_120, 1, x_27);
lean_ctor_set(x_120, 0, x_26);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_7);
return x_120;
}
else
{
lean_object* x_153; 
lean_dec(x_120);
x_153 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_153, 0, x_26);
lean_ctor_set(x_153, 1, x_27);
lean_ctor_set(x_153, 2, x_28);
lean_ctor_set(x_153, 3, x_115);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_7);
return x_153;
}
}
}
}
else
{
uint8_t x_154; 
x_154 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_115);
x_155 = lean_ctor_get(x_117, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_117, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_117, 2);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 3);
lean_inc(x_158);
lean_dec(x_117);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_155;
x_125 = x_156;
x_126 = x_157;
x_127 = x_158;
x_128 = x_118;
x_129 = x_119;
x_130 = x_120;
goto block_134;
}
else
{
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_30);
x_159 = !lean_is_exclusive(x_117);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_117, 3);
lean_dec(x_160);
x_161 = lean_ctor_get(x_117, 2);
lean_dec(x_161);
x_162 = lean_ctor_get(x_117, 1);
lean_dec(x_162);
x_163 = lean_ctor_get(x_117, 0);
lean_dec(x_163);
lean_ctor_set(x_117, 3, x_115);
lean_ctor_set(x_117, 2, x_28);
lean_ctor_set(x_117, 1, x_27);
lean_ctor_set(x_117, 0, x_26);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_7);
return x_117;
}
else
{
lean_object* x_164; 
lean_dec(x_117);
x_164 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_164, 0, x_26);
lean_ctor_set(x_164, 1, x_27);
lean_ctor_set(x_164, 2, x_28);
lean_ctor_set(x_164, 3, x_115);
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_7);
return x_164;
}
}
else
{
uint8_t x_165; 
x_165 = !lean_is_exclusive(x_115);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_115, 3);
lean_dec(x_166);
x_167 = lean_ctor_get(x_115, 2);
lean_dec(x_167);
x_168 = lean_ctor_get(x_115, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_115, 0);
lean_dec(x_169);
x_170 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_free_object(x_115);
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_120, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_120, 3);
lean_inc(x_174);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_171;
x_128 = x_172;
x_129 = x_173;
x_130 = x_174;
goto block_134;
}
else
{
uint8_t x_175; 
lean_dec(x_30);
x_175 = !lean_is_exclusive(x_117);
if (x_175 == 0)
{
lean_object* x_176; 
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_170);
x_176 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_176, 0, x_26);
lean_ctor_set(x_176, 1, x_27);
lean_ctor_set(x_176, 2, x_28);
lean_ctor_set(x_176, 3, x_115);
lean_ctor_set_uint8(x_176, sizeof(void*)*4, x_7);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_117, 0);
x_178 = lean_ctor_get(x_117, 1);
x_179 = lean_ctor_get(x_117, 2);
x_180 = lean_ctor_get(x_117, 3);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_117);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_178);
lean_ctor_set(x_181, 2, x_179);
lean_ctor_set(x_181, 3, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_170);
lean_ctor_set(x_115, 0, x_181);
x_182 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_182, 0, x_26);
lean_ctor_set(x_182, 1, x_27);
lean_ctor_set(x_182, 2, x_28);
lean_ctor_set(x_182, 3, x_115);
lean_ctor_set_uint8(x_182, sizeof(void*)*4, x_7);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_115);
x_183 = lean_ctor_get_uint8(x_120, sizeof(void*)*4);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_120, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_120, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_120, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_120, 3);
lean_inc(x_187);
lean_dec(x_120);
x_121 = x_26;
x_122 = x_27;
x_123 = x_28;
x_124 = x_117;
x_125 = x_118;
x_126 = x_119;
x_127 = x_184;
x_128 = x_185;
x_129 = x_186;
x_130 = x_187;
goto block_134;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_30);
x_188 = lean_ctor_get(x_117, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_117, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_117, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_117, 3);
lean_inc(x_191);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_192 = x_117;
} else {
 lean_dec_ref(x_117);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 4, 1);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_189);
lean_ctor_set(x_193, 2, x_190);
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_183);
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_118);
lean_ctor_set(x_194, 2, x_119);
lean_ctor_set(x_194, 3, x_120);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_116);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_26);
lean_ctor_set(x_195, 1, x_27);
lean_ctor_set(x_195, 2, x_28);
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_7);
return x_195;
}
}
}
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_30);
x_196 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_196, 0, x_26);
lean_ctor_set(x_196, 1, x_27);
lean_ctor_set(x_196, 2, x_28);
lean_ctor_set(x_196, 3, x_115);
lean_ctor_set_uint8(x_196, sizeof(void*)*4, x_7);
return x_196;
}
block_134:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
if (lean_is_scalar(x_30)) {
 x_131 = lean_alloc_ctor(1, 4, 1);
} else {
 x_131 = x_30;
}
lean_ctor_set(x_131, 0, x_121);
lean_ctor_set(x_131, 1, x_122);
lean_ctor_set(x_131, 2, x_123);
lean_ctor_set(x_131, 3, x_124);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_7);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_128);
lean_ctor_set(x_132, 2, x_129);
lean_ctor_set(x_132, 3, x_130);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_7);
x_133 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_125);
lean_ctor_set(x_133, 2, x_126);
lean_ctor_set(x_133, 3, x_132);
lean_ctor_set_uint8(x_133, sizeof(void*)*4, x_116);
return x_133;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___redArg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___redArg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_mkIndexSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_1, x_2, x_5);
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
x_6 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_1, x_2, x_5);
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
x_6 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_1, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LocalContext_addParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_IR_LocalContext_addParams_spec__0(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_IR_LocalContext_addParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_IR_LocalContext_addParams_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_addParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_LocalContext_isJP(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_6);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
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
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
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
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
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
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_6);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
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
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_6);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
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
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_nat_dec_lt(x_1, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_eq(x_1, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_RBNode_isBlack___redArg(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_7);
lean_ctor_set(x_2, 3, x_12);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_2);
x_14 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_7);
x_15 = l_Lean_RBNode_balRight___redArg(x_4, x_5, x_6, x_14);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_16 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_box(0);
x_19 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_4);
lean_ctor_set(x_2, 0, x_19);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_20);
return x_2;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_2);
x_21 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_4);
x_22 = l_Lean_RBNode_balLeft___redArg(x_21, x_5, x_6, x_7);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_27 = lean_nat_dec_lt(x_1, x_24);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_nat_dec_eq(x_1, x_24);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_RBNode_isBlack___redArg(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_box(0);
x_31 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_26);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_33);
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_26);
x_35 = l_Lean_RBNode_balRight___redArg(x_23, x_24, x_25, x_34);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_25);
lean_dec(x_24);
x_36 = l_Lean_RBNode_appendTrees___redArg(x_23, x_26);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = l_Lean_RBNode_isBlack___redArg(x_23);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_box(0);
x_39 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_23);
x_40 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_40, 2, x_25);
lean_ctor_set(x_40, 3, x_26);
x_41 = lean_unbox(x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_41);
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_23);
x_43 = l_Lean_RBNode_balLeft___redArg(x_42, x_24, x_25, x_26);
return x_43;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_2);
x_4 = l_Lean_RBNode_setBlack___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_eraseJoinPointDecl(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_LocalContext_getType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
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
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
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
LEAN_EXPORT uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
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
static lean_object* _init_l_Lean_IR_instAlphaEqvVarId___closed__0() {
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
x_1 = l_Lean_IR_instAlphaEqvVarId___closed__0;
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
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
return x_12;
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
static lean_object* _init_l_Lean_IR_instAlphaEqvArg___closed__0() {
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
x_1 = l_Lean_IR_instAlphaEqvArg___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_9 = lean_array_fget(x_2, x_8);
x_10 = lean_array_fget(x_3, x_8);
x_11 = l_Lean_IR_Arg_alphaEqv(x_1, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_8);
return x_11;
}
else
{
x_4 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___redArg(x_1, x_2, x_3, x_5);
return x_7;
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
if (x_6 == 0)
{
lean_dec(x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at___Lean_IR_args_alphaEqv_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
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
static lean_object* _init_l_Lean_IR_instAlphaEqvArrayArg___closed__0() {
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
x_1 = l_Lean_IR_instAlphaEqvArrayArg___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_Expr_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
x_22 = l_Lean_IR_CtorInfo_beq(x_18, x_20);
if (x_22 == 0)
{
return x_22;
}
else
{
uint8_t x_23; 
x_23 = l_Lean_IR_args_alphaEqv(x_1, x_19, x_21);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
x_4 = x_26;
x_5 = x_27;
x_6 = x_28;
x_7 = x_29;
goto block_10;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
return x_31;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_40; uint8_t x_44; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_ctor_get(x_3, 1);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_39 = lean_ctor_get(x_3, 2);
x_44 = l_Lean_IR_VarId_alphaEqv(x_1, x_32, x_36);
if (x_44 == 0)
{
x_40 = x_44;
goto block_43;
}
else
{
uint8_t x_45; 
x_45 = l_Lean_IR_CtorInfo_beq(x_33, x_37);
x_40 = x_45;
goto block_43;
}
block_43:
{
if (x_40 == 0)
{
return x_40;
}
else
{
if (x_34 == 0)
{
if (x_38 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_IR_args_alphaEqv(x_1, x_35, x_39);
return x_41;
}
else
{
return x_34;
}
}
else
{
if (x_38 == 0)
{
return x_38;
}
else
{
uint8_t x_42; 
x_42 = l_Lean_IR_args_alphaEqv(x_1, x_35, x_39);
return x_42;
}
}
}
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
return x_47;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
x_4 = x_48;
x_5 = x_49;
x_6 = x_50;
x_7 = x_51;
goto block_10;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
return x_53;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
x_56 = lean_ctor_get(x_3, 0);
x_57 = lean_ctor_get(x_3, 1);
x_4 = x_54;
x_5 = x_55;
x_6 = x_56;
x_7 = x_57;
goto block_10;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_box(0);
x_59 = lean_unbox(x_58);
return x_59;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_69; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
x_62 = lean_ctor_get(x_2, 2);
x_63 = lean_ctor_get(x_3, 0);
x_64 = lean_ctor_get(x_3, 1);
x_65 = lean_ctor_get(x_3, 2);
x_69 = lean_nat_dec_eq(x_60, x_63);
if (x_69 == 0)
{
x_66 = x_69;
goto block_68;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_eq(x_61, x_64);
x_66 = x_70;
goto block_68;
}
block_68:
{
if (x_66 == 0)
{
return x_66;
}
else
{
uint8_t x_67; 
x_67 = l_Lean_IR_VarId_alphaEqv(x_1, x_62, x_65);
return x_67;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_box(0);
x_72 = lean_unbox(x_71);
return x_72;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get(x_3, 0);
x_76 = lean_ctor_get(x_3, 1);
x_11 = x_73;
x_12 = x_74;
x_13 = x_75;
x_14 = x_76;
goto block_17;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_box(0);
x_78 = lean_unbox(x_77);
return x_78;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_2, 0);
x_80 = lean_ctor_get(x_2, 1);
x_81 = lean_ctor_get(x_3, 0);
x_82 = lean_ctor_get(x_3, 1);
x_11 = x_79;
x_12 = x_80;
x_13 = x_81;
x_14 = x_82;
goto block_17;
}
else
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_box(0);
x_84 = lean_unbox(x_83);
return x_84;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_2, 0);
x_86 = lean_ctor_get(x_2, 1);
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_ctor_get(x_3, 1);
x_89 = l_Lean_IR_VarId_alphaEqv(x_1, x_85, x_87);
if (x_89 == 0)
{
return x_89;
}
else
{
uint8_t x_90; 
x_90 = l_Lean_IR_args_alphaEqv(x_1, x_86, x_88);
return x_90;
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_box(0);
x_92 = lean_unbox(x_91);
return x_92;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_2, 0);
x_94 = lean_ctor_get(x_2, 1);
x_95 = lean_ctor_get(x_3, 0);
x_96 = lean_ctor_get(x_3, 1);
x_97 = l_Lean_IR_IRType_beq(x_93, x_95);
if (x_97 == 0)
{
return x_97;
}
else
{
uint8_t x_98; 
x_98 = l_Lean_IR_VarId_alphaEqv(x_1, x_94, x_96);
return x_98;
}
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_box(0);
x_100 = lean_unbox(x_99);
return x_100;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_2, 0);
x_102 = lean_ctor_get(x_3, 0);
x_103 = l_Lean_IR_VarId_alphaEqv(x_1, x_101, x_102);
return x_103;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_box(0);
x_105 = lean_unbox(x_104);
return x_105;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = lean_ctor_get(x_2, 0);
x_107 = lean_ctor_get(x_3, 0);
x_108 = l_Lean_IR_LitVal_beq(x_106, x_107);
return x_108;
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_box(0);
x_110 = lean_unbox(x_109);
return x_110;
}
}
default: 
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_2, 0);
x_112 = lean_ctor_get(x_3, 0);
x_113 = l_Lean_IR_VarId_alphaEqv(x_1, x_111, x_112);
return x_113;
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_box(0);
x_115 = lean_unbox(x_114);
return x_115;
}
}
}
block_10:
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
if (x_8 == 0)
{
return x_8;
}
else
{
uint8_t x_9; 
x_9 = l_Lean_IR_VarId_alphaEqv(x_1, x_5, x_7);
return x_9;
}
}
block_17:
{
uint8_t x_15; 
x_15 = lean_name_eq(x_11, x_13);
if (x_15 == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l_Lean_IR_args_alphaEqv(x_1, x_12, x_14);
return x_16;
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
static lean_object* _init_l_Lean_IR_instAlphaEqvExpr___closed__0() {
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
x_1 = l_Lean_IR_instAlphaEqvExpr___closed__0;
return x_1;
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
x_5 = l_Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0___redArg(x_1, x_2, x_3);
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
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_15 = l_Lean_IR_IRType_beq(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (x_15 == 0)
{
x_10 = x_15;
goto block_14;
}
else
{
if (x_5 == 0)
{
if (x_8 == 0)
{
x_10 = x_15;
goto block_14;
}
else
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
}
else
{
x_10 = x_8;
goto block_14;
}
}
block_14:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_IR_addVarRename(x_1, x_4, x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_IR_instInhabitedParam;
x_11 = lean_array_get(x_10, x_1, x_5);
x_12 = lean_array_get(x_10, x_2, x_5);
x_13 = l_Lean_IR_addParamRename(x_4, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_14;
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addParamsRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___redArg(x_2, x_3, x_10, x_1, x_8);
lean_dec(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_IR_addParamsRename_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
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
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_12; lean_object* x_13; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_4, x_7);
lean_dec(x_4);
x_12 = lean_array_fget(x_2, x_8);
x_13 = lean_array_fget(x_3, x_8);
if (lean_obj_tag(x_12) == 0)
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_IR_CtorInfo_beq(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
x_9 = x_18;
goto block_11;
}
else
{
uint8_t x_19; 
lean_inc(x_1);
x_19 = l_Lean_IR_FnBody_alphaEqv(x_1, x_15, x_17);
x_9 = x_19;
goto block_11;
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_1);
return x_6;
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
lean_inc(x_1);
x_22 = l_Lean_IR_FnBody_alphaEqv(x_1, x_20, x_21);
x_9 = x_22;
goto block_11;
}
}
block_11:
{
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_1);
return x_9;
}
else
{
x_4 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___redArg(x_1, x_2, x_3, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_47; 
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
x_47 = l_Lean_IR_IRType_beq(x_36, x_40);
lean_dec(x_40);
lean_dec(x_36);
if (x_47 == 0)
{
lean_dec(x_41);
lean_dec(x_37);
x_43 = x_47;
goto block_46;
}
else
{
uint8_t x_48; 
x_48 = l_Lean_IR_Expr_alphaEqv(x_1, x_37, x_41);
lean_dec(x_41);
lean_dec(x_37);
x_43 = x_48;
goto block_46;
}
block_46:
{
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_1);
return x_43;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_IR_addVarRename(x_1, x_35, x_39);
x_1 = x_44;
x_2 = x_38;
x_3 = x_42;
goto _start;
}
}
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_unbox(x_49);
return x_50;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 3);
lean_inc(x_54);
lean_dec(x_2);
x_55 = lean_ctor_get(x_3, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
lean_inc(x_1);
x_59 = l_Lean_IR_addParamsRename(x_1, x_52, x_56);
lean_dec(x_56);
lean_dec(x_52);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_51);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_unbox(x_60);
return x_61;
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l_Lean_IR_FnBody_alphaEqv(x_62, x_53, x_57);
if (x_63 == 0)
{
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_51);
lean_dec(x_1);
return x_63;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_IR_addVarRename(x_1, x_51, x_55);
x_1 = x_64;
x_2 = x_54;
x_3 = x_58;
goto _start;
}
}
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_box(0);
x_67 = lean_unbox(x_66);
return x_67;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_80; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_2, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 3);
lean_inc(x_71);
lean_dec(x_2);
x_72 = lean_ctor_get(x_3, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_3, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_3, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 3);
lean_inc(x_75);
lean_dec(x_3);
x_80 = l_Lean_IR_VarId_alphaEqv(x_1, x_68, x_72);
lean_dec(x_72);
lean_dec(x_68);
if (x_80 == 0)
{
lean_dec(x_73);
lean_dec(x_69);
x_76 = x_80;
goto block_79;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_eq(x_69, x_73);
lean_dec(x_73);
lean_dec(x_69);
x_76 = x_81;
goto block_79;
}
block_79:
{
if (x_76 == 0)
{
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_1);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = l_Lean_IR_Arg_alphaEqv(x_1, x_70, x_74);
lean_dec(x_74);
lean_dec(x_70);
if (x_77 == 0)
{
lean_dec(x_75);
lean_dec(x_71);
lean_dec(x_1);
return x_77;
}
else
{
x_2 = x_71;
x_3 = x_75;
goto _start;
}
}
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_unbox(x_82);
return x_83;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_93; 
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
lean_dec(x_2);
x_87 = lean_ctor_get(x_3, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_3, 2);
lean_inc(x_89);
lean_dec(x_3);
x_93 = l_Lean_IR_VarId_alphaEqv(x_1, x_84, x_87);
lean_dec(x_87);
lean_dec(x_84);
if (x_93 == 0)
{
lean_dec(x_88);
lean_dec(x_85);
x_90 = x_93;
goto block_92;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_eq(x_85, x_88);
lean_dec(x_88);
lean_dec(x_85);
x_90 = x_94;
goto block_92;
}
block_92:
{
if (x_90 == 0)
{
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_1);
return x_90;
}
else
{
x_2 = x_86;
x_3 = x_89;
goto _start;
}
}
}
else
{
lean_object* x_95; uint8_t x_96; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_box(0);
x_96 = lean_unbox(x_95);
return x_96;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_109; 
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 3);
lean_inc(x_100);
lean_dec(x_2);
x_101 = lean_ctor_get(x_3, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_3, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_3, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_3, 3);
lean_inc(x_104);
lean_dec(x_3);
x_109 = l_Lean_IR_VarId_alphaEqv(x_1, x_97, x_101);
lean_dec(x_101);
lean_dec(x_97);
if (x_109 == 0)
{
lean_dec(x_102);
lean_dec(x_98);
x_105 = x_109;
goto block_108;
}
else
{
uint8_t x_110; 
x_110 = lean_nat_dec_eq(x_98, x_102);
lean_dec(x_102);
lean_dec(x_98);
x_105 = x_110;
goto block_108;
}
block_108:
{
if (x_105 == 0)
{
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
return x_105;
}
else
{
uint8_t x_106; 
x_106 = l_Lean_IR_VarId_alphaEqv(x_1, x_99, x_103);
lean_dec(x_103);
lean_dec(x_99);
if (x_106 == 0)
{
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_1);
return x_106;
}
else
{
x_2 = x_100;
x_3 = x_104;
goto _start;
}
}
}
}
else
{
lean_object* x_111; uint8_t x_112; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = lean_box(0);
x_112 = lean_unbox(x_111);
return x_112;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; uint8_t x_131; 
x_113 = lean_ctor_get(x_2, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_2, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_2, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_2, 4);
lean_inc(x_117);
x_118 = lean_ctor_get(x_2, 5);
lean_inc(x_118);
lean_dec(x_2);
x_119 = lean_ctor_get(x_3, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_3, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_3, 2);
lean_inc(x_121);
x_122 = lean_ctor_get(x_3, 3);
lean_inc(x_122);
x_123 = lean_ctor_get(x_3, 4);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 5);
lean_inc(x_124);
lean_dec(x_3);
x_125 = lean_nat_dec_eq(x_115, x_121);
lean_dec(x_121);
lean_dec(x_115);
x_131 = l_Lean_IR_VarId_alphaEqv(x_1, x_113, x_119);
lean_dec(x_119);
lean_dec(x_113);
if (x_131 == 0)
{
lean_dec(x_120);
lean_dec(x_114);
x_126 = x_131;
goto block_130;
}
else
{
uint8_t x_132; 
x_132 = lean_nat_dec_eq(x_114, x_120);
lean_dec(x_120);
lean_dec(x_114);
x_126 = x_132;
goto block_130;
}
block_130:
{
if (x_126 == 0)
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_1);
return x_126;
}
else
{
if (x_125 == 0)
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_1);
return x_125;
}
else
{
uint8_t x_127; 
x_127 = l_Lean_IR_VarId_alphaEqv(x_1, x_116, x_122);
lean_dec(x_122);
lean_dec(x_116);
if (x_127 == 0)
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_1);
return x_127;
}
else
{
uint8_t x_128; 
x_128 = l_Lean_IR_IRType_beq(x_117, x_123);
lean_dec(x_123);
lean_dec(x_117);
if (x_128 == 0)
{
lean_dec(x_124);
lean_dec(x_118);
lean_dec(x_1);
return x_128;
}
else
{
x_2 = x_118;
x_3 = x_124;
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_133; uint8_t x_134; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_box(0);
x_134 = lean_unbox(x_133);
return x_134;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; 
x_135 = lean_ctor_get(x_2, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_138 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_139 = lean_ctor_get(x_2, 2);
lean_inc(x_139);
lean_dec(x_2);
x_140 = lean_ctor_get(x_3, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_3, 1);
lean_inc(x_141);
x_142 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_143 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_144 = lean_ctor_get(x_3, 2);
lean_inc(x_144);
lean_dec(x_3);
x_21 = x_1;
x_22 = x_135;
x_23 = x_136;
x_24 = x_137;
x_25 = x_138;
x_26 = x_139;
x_27 = x_140;
x_28 = x_141;
x_29 = x_142;
x_30 = x_143;
x_31 = x_144;
goto block_34;
}
else
{
lean_object* x_145; uint8_t x_146; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_box(0);
x_146 = lean_unbox(x_145);
return x_146;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; lean_object* x_156; 
x_147 = lean_ctor_get(x_2, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_2, 1);
lean_inc(x_148);
x_149 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_150 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_151 = lean_ctor_get(x_2, 2);
lean_inc(x_151);
lean_dec(x_2);
x_152 = lean_ctor_get(x_3, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_3, 1);
lean_inc(x_153);
x_154 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_155 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_156 = lean_ctor_get(x_3, 2);
lean_inc(x_156);
lean_dec(x_3);
x_21 = x_1;
x_22 = x_147;
x_23 = x_148;
x_24 = x_149;
x_25 = x_150;
x_26 = x_151;
x_27 = x_152;
x_28 = x_153;
x_29 = x_154;
x_30 = x_155;
x_31 = x_156;
goto block_34;
}
else
{
lean_object* x_157; uint8_t x_158; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_box(0);
x_158 = lean_unbox(x_157);
return x_158;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_159 = lean_ctor_get(x_2, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_2, 1);
lean_inc(x_160);
lean_dec(x_2);
x_161 = lean_ctor_get(x_3, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_3, 1);
lean_inc(x_162);
lean_dec(x_3);
x_163 = l_Lean_IR_VarId_alphaEqv(x_1, x_159, x_161);
lean_dec(x_161);
lean_dec(x_159);
if (x_163 == 0)
{
lean_dec(x_162);
lean_dec(x_160);
lean_dec(x_1);
return x_163;
}
else
{
x_2 = x_160;
x_3 = x_162;
goto _start;
}
}
else
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_box(0);
x_166 = lean_unbox(x_165);
return x_166;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_2, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_2, 1);
lean_inc(x_168);
lean_dec(x_2);
x_169 = lean_ctor_get(x_3, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_3, 1);
lean_inc(x_170);
lean_dec(x_3);
x_171 = l_Lean_KVMap_eqv(x_167, x_169);
if (x_171 == 0)
{
lean_dec(x_170);
lean_dec(x_168);
lean_dec(x_1);
return x_171;
}
else
{
x_2 = x_168;
x_3 = x_170;
goto _start;
}
}
else
{
lean_object* x_173; uint8_t x_174; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_box(0);
x_174 = lean_unbox(x_173);
return x_174;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_187; 
x_175 = lean_ctor_get(x_2, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_2, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_2, 3);
lean_inc(x_177);
lean_dec(x_2);
x_178 = lean_ctor_get(x_3, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_3, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_3, 3);
lean_inc(x_180);
lean_dec(x_3);
x_187 = lean_name_eq(x_175, x_178);
lean_dec(x_178);
lean_dec(x_175);
if (x_187 == 0)
{
lean_dec(x_179);
lean_dec(x_176);
x_181 = x_187;
goto block_186;
}
else
{
uint8_t x_188; 
x_188 = l_Lean_IR_VarId_alphaEqv(x_1, x_176, x_179);
lean_dec(x_179);
lean_dec(x_176);
x_181 = x_188;
goto block_186;
}
block_186:
{
if (x_181 == 0)
{
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_1);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_array_get_size(x_177);
x_183 = lean_array_get_size(x_180);
x_184 = lean_nat_dec_eq(x_182, x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_1);
return x_184;
}
else
{
uint8_t x_185; 
x_185 = l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___redArg(x_1, x_177, x_180, x_182);
lean_dec(x_180);
lean_dec(x_177);
return x_185;
}
}
}
}
else
{
lean_object* x_189; uint8_t x_190; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_box(0);
x_190 = lean_unbox(x_189);
return x_190;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_191 = lean_ctor_get(x_2, 0);
lean_inc(x_191);
lean_dec(x_2);
x_192 = lean_ctor_get(x_3, 0);
lean_inc(x_192);
lean_dec(x_3);
x_193 = l_Lean_IR_Arg_alphaEqv(x_1, x_191, x_192);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_1);
return x_193;
}
else
{
lean_object* x_194; uint8_t x_195; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_box(0);
x_195 = lean_unbox(x_194);
return x_195;
}
}
case 12:
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_2, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_2, 1);
lean_inc(x_197);
lean_dec(x_2);
x_198 = lean_ctor_get(x_3, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_3, 1);
lean_inc(x_199);
lean_dec(x_3);
x_200 = lean_nat_dec_eq(x_196, x_198);
lean_dec(x_198);
lean_dec(x_196);
if (x_200 == 0)
{
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_1);
return x_200;
}
else
{
uint8_t x_201; 
x_201 = l_Lean_IR_args_alphaEqv(x_1, x_197, x_199);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_1);
return x_201;
}
}
else
{
lean_object* x_202; uint8_t x_203; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_box(0);
x_203 = lean_unbox(x_202);
return x_203;
}
}
default: 
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 13)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_box(1);
x_205 = lean_unbox(x_204);
return x_205;
}
else
{
lean_object* x_206; uint8_t x_207; 
lean_dec(x_3);
x_206 = lean_box(0);
x_207 = lean_unbox(x_206);
return x_207;
}
}
}
block_11:
{
if (x_7 == 0)
{
if (x_4 == 0)
{
x_1 = x_5;
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
}
else
{
if (x_4 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_4;
}
else
{
x_1 = x_5;
x_2 = x_6;
x_3 = x_8;
goto _start;
}
}
}
block_20:
{
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
return x_19;
}
else
{
if (x_16 == 0)
{
if (x_15 == 0)
{
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_17;
x_8 = x_18;
goto block_11;
}
else
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
return x_16;
}
}
else
{
if (x_15 == 0)
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
return x_15;
}
else
{
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_17;
x_8 = x_18;
goto block_11;
}
}
}
}
block_34:
{
uint8_t x_32; 
x_32 = l_Lean_IR_VarId_alphaEqv(x_21, x_22, x_27);
lean_dec(x_27);
lean_dec(x_22);
if (x_32 == 0)
{
lean_dec(x_28);
lean_dec(x_23);
x_12 = x_30;
x_13 = x_21;
x_14 = x_26;
x_15 = x_29;
x_16 = x_24;
x_17 = x_25;
x_18 = x_31;
x_19 = x_32;
goto block_20;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_23, x_28);
lean_dec(x_28);
lean_dec(x_23);
x_12 = x_30;
x_13 = x_21;
x_14 = x_26;
x_15 = x_29;
x_16 = x_24;
x_17 = x_25;
x_18 = x_31;
x_19 = x_33;
goto block_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
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
static lean_object* _init_l_Lean_IR_instBEqFnBody___closed__0() {
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
x_1 = l_Lean_IR_instBEqFnBody___closed__0;
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
static lean_object* _init_l_Lean_IR_mkIf___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_mkIf___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkIf___closed__2;
x_2 = l_Lean_IR_mkIf___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_IR_mkIf___closed__3;
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkIf___closed__5;
x_2 = l_Lean_IR_mkIf___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_IR_mkIf___closed__6;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_IR_mkIf___closed__8() {
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
x_4 = l_Lean_IR_mkIf___closed__1;
x_5 = lean_box(1);
x_6 = l_Lean_IR_mkIf___closed__4;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = l_Lean_IR_mkIf___closed__7;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = l_Lean_IR_mkIf___closed__8;
x_11 = lean_array_push(x_10, x_7);
x_12 = lean_array_push(x_11, x_9);
x_13 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_5);
lean_ctor_set(x_13, 3, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_unbox_float", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_unbox_uint32", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_unbox_uint64", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_unbox_usize", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_unbox_float32", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_getUnboxOpName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_unbox", 10, 10);
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
x_2 = l_Lean_IR_getUnboxOpName___closed__0;
return x_2;
}
case 3:
{
lean_object* x_3; 
x_3 = l_Lean_IR_getUnboxOpName___closed__1;
return x_3;
}
case 4:
{
lean_object* x_4; 
x_4 = l_Lean_IR_getUnboxOpName___closed__2;
return x_4;
}
case 5:
{
lean_object* x_5; 
x_5 = l_Lean_IR_getUnboxOpName___closed__3;
return x_5;
}
case 9:
{
lean_object* x_6; 
x_6 = l_Lean_IR_getUnboxOpName___closed__4;
return x_6;
}
default: 
{
lean_object* x_7; 
x_7 = l_Lean_IR_getUnboxOpName___closed__5;
return x_7;
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
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lean_IR_reprVarId___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_ = _init_l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_();
lean_mark_persistent(l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_);
l_Lean_IR_instReprVarId___closed__0 = _init_l_Lean_IR_instReprVarId___closed__0();
lean_mark_persistent(l_Lean_IR_instReprVarId___closed__0);
l_Lean_IR_instReprVarId = _init_l_Lean_IR_instReprVarId();
lean_mark_persistent(l_Lean_IR_instReprVarId);
l_Lean_IR_instInhabitedJoinPointId = _init_l_Lean_IR_instInhabitedJoinPointId();
lean_mark_persistent(l_Lean_IR_instInhabitedJoinPointId);
l_Lean_IR_instReprJoinPointId___closed__0 = _init_l_Lean_IR_instReprJoinPointId___closed__0();
lean_mark_persistent(l_Lean_IR_instReprJoinPointId___closed__0);
l_Lean_IR_instReprJoinPointId = _init_l_Lean_IR_instReprJoinPointId();
lean_mark_persistent(l_Lean_IR_instReprJoinPointId);
l_Lean_IR_instBEqVarId = _init_l_Lean_IR_instBEqVarId();
lean_mark_persistent(l_Lean_IR_instBEqVarId);
l_Lean_IR_instToStringVarId___lam__0___closed__0 = _init_l_Lean_IR_instToStringVarId___lam__0___closed__0();
lean_mark_persistent(l_Lean_IR_instToStringVarId___lam__0___closed__0);
l_Lean_IR_instToStringVarId = _init_l_Lean_IR_instToStringVarId();
lean_mark_persistent(l_Lean_IR_instToStringVarId);
l_Lean_IR_instToFormatVarId = _init_l_Lean_IR_instToFormatVarId();
lean_mark_persistent(l_Lean_IR_instToFormatVarId);
l_Lean_IR_instHashableVarId = _init_l_Lean_IR_instHashableVarId();
lean_mark_persistent(l_Lean_IR_instHashableVarId);
l_Lean_IR_instBEqJoinPointId___closed__0 = _init_l_Lean_IR_instBEqJoinPointId___closed__0();
lean_mark_persistent(l_Lean_IR_instBEqJoinPointId___closed__0);
l_Lean_IR_instBEqJoinPointId = _init_l_Lean_IR_instBEqJoinPointId();
lean_mark_persistent(l_Lean_IR_instBEqJoinPointId);
l_Lean_IR_instToStringJoinPointId___lam__0___closed__0 = _init_l_Lean_IR_instToStringJoinPointId___lam__0___closed__0();
lean_mark_persistent(l_Lean_IR_instToStringJoinPointId___lam__0___closed__0);
l_Lean_IR_instToStringJoinPointId = _init_l_Lean_IR_instToStringJoinPointId();
lean_mark_persistent(l_Lean_IR_instToStringJoinPointId);
l_Lean_IR_instToFormatJoinPointId = _init_l_Lean_IR_instToFormatJoinPointId();
lean_mark_persistent(l_Lean_IR_instToFormatJoinPointId);
l_Lean_IR_instHashableJoinPointId___closed__0 = _init_l_Lean_IR_instHashableJoinPointId___closed__0();
lean_mark_persistent(l_Lean_IR_instHashableJoinPointId___closed__0);
l_Lean_IR_instHashableJoinPointId = _init_l_Lean_IR_instHashableJoinPointId();
lean_mark_persistent(l_Lean_IR_instHashableJoinPointId);
l_Lean_IR_MData_empty = _init_l_Lean_IR_MData_empty();
lean_mark_persistent(l_Lean_IR_MData_empty);
l_Lean_IR_instInhabitedIRType = _init_l_Lean_IR_instInhabitedIRType();
lean_mark_persistent(l_Lean_IR_instInhabitedIRType);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__0 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__0();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__0);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__1 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__1();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__1);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__3 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__3();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__3);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__4 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__4();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__4);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__5 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__5();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__5);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__6 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__6();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__6);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__7 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__7();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__7);
l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__8 = _init_l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__8();
lean_mark_persistent(l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__8);
l_Lean_IR_reprIRType___closed__0____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__0____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__0____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__1____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__1____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__1____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__2____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__2____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__2____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__3____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__3____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__3____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__4____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__4____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__4____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__5____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__5____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__5____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__6____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__6____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__6____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__7____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__7____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__7____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__8____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__8____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__8____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__9____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__9____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__9____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__10____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__10____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__10____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__11____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__11____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__11____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__12____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__12____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__12____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__13____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__13____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__13____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__14____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__14____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__14____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__15____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__15____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__15____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__16____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__16____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__16____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__17____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__17____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__17____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__18____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__18____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__18____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__19____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__19____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__19____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__21____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__21____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__21____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__22____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__22____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__22____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__23____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__23____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__23____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__24____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__24____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__24____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__25____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__25____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__25____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_reprIRType___closed__26____x40_Lean_Compiler_IR_Basic___hyg_358_ = _init_l_Lean_IR_reprIRType___closed__26____x40_Lean_Compiler_IR_Basic___hyg_358_();
lean_mark_persistent(l_Lean_IR_reprIRType___closed__26____x40_Lean_Compiler_IR_Basic___hyg_358_);
l_Lean_IR_instReprIRType___closed__0 = _init_l_Lean_IR_instReprIRType___closed__0();
lean_mark_persistent(l_Lean_IR_instReprIRType___closed__0);
l_Lean_IR_instReprIRType = _init_l_Lean_IR_instReprIRType();
lean_mark_persistent(l_Lean_IR_instReprIRType);
l_Lean_IR_IRType_instBEq___closed__0 = _init_l_Lean_IR_IRType_instBEq___closed__0();
lean_mark_persistent(l_Lean_IR_IRType_instBEq___closed__0);
l_Lean_IR_IRType_instBEq = _init_l_Lean_IR_IRType_instBEq();
lean_mark_persistent(l_Lean_IR_IRType_instBEq);
l_Lean_IR_instInhabitedArg___closed__0 = _init_l_Lean_IR_instInhabitedArg___closed__0();
lean_mark_persistent(l_Lean_IR_instInhabitedArg___closed__0);
l_Lean_IR_instInhabitedArg = _init_l_Lean_IR_instInhabitedArg();
lean_mark_persistent(l_Lean_IR_instInhabitedArg);
l_Lean_IR_instBEqArg___closed__0 = _init_l_Lean_IR_instBEqArg___closed__0();
lean_mark_persistent(l_Lean_IR_instBEqArg___closed__0);
l_Lean_IR_instBEqArg = _init_l_Lean_IR_instBEqArg();
lean_mark_persistent(l_Lean_IR_instBEqArg);
l_Lean_IR_instBEqLitVal___closed__0 = _init_l_Lean_IR_instBEqLitVal___closed__0();
lean_mark_persistent(l_Lean_IR_instBEqLitVal___closed__0);
l_Lean_IR_instBEqLitVal = _init_l_Lean_IR_instBEqLitVal();
lean_mark_persistent(l_Lean_IR_instBEqLitVal);
l_Lean_IR_instInhabitedCtorInfo___closed__0 = _init_l_Lean_IR_instInhabitedCtorInfo___closed__0();
lean_mark_persistent(l_Lean_IR_instInhabitedCtorInfo___closed__0);
l_Lean_IR_instInhabitedCtorInfo = _init_l_Lean_IR_instInhabitedCtorInfo();
lean_mark_persistent(l_Lean_IR_instInhabitedCtorInfo);
l_Lean_IR_reprCtorInfo___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__12____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__12____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__12____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_reprCtorInfo___redArg___closed__13____x40_Lean_Compiler_IR_Basic___hyg_1557_ = _init_l_Lean_IR_reprCtorInfo___redArg___closed__13____x40_Lean_Compiler_IR_Basic___hyg_1557_();
lean_mark_persistent(l_Lean_IR_reprCtorInfo___redArg___closed__13____x40_Lean_Compiler_IR_Basic___hyg_1557_);
l_Lean_IR_instReprCtorInfo___closed__0 = _init_l_Lean_IR_instReprCtorInfo___closed__0();
lean_mark_persistent(l_Lean_IR_instReprCtorInfo___closed__0);
l_Lean_IR_instReprCtorInfo = _init_l_Lean_IR_instReprCtorInfo();
lean_mark_persistent(l_Lean_IR_instReprCtorInfo);
l_Lean_IR_instBEqCtorInfo___closed__0 = _init_l_Lean_IR_instBEqCtorInfo___closed__0();
lean_mark_persistent(l_Lean_IR_instBEqCtorInfo___closed__0);
l_Lean_IR_instBEqCtorInfo = _init_l_Lean_IR_instBEqCtorInfo();
lean_mark_persistent(l_Lean_IR_instBEqCtorInfo);
l_Lean_IR_instInhabitedExpr___closed__0 = _init_l_Lean_IR_instInhabitedExpr___closed__0();
lean_mark_persistent(l_Lean_IR_instInhabitedExpr___closed__0);
l_Lean_IR_instInhabitedExpr___closed__1 = _init_l_Lean_IR_instInhabitedExpr___closed__1();
lean_mark_persistent(l_Lean_IR_instInhabitedExpr___closed__1);
l_Lean_IR_instInhabitedExpr = _init_l_Lean_IR_instInhabitedExpr();
lean_mark_persistent(l_Lean_IR_instInhabitedExpr);
l_Lean_IR_instInhabitedParam___closed__0 = _init_l_Lean_IR_instInhabitedParam___closed__0();
lean_mark_persistent(l_Lean_IR_instInhabitedParam___closed__0);
l_Lean_IR_instInhabitedParam = _init_l_Lean_IR_instInhabitedParam();
lean_mark_persistent(l_Lean_IR_instInhabitedParam);
l_Lean_IR_reprParam___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__0____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__1____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__2____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__3____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__4____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__5____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_reprParam___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_2264_ = _init_l_Lean_IR_reprParam___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_2264_();
lean_mark_persistent(l_Lean_IR_reprParam___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_2264_);
l_Lean_IR_instReprParam___closed__0 = _init_l_Lean_IR_instReprParam___closed__0();
lean_mark_persistent(l_Lean_IR_instReprParam___closed__0);
l_Lean_IR_instReprParam = _init_l_Lean_IR_instReprParam();
lean_mark_persistent(l_Lean_IR_instReprParam);
l_Lean_IR_instInhabitedFnBody = _init_l_Lean_IR_instInhabitedFnBody();
lean_mark_persistent(l_Lean_IR_instInhabitedFnBody);
l_Lean_IR_FnBody_nil = _init_l_Lean_IR_FnBody_nil();
lean_mark_persistent(l_Lean_IR_FnBody_nil);
l_Lean_IR_instInhabitedAlt___closed__0 = _init_l_Lean_IR_instInhabitedAlt___closed__0();
lean_mark_persistent(l_Lean_IR_instInhabitedAlt___closed__0);
l_Lean_IR_instInhabitedAlt = _init_l_Lean_IR_instInhabitedAlt();
lean_mark_persistent(l_Lean_IR_instInhabitedAlt);
l_Lean_IR_FnBody_flatten___closed__0 = _init_l_Lean_IR_FnBody_flatten___closed__0();
lean_mark_persistent(l_Lean_IR_FnBody_flatten___closed__0);
l_Lean_IR_reshapeAux___closed__0 = _init_l_Lean_IR_reshapeAux___closed__0();
lean_mark_persistent(l_Lean_IR_reshapeAux___closed__0);
l_Lean_IR_reshapeAux___closed__1 = _init_l_Lean_IR_reshapeAux___closed__1();
lean_mark_persistent(l_Lean_IR_reshapeAux___closed__1);
l_Lean_IR_reshapeAux___closed__2 = _init_l_Lean_IR_reshapeAux___closed__2();
lean_mark_persistent(l_Lean_IR_reshapeAux___closed__2);
l_Lean_IR_reshapeAux___closed__3 = _init_l_Lean_IR_reshapeAux___closed__3();
lean_mark_persistent(l_Lean_IR_reshapeAux___closed__3);
l_Lean_IR_modifyJPs___closed__0 = _init_l_Lean_IR_modifyJPs___closed__0();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__0);
l_Lean_IR_modifyJPs___closed__1 = _init_l_Lean_IR_modifyJPs___closed__1();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__1);
l_Lean_IR_modifyJPs___closed__2 = _init_l_Lean_IR_modifyJPs___closed__2();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__2);
l_Lean_IR_modifyJPs___closed__3 = _init_l_Lean_IR_modifyJPs___closed__3();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__3);
l_Lean_IR_modifyJPs___closed__4 = _init_l_Lean_IR_modifyJPs___closed__4();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__4);
l_Lean_IR_modifyJPs___closed__5 = _init_l_Lean_IR_modifyJPs___closed__5();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__5);
l_Lean_IR_modifyJPs___closed__6 = _init_l_Lean_IR_modifyJPs___closed__6();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__6);
l_Lean_IR_modifyJPs___closed__7 = _init_l_Lean_IR_modifyJPs___closed__7();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__7);
l_Lean_IR_modifyJPs___closed__8 = _init_l_Lean_IR_modifyJPs___closed__8();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__8);
l_Lean_IR_modifyJPs___closed__9 = _init_l_Lean_IR_modifyJPs___closed__9();
lean_mark_persistent(l_Lean_IR_modifyJPs___closed__9);
l_Lean_IR_instInhabitedDecl___closed__0 = _init_l_Lean_IR_instInhabitedDecl___closed__0();
lean_mark_persistent(l_Lean_IR_instInhabitedDecl___closed__0);
l_Lean_IR_instInhabitedDecl___closed__1 = _init_l_Lean_IR_instInhabitedDecl___closed__1();
lean_mark_persistent(l_Lean_IR_instInhabitedDecl___closed__1);
l_Lean_IR_instInhabitedDecl___closed__2 = _init_l_Lean_IR_instInhabitedDecl___closed__2();
lean_mark_persistent(l_Lean_IR_instInhabitedDecl___closed__2);
l_Lean_IR_instInhabitedDecl = _init_l_Lean_IR_instInhabitedDecl();
lean_mark_persistent(l_Lean_IR_instInhabitedDecl);
l_Lean_IR_Decl_updateBody_x21___closed__0 = _init_l_Lean_IR_Decl_updateBody_x21___closed__0();
lean_mark_persistent(l_Lean_IR_Decl_updateBody_x21___closed__0);
l_Lean_IR_Decl_updateBody_x21___closed__1 = _init_l_Lean_IR_Decl_updateBody_x21___closed__1();
lean_mark_persistent(l_Lean_IR_Decl_updateBody_x21___closed__1);
l_Lean_IR_Decl_updateBody_x21___closed__2 = _init_l_Lean_IR_Decl_updateBody_x21___closed__2();
lean_mark_persistent(l_Lean_IR_Decl_updateBody_x21___closed__2);
l_Lean_IR_Decl_updateBody_x21___closed__3 = _init_l_Lean_IR_Decl_updateBody_x21___closed__3();
lean_mark_persistent(l_Lean_IR_Decl_updateBody_x21___closed__3);
l_Lean_IR_instInhabitedIndexSet = _init_l_Lean_IR_instInhabitedIndexSet();
lean_mark_persistent(l_Lean_IR_instInhabitedIndexSet);
l_Lean_IR_instAlphaEqvVarId___closed__0 = _init_l_Lean_IR_instAlphaEqvVarId___closed__0();
lean_mark_persistent(l_Lean_IR_instAlphaEqvVarId___closed__0);
l_Lean_IR_instAlphaEqvVarId = _init_l_Lean_IR_instAlphaEqvVarId();
lean_mark_persistent(l_Lean_IR_instAlphaEqvVarId);
l_Lean_IR_instAlphaEqvArg___closed__0 = _init_l_Lean_IR_instAlphaEqvArg___closed__0();
lean_mark_persistent(l_Lean_IR_instAlphaEqvArg___closed__0);
l_Lean_IR_instAlphaEqvArg = _init_l_Lean_IR_instAlphaEqvArg();
lean_mark_persistent(l_Lean_IR_instAlphaEqvArg);
l_Lean_IR_instAlphaEqvArrayArg___closed__0 = _init_l_Lean_IR_instAlphaEqvArrayArg___closed__0();
lean_mark_persistent(l_Lean_IR_instAlphaEqvArrayArg___closed__0);
l_Lean_IR_instAlphaEqvArrayArg = _init_l_Lean_IR_instAlphaEqvArrayArg();
lean_mark_persistent(l_Lean_IR_instAlphaEqvArrayArg);
l_Lean_IR_instAlphaEqvExpr___closed__0 = _init_l_Lean_IR_instAlphaEqvExpr___closed__0();
lean_mark_persistent(l_Lean_IR_instAlphaEqvExpr___closed__0);
l_Lean_IR_instAlphaEqvExpr = _init_l_Lean_IR_instAlphaEqvExpr();
lean_mark_persistent(l_Lean_IR_instAlphaEqvExpr);
l_Lean_IR_instBEqFnBody___closed__0 = _init_l_Lean_IR_instBEqFnBody___closed__0();
lean_mark_persistent(l_Lean_IR_instBEqFnBody___closed__0);
l_Lean_IR_instBEqFnBody = _init_l_Lean_IR_instBEqFnBody();
lean_mark_persistent(l_Lean_IR_instBEqFnBody);
l_Lean_IR_instInhabitedVarIdSet = _init_l_Lean_IR_instInhabitedVarIdSet();
lean_mark_persistent(l_Lean_IR_instInhabitedVarIdSet);
l_Lean_IR_mkIf___closed__0 = _init_l_Lean_IR_mkIf___closed__0();
lean_mark_persistent(l_Lean_IR_mkIf___closed__0);
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
l_Lean_IR_getUnboxOpName___closed__0 = _init_l_Lean_IR_getUnboxOpName___closed__0();
lean_mark_persistent(l_Lean_IR_getUnboxOpName___closed__0);
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
