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
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Name_isMetaprogramming_spec__0(lean_object*, lean_object*);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_3 = l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_11 = l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_7);
return x_16;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = l_Lean_IR_reprVarId___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_3 = l_Lean_IR_reprVarId___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_4 = l_Nat_reprFast(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_11 = l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_7);
return x_16;
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
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; lean_object* x_31; lean_object* x_38; lean_object* x_45; lean_object* x_52; lean_object* x_59; lean_object* x_66; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_unsigned_to_nat(1024u);
x_74 = lean_nat_dec_le(x_73, x_2);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_3 = x_75;
goto block_9;
}
else
{
lean_object* x_76; 
x_76 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_3 = x_76;
goto block_9;
}
}
case 1:
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_unsigned_to_nat(1024u);
x_78 = lean_nat_dec_le(x_77, x_2);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_10 = x_79;
goto block_16;
}
else
{
lean_object* x_80; 
x_80 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_10 = x_80;
goto block_16;
}
}
case 2:
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_unsigned_to_nat(1024u);
x_82 = lean_nat_dec_le(x_81, x_2);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_17 = x_83;
goto block_23;
}
else
{
lean_object* x_84; 
x_84 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_17 = x_84;
goto block_23;
}
}
case 3:
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_unsigned_to_nat(1024u);
x_86 = lean_nat_dec_le(x_85, x_2);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_24 = x_87;
goto block_30;
}
else
{
lean_object* x_88; 
x_88 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_24 = x_88;
goto block_30;
}
}
case 4:
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_unsigned_to_nat(1024u);
x_90 = lean_nat_dec_le(x_89, x_2);
if (x_90 == 0)
{
lean_object* x_91; 
x_91 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_31 = x_91;
goto block_37;
}
else
{
lean_object* x_92; 
x_92 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_31 = x_92;
goto block_37;
}
}
case 5:
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_unsigned_to_nat(1024u);
x_94 = lean_nat_dec_le(x_93, x_2);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_38 = x_95;
goto block_44;
}
else
{
lean_object* x_96; 
x_96 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_38 = x_96;
goto block_44;
}
}
case 6:
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_unsigned_to_nat(1024u);
x_98 = lean_nat_dec_le(x_97, x_2);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_45 = x_99;
goto block_51;
}
else
{
lean_object* x_100; 
x_100 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_45 = x_100;
goto block_51;
}
}
case 7:
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_unsigned_to_nat(1024u);
x_102 = lean_nat_dec_le(x_101, x_2);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_52 = x_103;
goto block_58;
}
else
{
lean_object* x_104; 
x_104 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_52 = x_104;
goto block_58;
}
}
case 8:
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_unsigned_to_nat(1024u);
x_106 = lean_nat_dec_le(x_105, x_2);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_59 = x_107;
goto block_65;
}
else
{
lean_object* x_108; 
x_108 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_59 = x_108;
goto block_65;
}
}
case 9:
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_unsigned_to_nat(1024u);
x_110 = lean_nat_dec_le(x_109, x_2);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_66 = x_111;
goto block_72;
}
else
{
lean_object* x_112; 
x_112 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_66 = x_112;
goto block_72;
}
}
case 10:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_130; uint8_t x_131; 
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_1, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_115 = x_1;
} else {
 lean_dec_ref(x_1);
 x_115 = lean_box(0);
}
x_130 = lean_unsigned_to_nat(1024u);
x_131 = lean_nat_dec_le(x_130, x_2);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_116 = x_132;
goto block_129;
}
else
{
lean_object* x_133; 
x_133 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_116 = x_133;
goto block_129;
}
block_129:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
x_117 = lean_box(1);
x_118 = l_Lean_IR_reprIRType___closed__23____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_119 = lean_unsigned_to_nat(1024u);
x_120 = l_Option_repr___at___Lean_Environment_dbgFormatAsyncState_spec__6(x_113, x_119);
if (lean_is_scalar(x_115)) {
 x_121 = lean_alloc_ctor(5, 2, 0);
} else {
 x_121 = x_115;
 lean_ctor_set_tag(x_121, 5);
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
x_123 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0(x_114);
x_124 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_124);
x_126 = 0;
x_127 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*1, x_126);
x_128 = l_Repr_addAppParen(x_127, x_2);
return x_128;
}
}
default: 
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_151; uint8_t x_152; 
x_134 = lean_ctor_get(x_1, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_1, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_136 = x_1;
} else {
 lean_dec_ref(x_1);
 x_136 = lean_box(0);
}
x_151 = lean_unsigned_to_nat(1024u);
x_152 = lean_nat_dec_le(x_151, x_2);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_137 = x_153;
goto block_150;
}
else
{
lean_object* x_154; 
x_154 = l_Lean_IR_reprIRType___closed__20____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_137 = x_154;
goto block_150;
}
block_150:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_138 = lean_box(1);
x_139 = l_Lean_IR_reprIRType___closed__26____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_140 = lean_unsigned_to_nat(1024u);
x_141 = l_Lean_Name_reprPrec(x_134, x_140);
if (lean_is_scalar(x_136)) {
 x_142 = lean_alloc_ctor(5, 2, 0);
} else {
 x_142 = x_136;
 lean_ctor_set_tag(x_142, 5);
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_138);
x_144 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0(x_135);
x_145 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_146, 0, x_137);
lean_ctor_set(x_146, 1, x_145);
x_147 = 0;
x_148 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_147);
x_149 = l_Repr_addAppParen(x_148, x_2);
return x_149;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_IR_reprIRType___closed__1____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_IR_reprIRType___closed__3____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_IR_reprIRType___closed__5____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lean_IR_reprIRType___closed__7____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
block_37:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lean_IR_reprIRType___closed__9____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = l_Repr_addAppParen(x_35, x_2);
return x_36;
}
block_44:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = l_Lean_IR_reprIRType___closed__11____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = 0;
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = l_Repr_addAppParen(x_42, x_2);
return x_43;
}
block_51:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = l_Lean_IR_reprIRType___closed__13____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = 0;
x_49 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = l_Repr_addAppParen(x_49, x_2);
return x_50;
}
block_58:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l_Lean_IR_reprIRType___closed__15____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = 0;
x_56 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = l_Repr_addAppParen(x_56, x_2);
return x_57;
}
block_65:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_60 = l_Lean_IR_reprIRType___closed__17____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = 0;
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = l_Repr_addAppParen(x_63, x_2);
return x_64;
}
block_72:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = l_Lean_IR_reprIRType___closed__19____x40_Lean_Compiler_IR_Basic___hyg_358_;
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = 0;
x_70 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = l_Repr_addAppParen(x_70, x_2);
return x_71;
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
uint8_t x_21; 
x_21 = 1;
return x_21;
}
else
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
}
case 10:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_161____at___Lean_Name_isMetaprogramming_spec__0(x_23, x_25);
if (x_27 == 0)
{
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_array_get_size(x_24);
x_29 = lean_array_get_size(x_26);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_dec(x_28);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg(x_24, x_26, x_28);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = 0;
return x_32;
}
}
default: 
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_name_eq(x_33, x_35);
if (x_37 == 0)
{
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_array_get_size(x_34);
x_39 = lean_array_get_size(x_36);
x_40 = lean_nat_dec_eq(x_38, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_dec(x_38);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = l_Array_isEqvAux___at___Lean_IR_IRType_beq_spec__0___redArg(x_34, x_36, x_38);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = 0;
return x_42;
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
case 10:
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
case 11:
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
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
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_IR_reprCtorInfo___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
x_23 = l_Nat_reprFast(x_3);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_9);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_13);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
x_30 = l_Lean_IR_reprCtorInfo___redArg___closed__8____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
x_33 = l_Nat_reprFast(x_4);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_13);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_16);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_18);
x_40 = l_Lean_IR_reprCtorInfo___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
x_43 = l_Lean_IR_reprCtorInfo___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_44 = l_Nat_reprFast(x_5);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_13);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_16);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_18);
x_51 = l_Lean_IR_reprCtorInfo___redArg___closed__13____x40_Lean_Compiler_IR_Basic___hyg_1557_;
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
x_54 = l_Nat_reprFast(x_6);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_13);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_60 = l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_62 = l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_13);
return x_65;
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
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
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Array_Array_repr___at___Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358__spec__0___closed__2;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_IR_reprParam___redArg___closed__6____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = l_Lean_IR_reprParam___redArg___closed__7____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_22 = l_Bool_repr___redArg(x_3);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_11);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
x_28 = l_Lean_IR_reprParam___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
x_31 = l_Lean_IR_reprParam___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_2264_;
x_32 = l_Lean_IR_reprIRType____x40_Lean_Compiler_IR_Basic___hyg_358_(x_4, x_8);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_11);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_IR_reprVarId___redArg___closed__9____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_37 = l_Lean_IR_reprVarId___redArg___closed__10____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_Lean_IR_reprVarId___redArg___closed__11____x40_Lean_Compiler_IR_Basic___hyg_38_;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_11);
return x_42;
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
x_19 = lean_unsigned_to_nat(444u);
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
uint8_t x_5; 
x_5 = 2;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(x_2, x_9);
switch (x_12) {
case 0:
{
lean_object* x_13; 
x_13 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
case 1:
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
default: 
{
lean_object* x_14; 
x_14 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_14);
return x_1;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_19 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(x_2, x_16);
switch (x_19) {
case 0:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_15, x_2, x_3);
x_21 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_6);
return x_21;
}
case 1:
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*4, x_6);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_18, x_2, x_3);
x_24 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_6);
return x_24;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_29 = x_1;
} else {
 lean_dec_ref(x_1);
 x_29 = lean_box(0);
}
x_30 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg___lam__0(x_2, x_26);
switch (x_30) {
case 0:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_31 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_25, x_2, x_3);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*4);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 3);
lean_inc(x_36);
if (x_32 == 0)
{
if (lean_obj_tag(x_33) == 0)
{
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_51; 
lean_dec(x_29);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_31, 3);
lean_dec(x_52);
x_53 = lean_ctor_get(x_31, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_31, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_31, 0);
lean_dec(x_55);
lean_ctor_set(x_31, 0, x_36);
x_56 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_56, 0, x_31);
lean_ctor_set(x_56, 1, x_26);
lean_ctor_set(x_56, 2, x_27);
lean_ctor_set(x_56, 3, x_28);
lean_ctor_set_uint8(x_56, sizeof(void*)*4, x_6);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_31);
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_36);
lean_ctor_set(x_57, 1, x_34);
lean_ctor_set(x_57, 2, x_35);
lean_ctor_set(x_57, 3, x_36);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_32);
x_58 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_26);
lean_ctor_set(x_58, 2, x_27);
lean_ctor_set(x_58, 3, x_28);
lean_ctor_set_uint8(x_58, sizeof(void*)*4, x_6);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_31);
x_60 = lean_ctor_get(x_36, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_36, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_36, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_36, 3);
lean_inc(x_63);
lean_dec(x_36);
x_37 = x_33;
x_38 = x_34;
x_39 = x_35;
x_40 = x_60;
x_41 = x_61;
x_42 = x_62;
x_43 = x_63;
x_44 = x_26;
x_45 = x_27;
x_46 = x_28;
goto block_50;
}
else
{
uint8_t x_64; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
x_64 = !lean_is_exclusive(x_36);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_36, 3);
lean_dec(x_65);
x_66 = lean_ctor_get(x_36, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_36, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_36, 0);
lean_dec(x_68);
lean_ctor_set(x_36, 3, x_28);
lean_ctor_set(x_36, 2, x_27);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_6);
return x_36;
}
else
{
lean_object* x_69; 
lean_dec(x_36);
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_31);
lean_ctor_set(x_69, 1, x_26);
lean_ctor_set(x_69, 2, x_27);
lean_ctor_set(x_69, 3, x_28);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_6);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
x_70 = lean_ctor_get_uint8(x_33, sizeof(void*)*4);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_31);
x_71 = lean_ctor_get(x_33, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_33, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_33, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_33, 3);
lean_inc(x_74);
lean_dec(x_33);
x_37 = x_71;
x_38 = x_72;
x_39 = x_73;
x_40 = x_74;
x_41 = x_34;
x_42 = x_35;
x_43 = x_36;
x_44 = x_26;
x_45 = x_27;
x_46 = x_28;
goto block_50;
}
else
{
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_75; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
x_75 = !lean_is_exclusive(x_33);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_33, 3);
lean_dec(x_76);
x_77 = lean_ctor_get(x_33, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_33, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_33, 0);
lean_dec(x_79);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set(x_33, 2, x_27);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_6);
return x_33;
}
else
{
lean_object* x_80; 
lean_dec(x_33);
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_31);
lean_ctor_set(x_80, 1, x_26);
lean_ctor_set(x_80, 2, x_27);
lean_ctor_set(x_80, 3, x_28);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_6);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_31);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_31, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_31, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_31, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_31, 0);
lean_dec(x_85);
x_86 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_free_object(x_31);
x_87 = lean_ctor_get(x_36, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_36, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_36, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_36, 3);
lean_inc(x_90);
lean_dec(x_36);
x_37 = x_33;
x_38 = x_34;
x_39 = x_35;
x_40 = x_87;
x_41 = x_88;
x_42 = x_89;
x_43 = x_90;
x_44 = x_26;
x_45 = x_27;
x_46 = x_28;
goto block_50;
}
else
{
uint8_t x_91; 
lean_dec(x_29);
x_91 = !lean_is_exclusive(x_33);
if (x_91 == 0)
{
lean_object* x_92; 
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_86);
x_92 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_92, 0, x_31);
lean_ctor_set(x_92, 1, x_26);
lean_ctor_set(x_92, 2, x_27);
lean_ctor_set(x_92, 3, x_28);
lean_ctor_set_uint8(x_92, sizeof(void*)*4, x_6);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_33, 0);
x_94 = lean_ctor_get(x_33, 1);
x_95 = lean_ctor_get(x_33, 2);
x_96 = lean_ctor_get(x_33, 3);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_33);
x_97 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_95);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*4, x_86);
lean_ctor_set(x_31, 0, x_97);
x_98 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_98, 0, x_31);
lean_ctor_set(x_98, 1, x_26);
lean_ctor_set(x_98, 2, x_27);
lean_ctor_set(x_98, 3, x_28);
lean_ctor_set_uint8(x_98, sizeof(void*)*4, x_6);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_31);
x_99 = lean_ctor_get_uint8(x_36, sizeof(void*)*4);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_36, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_36, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_36, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_36, 3);
lean_inc(x_103);
lean_dec(x_36);
x_37 = x_33;
x_38 = x_34;
x_39 = x_35;
x_40 = x_100;
x_41 = x_101;
x_42 = x_102;
x_43 = x_103;
x_44 = x_26;
x_45 = x_27;
x_46 = x_28;
goto block_50;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_29);
x_104 = lean_ctor_get(x_33, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_33, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_33, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_33, 3);
lean_inc(x_107);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 lean_ctor_release(x_33, 3);
 x_108 = x_33;
} else {
 lean_dec_ref(x_33);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 4, 1);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_106);
lean_ctor_set(x_109, 3, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_99);
x_110 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_34);
lean_ctor_set(x_110, 2, x_35);
lean_ctor_set(x_110, 3, x_36);
lean_ctor_set_uint8(x_110, sizeof(void*)*4, x_32);
x_111 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_26);
lean_ctor_set(x_111, 2, x_27);
lean_ctor_set(x_111, 3, x_28);
lean_ctor_set_uint8(x_111, sizeof(void*)*4, x_6);
return x_111;
}
}
}
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
x_112 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_112, 0, x_31);
lean_ctor_set(x_112, 1, x_26);
lean_ctor_set(x_112, 2, x_27);
lean_ctor_set(x_112, 3, x_28);
lean_ctor_set_uint8(x_112, sizeof(void*)*4, x_6);
return x_112;
}
block_50:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
if (lean_is_scalar(x_29)) {
 x_47 = lean_alloc_ctor(1, 4, 1);
} else {
 x_47 = x_29;
}
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_38);
lean_ctor_set(x_47, 2, x_39);
lean_ctor_set(x_47, 3, x_40);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_6);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_6);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_42);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_32);
return x_49;
}
}
case 1:
{
lean_object* x_113; 
lean_dec(x_27);
lean_dec(x_26);
if (lean_is_scalar(x_29)) {
 x_113 = lean_alloc_ctor(1, 4, 1);
} else {
 x_113 = x_29;
}
lean_ctor_set(x_113, 0, x_25);
lean_ctor_set(x_113, 1, x_2);
lean_ctor_set(x_113, 2, x_3);
lean_ctor_set(x_113, 3, x_28);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_6);
return x_113;
}
default: 
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_114 = l_Lean_RBNode_ins___at___Lean_RBNode_insert___at___Lean_IR_mkIndexSet_spec__0_spec__0___redArg(x_28, x_2, x_3);
x_115 = lean_ctor_get_uint8(x_114, sizeof(void*)*4);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 3);
lean_inc(x_119);
if (x_115 == 0)
{
if (lean_obj_tag(x_116) == 0)
{
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_134; 
lean_dec(x_29);
x_134 = !lean_is_exclusive(x_114);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_114, 3);
lean_dec(x_135);
x_136 = lean_ctor_get(x_114, 2);
lean_dec(x_136);
x_137 = lean_ctor_get(x_114, 1);
lean_dec(x_137);
x_138 = lean_ctor_get(x_114, 0);
lean_dec(x_138);
lean_ctor_set(x_114, 0, x_119);
x_139 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_139, 0, x_25);
lean_ctor_set(x_139, 1, x_26);
lean_ctor_set(x_139, 2, x_27);
lean_ctor_set(x_139, 3, x_114);
lean_ctor_set_uint8(x_139, sizeof(void*)*4, x_6);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_114);
x_140 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_140, 0, x_119);
lean_ctor_set(x_140, 1, x_117);
lean_ctor_set(x_140, 2, x_118);
lean_ctor_set(x_140, 3, x_119);
lean_ctor_set_uint8(x_140, sizeof(void*)*4, x_115);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_25);
lean_ctor_set(x_141, 1, x_26);
lean_ctor_set(x_141, 2, x_27);
lean_ctor_set(x_141, 3, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_6);
return x_141;
}
}
else
{
uint8_t x_142; 
x_142 = lean_ctor_get_uint8(x_119, sizeof(void*)*4);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_114);
x_143 = lean_ctor_get(x_119, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_119, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_119, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_119, 3);
lean_inc(x_146);
lean_dec(x_119);
x_120 = x_25;
x_121 = x_26;
x_122 = x_27;
x_123 = x_116;
x_124 = x_117;
x_125 = x_118;
x_126 = x_143;
x_127 = x_144;
x_128 = x_145;
x_129 = x_146;
goto block_133;
}
else
{
uint8_t x_147; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_29);
x_147 = !lean_is_exclusive(x_119);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_119, 3);
lean_dec(x_148);
x_149 = lean_ctor_get(x_119, 2);
lean_dec(x_149);
x_150 = lean_ctor_get(x_119, 1);
lean_dec(x_150);
x_151 = lean_ctor_get(x_119, 0);
lean_dec(x_151);
lean_ctor_set(x_119, 3, x_114);
lean_ctor_set(x_119, 2, x_27);
lean_ctor_set(x_119, 1, x_26);
lean_ctor_set(x_119, 0, x_25);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_6);
return x_119;
}
else
{
lean_object* x_152; 
lean_dec(x_119);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_25);
lean_ctor_set(x_152, 1, x_26);
lean_ctor_set(x_152, 2, x_27);
lean_ctor_set(x_152, 3, x_114);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_6);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
x_153 = lean_ctor_get_uint8(x_116, sizeof(void*)*4);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_114);
x_154 = lean_ctor_get(x_116, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_116, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_116, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_116, 3);
lean_inc(x_157);
lean_dec(x_116);
x_120 = x_25;
x_121 = x_26;
x_122 = x_27;
x_123 = x_154;
x_124 = x_155;
x_125 = x_156;
x_126 = x_157;
x_127 = x_117;
x_128 = x_118;
x_129 = x_119;
goto block_133;
}
else
{
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_158; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_29);
x_158 = !lean_is_exclusive(x_116);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_116, 3);
lean_dec(x_159);
x_160 = lean_ctor_get(x_116, 2);
lean_dec(x_160);
x_161 = lean_ctor_get(x_116, 1);
lean_dec(x_161);
x_162 = lean_ctor_get(x_116, 0);
lean_dec(x_162);
lean_ctor_set(x_116, 3, x_114);
lean_ctor_set(x_116, 2, x_27);
lean_ctor_set(x_116, 1, x_26);
lean_ctor_set(x_116, 0, x_25);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_6);
return x_116;
}
else
{
lean_object* x_163; 
lean_dec(x_116);
x_163 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_163, 0, x_25);
lean_ctor_set(x_163, 1, x_26);
lean_ctor_set(x_163, 2, x_27);
lean_ctor_set(x_163, 3, x_114);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_6);
return x_163;
}
}
else
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_114);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_165 = lean_ctor_get(x_114, 3);
lean_dec(x_165);
x_166 = lean_ctor_get(x_114, 2);
lean_dec(x_166);
x_167 = lean_ctor_get(x_114, 1);
lean_dec(x_167);
x_168 = lean_ctor_get(x_114, 0);
lean_dec(x_168);
x_169 = lean_ctor_get_uint8(x_119, sizeof(void*)*4);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_free_object(x_114);
x_170 = lean_ctor_get(x_119, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_119, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_119, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_119, 3);
lean_inc(x_173);
lean_dec(x_119);
x_120 = x_25;
x_121 = x_26;
x_122 = x_27;
x_123 = x_116;
x_124 = x_117;
x_125 = x_118;
x_126 = x_170;
x_127 = x_171;
x_128 = x_172;
x_129 = x_173;
goto block_133;
}
else
{
uint8_t x_174; 
lean_dec(x_29);
x_174 = !lean_is_exclusive(x_116);
if (x_174 == 0)
{
lean_object* x_175; 
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_169);
x_175 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_175, 0, x_25);
lean_ctor_set(x_175, 1, x_26);
lean_ctor_set(x_175, 2, x_27);
lean_ctor_set(x_175, 3, x_114);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_6);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_116, 0);
x_177 = lean_ctor_get(x_116, 1);
x_178 = lean_ctor_get(x_116, 2);
x_179 = lean_ctor_get(x_116, 3);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_116);
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_177);
lean_ctor_set(x_180, 2, x_178);
lean_ctor_set(x_180, 3, x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_169);
lean_ctor_set(x_114, 0, x_180);
x_181 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_181, 0, x_25);
lean_ctor_set(x_181, 1, x_26);
lean_ctor_set(x_181, 2, x_27);
lean_ctor_set(x_181, 3, x_114);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_6);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_114);
x_182 = lean_ctor_get_uint8(x_119, sizeof(void*)*4);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_119, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_119, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_119, 2);
lean_inc(x_185);
x_186 = lean_ctor_get(x_119, 3);
lean_inc(x_186);
lean_dec(x_119);
x_120 = x_25;
x_121 = x_26;
x_122 = x_27;
x_123 = x_116;
x_124 = x_117;
x_125 = x_118;
x_126 = x_183;
x_127 = x_184;
x_128 = x_185;
x_129 = x_186;
goto block_133;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_29);
x_187 = lean_ctor_get(x_116, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_116, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_116, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_116, 3);
lean_inc(x_190);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 x_191 = x_116;
} else {
 lean_dec_ref(x_116);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 4, 1);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_187);
lean_ctor_set(x_192, 1, x_188);
lean_ctor_set(x_192, 2, x_189);
lean_ctor_set(x_192, 3, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_182);
x_193 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_117);
lean_ctor_set(x_193, 2, x_118);
lean_ctor_set(x_193, 3, x_119);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_115);
x_194 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_194, 0, x_25);
lean_ctor_set(x_194, 1, x_26);
lean_ctor_set(x_194, 2, x_27);
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_6);
return x_194;
}
}
}
}
}
}
else
{
lean_object* x_195; 
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_29);
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_25);
lean_ctor_set(x_195, 1, x_26);
lean_ctor_set(x_195, 2, x_27);
lean_ctor_set(x_195, 3, x_114);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_6);
return x_195;
}
block_133:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
if (lean_is_scalar(x_29)) {
 x_130 = lean_alloc_ctor(1, 4, 1);
} else {
 x_130 = x_29;
}
lean_ctor_set(x_130, 0, x_120);
lean_ctor_set(x_130, 1, x_121);
lean_ctor_set(x_130, 2, x_122);
lean_ctor_set(x_130, 3, x_123);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_6);
x_131 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_128);
lean_ctor_set(x_131, 3, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*4, x_6);
x_132 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_124);
lean_ctor_set(x_132, 2, x_125);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*4, x_115);
return x_132;
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
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
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
x_3 = l_Lean_RBNode_find___at___Lean_IR_LocalContext_isJP_spec__0___redArg(x_1, x_2);
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
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
x_12 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_7);
lean_ctor_set(x_2, 3, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_11);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_2);
x_13 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_7);
x_14 = l_Lean_RBNode_balRight___redArg(x_4, x_5, x_6, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_15 = l_Lean_RBNode_appendTrees___redArg(x_4, x_7);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = l_Lean_RBNode_isBlack___redArg(x_4);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
x_18 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_4);
lean_ctor_set(x_2, 0, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_17);
return x_2;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_2);
x_19 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_4);
x_20 = l_Lean_RBNode_balLeft___redArg(x_19, x_5, x_6, x_7);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_25 = lean_nat_dec_lt(x_1, x_22);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_1, x_22);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_RBNode_isBlack___redArg(x_24);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 0;
x_29 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_24);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_23);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_24);
x_32 = l_Lean_RBNode_balRight___redArg(x_21, x_22, x_23, x_31);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_22);
x_33 = l_Lean_RBNode_appendTrees___redArg(x_21, x_24);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = l_Lean_RBNode_isBlack___redArg(x_21);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 0;
x_36 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_21);
x_37 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_37, 2, x_23);
lean_ctor_set(x_37, 3, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_RBNode_del___at___Lean_RBNode_erase___at___Lean_IR_LocalContext_eraseJoinPointDecl_spec__0_spec__0___redArg(x_1, x_21);
x_39 = l_Lean_RBNode_balLeft___redArg(x_38, x_22, x_23, x_24);
return x_39;
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
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
x_4 = x_25;
x_5 = x_26;
x_6 = x_27;
x_7 = x_28;
goto block_10;
}
else
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; uint8_t x_42; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get(x_3, 1);
x_36 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_37 = lean_ctor_get(x_3, 2);
x_42 = l_Lean_IR_VarId_alphaEqv(x_1, x_30, x_34);
if (x_42 == 0)
{
x_38 = x_42;
goto block_41;
}
else
{
uint8_t x_43; 
x_43 = l_Lean_IR_CtorInfo_beq(x_31, x_35);
x_38 = x_43;
goto block_41;
}
block_41:
{
if (x_38 == 0)
{
return x_38;
}
else
{
if (x_32 == 0)
{
if (x_36 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_IR_args_alphaEqv(x_1, x_33, x_37);
return x_39;
}
else
{
return x_32;
}
}
else
{
if (x_36 == 0)
{
return x_36;
}
else
{
uint8_t x_40; 
x_40 = l_Lean_IR_args_alphaEqv(x_1, x_33, x_37);
return x_40;
}
}
}
}
}
else
{
uint8_t x_44; 
x_44 = 0;
return x_44;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_4 = x_45;
x_5 = x_46;
x_6 = x_47;
x_7 = x_48;
goto block_10;
}
else
{
uint8_t x_49; 
x_49 = 0;
return x_49;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_2, 0);
x_51 = lean_ctor_get(x_2, 1);
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
x_4 = x_50;
x_5 = x_51;
x_6 = x_52;
x_7 = x_53;
goto block_10;
}
else
{
uint8_t x_54; 
x_54 = 0;
return x_54;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_64; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_2, 2);
x_58 = lean_ctor_get(x_3, 0);
x_59 = lean_ctor_get(x_3, 1);
x_60 = lean_ctor_get(x_3, 2);
x_64 = lean_nat_dec_eq(x_55, x_58);
if (x_64 == 0)
{
x_61 = x_64;
goto block_63;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_eq(x_56, x_59);
x_61 = x_65;
goto block_63;
}
block_63:
{
if (x_61 == 0)
{
return x_61;
}
else
{
uint8_t x_62; 
x_62 = l_Lean_IR_VarId_alphaEqv(x_1, x_57, x_60);
return x_62;
}
}
}
else
{
uint8_t x_66; 
x_66 = 0;
return x_66;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_2, 0);
x_68 = lean_ctor_get(x_2, 1);
x_69 = lean_ctor_get(x_3, 0);
x_70 = lean_ctor_get(x_3, 1);
x_11 = x_67;
x_12 = x_68;
x_13 = x_69;
x_14 = x_70;
goto block_17;
}
else
{
uint8_t x_71; 
x_71 = 0;
return x_71;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_2, 0);
x_73 = lean_ctor_get(x_2, 1);
x_74 = lean_ctor_get(x_3, 0);
x_75 = lean_ctor_get(x_3, 1);
x_11 = x_72;
x_12 = x_73;
x_13 = x_74;
x_14 = x_75;
goto block_17;
}
else
{
uint8_t x_76; 
x_76 = 0;
return x_76;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_2, 0);
x_78 = lean_ctor_get(x_2, 1);
x_79 = lean_ctor_get(x_3, 0);
x_80 = lean_ctor_get(x_3, 1);
x_81 = l_Lean_IR_VarId_alphaEqv(x_1, x_77, x_79);
if (x_81 == 0)
{
return x_81;
}
else
{
uint8_t x_82; 
x_82 = l_Lean_IR_args_alphaEqv(x_1, x_78, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = 0;
return x_83;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_2, 0);
x_85 = lean_ctor_get(x_2, 1);
x_86 = lean_ctor_get(x_3, 0);
x_87 = lean_ctor_get(x_3, 1);
x_88 = l_Lean_IR_IRType_beq(x_84, x_86);
if (x_88 == 0)
{
return x_88;
}
else
{
uint8_t x_89; 
x_89 = l_Lean_IR_VarId_alphaEqv(x_1, x_85, x_87);
return x_89;
}
}
else
{
uint8_t x_90; 
x_90 = 0;
return x_90;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_ctor_get(x_2, 0);
x_92 = lean_ctor_get(x_3, 0);
x_93 = l_Lean_IR_VarId_alphaEqv(x_1, x_91, x_92);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = 0;
return x_94;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_3, 0);
x_97 = l_Lean_IR_LitVal_beq(x_95, x_96);
return x_97;
}
else
{
uint8_t x_98; 
x_98 = 0;
return x_98;
}
}
default: 
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_2, 0);
x_100 = lean_ctor_get(x_3, 0);
x_101 = l_Lean_IR_VarId_alphaEqv(x_1, x_99, x_100);
return x_101;
}
else
{
uint8_t x_102; 
x_102 = 0;
return x_102;
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
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
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
uint8_t x_49; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = 0;
return x_49;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 3);
lean_inc(x_53);
lean_dec(x_2);
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 3);
lean_inc(x_57);
lean_dec(x_3);
lean_inc(x_1);
x_58 = l_Lean_IR_addParamsRename(x_1, x_51, x_55);
lean_dec(x_55);
lean_dec(x_51);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_1);
x_59 = 0;
return x_59;
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_IR_FnBody_alphaEqv(x_60, x_52, x_56);
if (x_61 == 0)
{
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_1);
return x_61;
}
else
{
lean_object* x_62; 
x_62 = l_Lean_IR_addVarRename(x_1, x_50, x_54);
x_1 = x_62;
x_2 = x_53;
x_3 = x_57;
goto _start;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = 0;
return x_64;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_77; 
x_65 = lean_ctor_get(x_2, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 3);
lean_inc(x_68);
lean_dec(x_2);
x_69 = lean_ctor_get(x_3, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_3, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_3, 3);
lean_inc(x_72);
lean_dec(x_3);
x_77 = l_Lean_IR_VarId_alphaEqv(x_1, x_65, x_69);
lean_dec(x_69);
lean_dec(x_65);
if (x_77 == 0)
{
lean_dec(x_70);
lean_dec(x_66);
x_73 = x_77;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_eq(x_66, x_70);
lean_dec(x_70);
lean_dec(x_66);
x_73 = x_78;
goto block_76;
}
block_76:
{
if (x_73 == 0)
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_1);
return x_73;
}
else
{
uint8_t x_74; 
x_74 = l_Lean_IR_Arg_alphaEqv(x_1, x_67, x_71);
lean_dec(x_71);
lean_dec(x_67);
if (x_74 == 0)
{
lean_dec(x_72);
lean_dec(x_68);
lean_dec(x_1);
return x_74;
}
else
{
x_2 = x_68;
x_3 = x_72;
goto _start;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = 0;
return x_79;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_89; 
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 2);
lean_inc(x_82);
lean_dec(x_2);
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 2);
lean_inc(x_85);
lean_dec(x_3);
x_89 = l_Lean_IR_VarId_alphaEqv(x_1, x_80, x_83);
lean_dec(x_83);
lean_dec(x_80);
if (x_89 == 0)
{
lean_dec(x_84);
lean_dec(x_81);
x_86 = x_89;
goto block_88;
}
else
{
uint8_t x_90; 
x_90 = lean_nat_dec_eq(x_81, x_84);
lean_dec(x_84);
lean_dec(x_81);
x_86 = x_90;
goto block_88;
}
block_88:
{
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_1);
return x_86;
}
else
{
x_2 = x_82;
x_3 = x_85;
goto _start;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = 0;
return x_91;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_104; 
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_2, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_2, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_2, 3);
lean_inc(x_95);
lean_dec(x_2);
x_96 = lean_ctor_get(x_3, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_3, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_3, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_3, 3);
lean_inc(x_99);
lean_dec(x_3);
x_104 = l_Lean_IR_VarId_alphaEqv(x_1, x_92, x_96);
lean_dec(x_96);
lean_dec(x_92);
if (x_104 == 0)
{
lean_dec(x_97);
lean_dec(x_93);
x_100 = x_104;
goto block_103;
}
else
{
uint8_t x_105; 
x_105 = lean_nat_dec_eq(x_93, x_97);
lean_dec(x_97);
lean_dec(x_93);
x_100 = x_105;
goto block_103;
}
block_103:
{
if (x_100 == 0)
{
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_1);
return x_100;
}
else
{
uint8_t x_101; 
x_101 = l_Lean_IR_VarId_alphaEqv(x_1, x_94, x_98);
lean_dec(x_98);
lean_dec(x_94);
if (x_101 == 0)
{
lean_dec(x_99);
lean_dec(x_95);
lean_dec(x_1);
return x_101;
}
else
{
x_2 = x_95;
x_3 = x_99;
goto _start;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = 0;
return x_106;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_125; 
x_107 = lean_ctor_get(x_2, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_2, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_2, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_2, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_2, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_2, 5);
lean_inc(x_112);
lean_dec(x_2);
x_113 = lean_ctor_get(x_3, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_3, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_3, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_3, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_3, 4);
lean_inc(x_117);
x_118 = lean_ctor_get(x_3, 5);
lean_inc(x_118);
lean_dec(x_3);
x_119 = lean_nat_dec_eq(x_109, x_115);
lean_dec(x_115);
lean_dec(x_109);
x_125 = l_Lean_IR_VarId_alphaEqv(x_1, x_107, x_113);
lean_dec(x_113);
lean_dec(x_107);
if (x_125 == 0)
{
lean_dec(x_114);
lean_dec(x_108);
x_120 = x_125;
goto block_124;
}
else
{
uint8_t x_126; 
x_126 = lean_nat_dec_eq(x_108, x_114);
lean_dec(x_114);
lean_dec(x_108);
x_120 = x_126;
goto block_124;
}
block_124:
{
if (x_120 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_1);
return x_120;
}
else
{
if (x_119 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_1);
return x_119;
}
else
{
uint8_t x_121; 
x_121 = l_Lean_IR_VarId_alphaEqv(x_1, x_110, x_116);
lean_dec(x_116);
lean_dec(x_110);
if (x_121 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_1);
return x_121;
}
else
{
uint8_t x_122; 
x_122 = l_Lean_IR_IRType_beq(x_111, x_117);
lean_dec(x_117);
lean_dec(x_111);
if (x_122 == 0)
{
lean_dec(x_118);
lean_dec(x_112);
lean_dec(x_1);
return x_122;
}
else
{
x_2 = x_112;
x_3 = x_118;
goto _start;
}
}
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
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; lean_object* x_137; 
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
x_21 = x_1;
x_22 = x_128;
x_23 = x_129;
x_24 = x_130;
x_25 = x_131;
x_26 = x_132;
x_27 = x_133;
x_28 = x_134;
x_29 = x_135;
x_30 = x_136;
x_31 = x_137;
goto block_34;
}
else
{
uint8_t x_138; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = 0;
return x_138;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; 
x_139 = lean_ctor_get(x_2, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_2, 1);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_142 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_143 = lean_ctor_get(x_2, 2);
lean_inc(x_143);
lean_dec(x_2);
x_144 = lean_ctor_get(x_3, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_3, 1);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_147 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_148 = lean_ctor_get(x_3, 2);
lean_inc(x_148);
lean_dec(x_3);
x_21 = x_1;
x_22 = x_139;
x_23 = x_140;
x_24 = x_141;
x_25 = x_142;
x_26 = x_143;
x_27 = x_144;
x_28 = x_145;
x_29 = x_146;
x_30 = x_147;
x_31 = x_148;
goto block_34;
}
else
{
uint8_t x_149; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = 0;
return x_149;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_150 = lean_ctor_get(x_2, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_2, 1);
lean_inc(x_151);
lean_dec(x_2);
x_152 = lean_ctor_get(x_3, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_3, 1);
lean_inc(x_153);
lean_dec(x_3);
x_154 = l_Lean_IR_VarId_alphaEqv(x_1, x_150, x_152);
lean_dec(x_152);
lean_dec(x_150);
if (x_154 == 0)
{
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_1);
return x_154;
}
else
{
x_2 = x_151;
x_3 = x_153;
goto _start;
}
}
else
{
uint8_t x_156; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = 0;
return x_156;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_2, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_2, 1);
lean_inc(x_158);
lean_dec(x_2);
x_159 = lean_ctor_get(x_3, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_3, 1);
lean_inc(x_160);
lean_dec(x_3);
x_161 = l_Lean_KVMap_eqv(x_157, x_159);
if (x_161 == 0)
{
lean_dec(x_160);
lean_dec(x_158);
lean_dec(x_1);
return x_161;
}
else
{
x_2 = x_158;
x_3 = x_160;
goto _start;
}
}
else
{
uint8_t x_163; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = 0;
return x_163;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_176; 
x_164 = lean_ctor_get(x_2, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_2, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_2, 3);
lean_inc(x_166);
lean_dec(x_2);
x_167 = lean_ctor_get(x_3, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_3, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_3, 3);
lean_inc(x_169);
lean_dec(x_3);
x_176 = lean_name_eq(x_164, x_167);
lean_dec(x_167);
lean_dec(x_164);
if (x_176 == 0)
{
lean_dec(x_168);
lean_dec(x_165);
x_170 = x_176;
goto block_175;
}
else
{
uint8_t x_177; 
x_177 = l_Lean_IR_VarId_alphaEqv(x_1, x_165, x_168);
lean_dec(x_168);
lean_dec(x_165);
x_170 = x_177;
goto block_175;
}
block_175:
{
if (x_170 == 0)
{
lean_dec(x_169);
lean_dec(x_166);
lean_dec(x_1);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_array_get_size(x_166);
x_172 = lean_array_get_size(x_169);
x_173 = lean_nat_dec_eq(x_171, x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_166);
lean_dec(x_1);
return x_173;
}
else
{
uint8_t x_174; 
x_174 = l_Array_isEqvAux___at___Lean_IR_FnBody_alphaEqv_spec__0___redArg(x_1, x_166, x_169, x_171);
lean_dec(x_169);
lean_dec(x_166);
return x_174;
}
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = 0;
return x_178;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_2, 0);
lean_inc(x_179);
lean_dec(x_2);
x_180 = lean_ctor_get(x_3, 0);
lean_inc(x_180);
lean_dec(x_3);
x_181 = l_Lean_IR_Arg_alphaEqv(x_1, x_179, x_180);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_1);
return x_181;
}
else
{
uint8_t x_182; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = 0;
return x_182;
}
}
case 12:
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_2, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 1);
lean_inc(x_184);
lean_dec(x_2);
x_185 = lean_ctor_get(x_3, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_3, 1);
lean_inc(x_186);
lean_dec(x_3);
x_187 = lean_nat_dec_eq(x_183, x_185);
lean_dec(x_185);
lean_dec(x_183);
if (x_187 == 0)
{
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_1);
return x_187;
}
else
{
uint8_t x_188; 
x_188 = l_Lean_IR_args_alphaEqv(x_1, x_184, x_186);
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_1);
return x_188;
}
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
default: 
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 13)
{
uint8_t x_190; 
x_190 = 1;
return x_190;
}
else
{
uint8_t x_191; 
lean_dec(x_3);
x_191 = 0;
return x_191;
}
}
}
block_11:
{
if (x_4 == 0)
{
if (x_7 == 0)
{
x_1 = x_6;
x_2 = x_8;
x_3 = x_5;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_4;
}
}
else
{
if (x_7 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_7;
}
else
{
x_1 = x_6;
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
block_20:
{
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
return x_19;
}
else
{
if (x_18 == 0)
{
if (x_16 == 0)
{
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_15;
x_8 = x_17;
goto block_11;
}
else
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
return x_18;
}
}
else
{
if (x_16 == 0)
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
return x_16;
}
else
{
x_4 = x_12;
x_5 = x_13;
x_6 = x_14;
x_7 = x_15;
x_8 = x_17;
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
x_12 = x_25;
x_13 = x_31;
x_14 = x_21;
x_15 = x_30;
x_16 = x_29;
x_17 = x_26;
x_18 = x_24;
x_19 = x_32;
goto block_20;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_eq(x_23, x_28);
lean_dec(x_28);
lean_dec(x_23);
x_12 = x_25;
x_13 = x_31;
x_14 = x_21;
x_15 = x_30;
x_16 = x_29;
x_17 = x_26;
x_18 = x_24;
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
