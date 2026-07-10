// Lean compiler output
// Module: Lean.Elab.ConfigEval.Instances
// Imports: public import Lean.Elab.ConfigEval.Basic
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
extern lean_object* l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
lean_object* l_Lean_Expr_nat_x3f(lean_object*);
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_TSyntax_getNat(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_int_neg_succ_of_nat(lean_object*);
lean_object* l_Lean_Expr_int_x3f(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_unzip___redArg(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_name_x3f(lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dotIdent"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value),LEAN_SCALAR_PTR_LITERAL(173, 139, 76, 218, 89, 59, 213, 196)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 196, 140, 104, 187, 164, 111)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_ConfigEval_EvalTerm_evalIntStx_spec__0(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term-_"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value),LEAN_SCALAR_PTR_LITERAL(77, 127, 37, 42, 155, 196, 209, 131)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "doubleQuotedName"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "quotedName"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value),LEAN_SCALAR_PTR_LITERAL(217, 120, 158, 75, 195, 162, 2, 130)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(73, 239, 30, 105, 8, 60, 178, 241)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 202, 7, 33, 103, 74, 114, 212)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6;
static const lean_array_object l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term#[_,]"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 119, 178, 128, 145, 112, 206, 247)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5(lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "DataValue"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofBool"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 23, 12, 160, 15, 148, 79, 170)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofName"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value),LEAN_SCALAR_PTR_LITERAL(99, 144, 20, 164, 82, 146, 48, 233)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofString"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value),LEAN_SCALAR_PTR_LITERAL(218, 187, 198, 144, 107, 222, 189, 173)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofInt"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value),LEAN_SCALAR_PTR_LITERAL(213, 162, 111, 148, 162, 163, 105, 18)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value),LEAN_SCALAR_PTR_LITERAL(231, 117, 125, 112, 51, 55, 57, 204)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instBool;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instNat;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instInt;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instString;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instName;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 132, 69, 23, 118, 186, 30, 188)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instDataValue;
static lean_once_cell_t l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nof type `"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0 = (const lean_object*)&l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value),LEAN_SCALAR_PTR_LITERAL(192, 66, 133, 102, 95, 170, 134, 92)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Could not evaluate the expression"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(125, 112, 129, 141, 33, 112, 200, 209)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instBool;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instInt;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instString;
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instName;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instDataValue = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value;
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___boxed(lean_object* v_00_u03b1_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0(v_00_u03b1_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
return v_res_26_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_box(0);
v___x_31_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1));
v___x_32_ = l_Lean_mkConst(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2);
v___x_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_box(0);
v___x_40_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5));
v___x_41_ = l_Lean_mkConst(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8));
v___x_48_ = l_Lean_mkConst(v___x_47_, v___x_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
uint8_t v___y_71_; lean_object* v___y_72_; uint8_t v_a_101_; uint8_t v_a_104_; lean_object* v___y_107_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_id_118_; lean_object* v___x_119_; uint8_t v___y_121_; lean_object* v___y_122_; uint8_t v___y_123_; uint8_t v___y_124_; uint8_t v___y_134_; uint8_t v___x_140_; 
lean_inc(v_a_62_);
v___x_116_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_62_);
v___x_117_ = l_Lean_Syntax_getId(v___x_116_);
v_id_118_ = l_Lean_Name_eraseMacroScopes(v___x_117_);
lean_dec(v___x_117_);
v___x_119_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10));
v___x_140_ = lean_name_eq(v_id_118_, v___x_119_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5));
v___x_142_ = lean_name_eq(v_id_118_, v___x_141_);
v___y_134_ = v___x_142_;
goto v___jp_133_;
}
else
{
v___y_134_ = v___x_140_;
goto v___jp_133_;
}
v___jp_70_:
{
lean_object* v___x_73_; lean_object* v_infoState_74_; uint8_t v_enabled_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = lean_st_ref_get(v_a_68_);
v_infoState_74_ = lean_ctor_get(v___x_73_, 7);
lean_inc_ref(v_infoState_74_);
lean_dec(v___x_73_);
v_enabled_75_ = lean_ctor_get_uint8(v_infoState_74_, sizeof(void*)*3);
lean_dec_ref(v_infoState_74_);
v___x_76_ = lean_box(v___y_71_);
lean_inc_ref(v___y_72_);
v___x_77_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___y_72_);
if (v_enabled_75_ == 0)
{
lean_object* v___x_78_; 
lean_dec(v_a_62_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; 
v___x_79_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3);
v___x_80_ = lean_box(0);
v___x_81_ = lean_box(0);
v___x_82_ = 0;
lean_inc_ref(v___y_72_);
v___x_83_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_62_, v___y_72_, v___x_79_, v___x_80_, v___x_81_, v___x_82_, v___x_82_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_90_; 
v_isSharedCheck_90_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_90_ == 0)
{
lean_object* v_unused_91_; 
v_unused_91_ = lean_ctor_get(v___x_83_, 0);
lean_dec(v_unused_91_);
v___x_85_ = v___x_83_;
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
else
{
lean_dec(v___x_83_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_90_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_77_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_77_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref_known(v___x_77_, 2);
v_a_92_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_83_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_83_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
v___jp_100_:
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6);
v___y_71_ = v_a_101_;
v___y_72_ = v___x_102_;
goto v___jp_70_;
}
v___jp_103_:
{
if (v_a_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9);
v___y_71_ = v_a_104_;
v___y_72_ = v___x_105_;
goto v___jp_70_;
}
else
{
v_a_101_ = v_a_104_;
goto v___jp_100_;
}
}
v___jp_106_:
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___y_107_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___y_107_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___y_107_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___y_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
v___jp_120_:
{
if (v___y_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15));
lean_inc(v___x_116_);
v___x_126_ = l_Lean_Syntax_isOfKind(v___x_116_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec(v___x_116_);
lean_dec(v_a_62_);
v___x_127_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_107_ = v___x_127_;
goto v___jp_106_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = l_Lean_Syntax_getArg(v___x_116_, v___x_128_);
lean_dec(v___x_116_);
v___x_130_ = l_Lean_Syntax_matchesIdent(v___x_129_, v___x_119_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = l_Lean_Syntax_matchesIdent(v___x_129_, v___y_122_);
lean_dec(v___x_129_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
lean_dec(v_a_62_);
v___x_132_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_107_ = v___x_132_;
goto v___jp_106_;
}
else
{
v_a_104_ = v___x_130_;
goto v___jp_103_;
}
}
else
{
lean_dec(v___x_129_);
v_a_104_ = v___y_123_;
goto v___jp_103_;
}
}
}
else
{
lean_dec(v___x_116_);
v_a_104_ = v___y_121_;
goto v___jp_103_;
}
}
v___jp_133_:
{
uint8_t v___x_135_; 
v___x_135_ = 1;
if (v___y_134_ == 0)
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16));
v___x_137_ = lean_name_eq(v_id_118_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8));
v___x_139_ = lean_name_eq(v_id_118_, v___x_138_);
lean_dec(v_id_118_);
v___y_121_ = v___y_134_;
v___y_122_ = v___x_136_;
v___y_123_ = v___x_135_;
v___y_124_ = v___x_139_;
goto v___jp_120_;
}
else
{
lean_dec(v_id_118_);
v___y_121_ = v___y_134_;
v___y_122_ = v___x_136_;
v___y_123_ = v___x_135_;
v___y_124_ = v___x_137_;
goto v___jp_120_;
}
}
else
{
lean_dec(v_id_118_);
lean_dec(v___x_116_);
v_a_101_ = v___x_135_;
goto v___jp_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___boxed(lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
return v_res_151_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_box(0);
v___x_156_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1));
v___x_157_ = l_Lean_mkConst(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2);
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_a_172_; lean_object* v_n_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
lean_inc(v_a_163_);
v_n_200_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_163_);
v___x_201_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5));
lean_inc(v_n_200_);
v___x_202_ = l_Lean_Syntax_isOfKind(v_n_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_n_200_);
lean_dec(v_a_163_);
v___x_203_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
else
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_TSyntax_getNat(v_n_200_);
lean_dec(v_n_200_);
v_a_172_ = v___x_212_;
goto v___jp_171_;
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v_infoState_174_; uint8_t v_enabled_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_173_ = lean_st_ref_get(v_a_169_);
v_infoState_174_ = lean_ctor_get(v___x_173_, 7);
lean_inc_ref(v_infoState_174_);
lean_dec(v___x_173_);
v_enabled_175_ = lean_ctor_get_uint8(v_infoState_174_, sizeof(void*)*3);
lean_dec_ref(v_infoState_174_);
lean_inc(v_a_172_);
v___x_176_ = l_Lean_mkNatLit(v_a_172_);
lean_inc_ref(v___x_176_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_a_172_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
if (v_enabled_175_ == 0)
{
lean_object* v___x_178_; 
lean_dec_ref(v___x_176_);
lean_dec(v_a_163_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; 
v___x_179_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3);
v___x_180_ = lean_box(0);
v___x_181_ = lean_box(0);
v___x_182_ = 0;
v___x_183_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_163_, v___x_176_, v___x_179_, v___x_180_, v___x_181_, v___x_182_, v___x_182_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_190_ == 0)
{
lean_object* v_unused_191_; 
v_unused_191_ = lean_ctor_get(v___x_183_, 0);
lean_dec(v_unused_191_);
v___x_185_ = v___x_183_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_dec(v___x_183_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_177_);
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_177_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref_known(v___x_177_, 2);
v_a_192_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_183_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_183_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed(lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Elab_ConfigEval_EvalTerm_evalIntStx_spec__0(lean_object* v_a_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_nat_to_int(v_a_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_box(0);
v___x_228_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1));
v___x_229_ = l_Lean_Expr_const___override(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2);
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_nat_to_int(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = l_Lean_Level_ofNat(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_box(0);
v___x_242_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8);
v___x_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_245_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7));
v___x_246_ = l_Lean_Expr_const___override(v___x_245_, v___x_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = lean_box(0);
v___x_252_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12));
v___x_253_ = l_Lean_Expr_const___override(v___x_252_, v___x_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_265_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v_a_296_; lean_object* v___y_308_; lean_object* v_n_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_265_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2);
lean_inc(v_a_257_);
v_n_317_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_257_);
v___x_318_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5));
lean_inc(v_n_317_);
v___x_319_ = l_Lean_Syntax_isOfKind(v_n_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15));
lean_inc(v_n_317_);
v___x_321_ = l_Lean_Syntax_isOfKind(v_n_317_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_n_317_);
lean_dec(v_a_257_);
v___x_322_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_308_ = v___x_322_;
goto v___jp_307_;
}
else
{
lean_object* v___x_323_; lean_object* v_n_324_; uint8_t v___x_325_; 
v___x_323_ = lean_unsigned_to_nat(1u);
v_n_324_ = l_Lean_Syntax_getArg(v_n_317_, v___x_323_);
lean_dec(v_n_317_);
lean_inc(v_n_324_);
v___x_325_ = l_Lean_Syntax_isOfKind(v_n_324_, v___x_318_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
lean_dec(v_n_324_);
lean_dec(v_a_257_);
v___x_326_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_308_ = v___x_326_;
goto v___jp_307_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = l_Lean_TSyntax_getNat(v_n_324_);
lean_dec(v_n_324_);
v___x_328_ = lean_nat_to_int(v___x_327_);
v___x_329_ = lean_int_neg(v___x_328_);
lean_dec(v___x_328_);
v_a_296_ = v___x_329_;
goto v___jp_295_;
}
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = l_Lean_TSyntax_getNat(v_n_317_);
lean_dec(v_n_317_);
v___x_331_ = lean_nat_to_int(v___x_330_);
v_a_296_ = v___x_331_;
goto v___jp_295_;
}
v___jp_266_:
{
lean_object* v___x_269_; lean_object* v_infoState_270_; uint8_t v_enabled_271_; lean_object* v___x_272_; 
v___x_269_ = lean_st_ref_get(v_a_263_);
v_infoState_270_ = lean_ctor_get(v___x_269_, 7);
lean_inc_ref(v_infoState_270_);
lean_dec(v___x_269_);
v_enabled_271_ = lean_ctor_get_uint8(v_infoState_270_, sizeof(void*)*3);
lean_dec_ref(v_infoState_270_);
lean_inc_ref(v___y_268_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___y_267_);
lean_ctor_set(v___x_272_, 1, v___y_268_);
if (v_enabled_271_ == 0)
{
lean_object* v___x_273_; 
lean_dec_ref(v___y_268_);
lean_dec(v_a_257_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; 
v___x_274_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3);
v___x_275_ = lean_box(0);
v___x_276_ = lean_box(0);
v___x_277_ = 0;
v___x_278_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_257_, v___y_268_, v___x_274_, v___x_275_, v___x_276_, v___x_277_, v___x_277_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; 
v_unused_286_ = lean_ctor_get(v___x_278_, 0);
lean_dec(v_unused_286_);
v___x_280_ = v___x_278_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_dec(v___x_278_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_272_);
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_272_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref_known(v___x_272_, 2);
v_a_287_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_278_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_278_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
v___jp_295_:
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4);
v___x_298_ = lean_int_dec_le(v___x_297_, v_a_296_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10);
v___x_300_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13);
v___x_301_ = lean_int_neg(v_a_296_);
v___x_302_ = l_Int_toNat(v___x_301_);
lean_dec(v___x_301_);
v___x_303_ = l_Lean_instToExprInt_mkNat(v___x_302_);
v___x_304_ = l_Lean_mkApp3(v___x_299_, v___x_265_, v___x_300_, v___x_303_);
v___y_267_ = v_a_296_;
v___y_268_ = v___x_304_;
goto v___jp_266_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = l_Int_toNat(v_a_296_);
v___x_306_ = l_Lean_instToExprInt_mkNat(v___x_305_);
v___y_267_ = v_a_296_;
v___y_268_ = v___x_306_;
goto v___jp_266_;
}
}
v___jp_307_:
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___y_308_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___y_308_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___y_308_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___y_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___boxed(lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = lean_box(0);
v___x_345_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1));
v___x_346_ = l_Lean_mkConst(v___x_345_, v___x_344_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_a_361_; lean_object* v_s_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
lean_inc(v_a_352_);
v_s_389_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_352_);
v___x_390_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5));
lean_inc(v_s_389_);
v___x_391_ = l_Lean_Syntax_isOfKind(v_s_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v_s_389_);
lean_dec(v_a_352_);
v___x_392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_TSyntax_getString(v_s_389_);
lean_dec(v_s_389_);
v_a_361_ = v___x_401_;
goto v___jp_360_;
}
v___jp_360_:
{
lean_object* v___x_362_; lean_object* v_infoState_363_; uint8_t v_enabled_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_362_ = lean_st_ref_get(v_a_358_);
v_infoState_363_ = lean_ctor_get(v___x_362_, 7);
lean_inc_ref(v_infoState_363_);
lean_dec(v___x_362_);
v_enabled_364_ = lean_ctor_get_uint8(v_infoState_363_, sizeof(void*)*3);
lean_dec_ref(v_infoState_363_);
lean_inc_ref(v_a_361_);
v___x_365_ = l_Lean_mkStrLit(v_a_361_);
lean_inc_ref(v___x_365_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_a_361_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
if (v_enabled_364_ == 0)
{
lean_object* v___x_367_; 
lean_dec_ref(v___x_365_);
lean_dec(v_a_352_);
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; 
v___x_368_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3);
v___x_369_ = lean_box(0);
v___x_370_ = lean_box(0);
v___x_371_ = 0;
v___x_372_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_352_, v___x_365_, v___x_368_, v___x_369_, v___x_370_, v___x_371_, v___x_371_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_379_; 
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_379_ == 0)
{
lean_object* v_unused_380_; 
v_unused_380_ = lean_ctor_get(v___x_372_, 0);
lean_dec(v_unused_380_);
v___x_374_ = v___x_372_;
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
else
{
lean_dec(v___x_372_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_379_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_377_; 
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_366_);
v___x_377_ = v___x_374_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_366_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec_ref_known(v___x_366_, 2);
v_a_381_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_372_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_372_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___boxed(lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(lean_object* v_keys_411_, lean_object* v_i_412_, lean_object* v_k_413_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_array_get_size(v_keys_411_);
v___x_415_ = lean_nat_dec_lt(v_i_412_, v___x_414_);
if (v___x_415_ == 0)
{
lean_dec(v_i_412_);
return v___x_415_;
}
else
{
lean_object* v_k_x27_416_; uint8_t v___x_417_; 
v_k_x27_416_ = lean_array_fget_borrowed(v_keys_411_, v_i_412_);
v___x_417_ = l_Lean_instBEqExtraModUse_beq(v_k_413_, v_k_x27_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(1u);
v___x_419_ = lean_nat_add(v_i_412_, v___x_418_);
lean_dec(v_i_412_);
v_i_412_ = v___x_419_;
goto _start;
}
else
{
lean_dec(v_i_412_);
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_keys_421_, lean_object* v_i_422_, lean_object* v_k_423_){
_start:
{
uint8_t v_res_424_; lean_object* v_r_425_; 
v_res_424_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_keys_421_, v_i_422_, v_k_423_);
lean_dec_ref(v_k_423_);
lean_dec_ref(v_keys_421_);
v_r_425_ = lean_box(v_res_424_);
return v_r_425_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_426_, size_t v_x_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v_es_429_; lean_object* v___x_430_; size_t v___x_431_; size_t v___x_432_; lean_object* v_j_433_; lean_object* v___x_434_; 
v_es_429_ = lean_ctor_get(v_x_426_, 0);
v___x_430_ = lean_box(2);
v___x_431_ = ((size_t)31ULL);
v___x_432_ = lean_usize_land(v_x_427_, v___x_431_);
v_j_433_ = lean_usize_to_nat(v___x_432_);
v___x_434_ = lean_array_get_borrowed(v___x_430_, v_es_429_, v_j_433_);
lean_dec(v_j_433_);
switch(lean_obj_tag(v___x_434_))
{
case 0:
{
lean_object* v_key_435_; uint8_t v___x_436_; 
v_key_435_ = lean_ctor_get(v___x_434_, 0);
v___x_436_ = l_Lean_instBEqExtraModUse_beq(v_x_428_, v_key_435_);
return v___x_436_;
}
case 1:
{
lean_object* v_node_437_; size_t v___x_438_; size_t v___x_439_; 
v_node_437_ = lean_ctor_get(v___x_434_, 0);
v___x_438_ = ((size_t)5ULL);
v___x_439_ = lean_usize_shift_right(v_x_427_, v___x_438_);
v_x_426_ = v_node_437_;
v_x_427_ = v___x_439_;
goto _start;
}
default: 
{
uint8_t v___x_441_; 
v___x_441_ = 0;
return v___x_441_;
}
}
}
else
{
lean_object* v_ks_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_ks_442_ = lean_ctor_get(v_x_426_, 0);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_ks_442_, v___x_443_, v_x_428_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
size_t v_x_10238__boxed_448_; uint8_t v_res_449_; lean_object* v_r_450_; 
v_x_10238__boxed_448_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_res_449_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_445_, v_x_10238__boxed_448_, v_x_447_);
lean_dec_ref(v_x_447_);
lean_dec_ref(v_x_445_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
uint64_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v___x_453_ = l_Lean_instHashableExtraModUse_hash(v_x_452_);
v___x_454_ = lean_uint64_to_usize(v___x_453_);
v___x_455_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_451_, v___x_454_, v_x_452_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
uint8_t v_res_458_; lean_object* v_r_459_; 
v_res_458_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v_x_456_, v_x_457_);
lean_dec_ref(v_x_457_);
lean_dec_ref(v_x_456_);
v_r_459_ = lean_box(v_res_458_);
return v_r_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(lean_object* v_msgData_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; lean_object* v_env_467_; lean_object* v___x_468_; lean_object* v_mctx_469_; lean_object* v_lctx_470_; lean_object* v_options_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_466_ = lean_st_ref_get(v___y_464_);
v_env_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc_ref(v_env_467_);
lean_dec(v___x_466_);
v___x_468_ = lean_st_ref_get(v___y_462_);
v_mctx_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc_ref(v_mctx_469_);
lean_dec(v___x_468_);
v_lctx_470_ = lean_ctor_get(v___y_461_, 2);
v_options_471_ = lean_ctor_get(v___y_463_, 2);
lean_inc_ref(v_options_471_);
lean_inc_ref(v_lctx_470_);
v___x_472_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_472_, 0, v_env_467_);
lean_ctor_set(v___x_472_, 1, v_mctx_469_);
lean_ctor_set(v___x_472_, 2, v_lctx_470_);
lean_ctor_set(v___x_472_, 3, v_options_471_);
v___x_473_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v_msgData_460_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_msgData_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msgData_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_482_; double v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_float_of_nat(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_487_, lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_ref_494_; lean_object* v___x_495_; lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_540_; 
v_ref_494_ = lean_ctor_get(v___y_491_, 5);
v___x_495_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_540_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_540_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_540_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v_traceState_501_; lean_object* v_env_502_; lean_object* v_nextMacroScope_503_; lean_object* v_ngen_504_; lean_object* v_auxDeclNGen_505_; lean_object* v_cache_506_; lean_object* v_messages_507_; lean_object* v_infoState_508_; lean_object* v_snapshotTasks_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_539_; 
v___x_500_ = lean_st_ref_take(v___y_492_);
v_traceState_501_ = lean_ctor_get(v___x_500_, 4);
v_env_502_ = lean_ctor_get(v___x_500_, 0);
v_nextMacroScope_503_ = lean_ctor_get(v___x_500_, 1);
v_ngen_504_ = lean_ctor_get(v___x_500_, 2);
v_auxDeclNGen_505_ = lean_ctor_get(v___x_500_, 3);
v_cache_506_ = lean_ctor_get(v___x_500_, 5);
v_messages_507_ = lean_ctor_get(v___x_500_, 6);
v_infoState_508_ = lean_ctor_get(v___x_500_, 7);
v_snapshotTasks_509_ = lean_ctor_get(v___x_500_, 8);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_539_ == 0)
{
v___x_511_ = v___x_500_;
v_isShared_512_ = v_isSharedCheck_539_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snapshotTasks_509_);
lean_inc(v_infoState_508_);
lean_inc(v_messages_507_);
lean_inc(v_cache_506_);
lean_inc(v_traceState_501_);
lean_inc(v_auxDeclNGen_505_);
lean_inc(v_ngen_504_);
lean_inc(v_nextMacroScope_503_);
lean_inc(v_env_502_);
lean_dec(v___x_500_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_539_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
uint64_t v_tid_513_; lean_object* v_traces_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_538_; 
v_tid_513_ = lean_ctor_get_uint64(v_traceState_501_, sizeof(void*)*1);
v_traces_514_ = lean_ctor_get(v_traceState_501_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_traceState_501_);
if (v_isSharedCheck_538_ == 0)
{
v___x_516_ = v_traceState_501_;
v_isShared_517_ = v_isSharedCheck_538_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_traces_514_);
lean_dec(v_traceState_501_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_538_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; double v___x_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_518_ = lean_box(0);
v___x_519_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_520_ = 0;
v___x_521_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_522_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_522_, 0, v_cls_487_);
lean_ctor_set(v___x_522_, 1, v___x_518_);
lean_ctor_set(v___x_522_, 2, v___x_521_);
lean_ctor_set_float(v___x_522_, sizeof(void*)*3, v___x_519_);
lean_ctor_set_float(v___x_522_, sizeof(void*)*3 + 8, v___x_519_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*3 + 16, v___x_520_);
v___x_523_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_524_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v_a_496_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
lean_inc(v_ref_494_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_ref_494_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Lean_PersistentArray_push___redArg(v_traces_514_, v___x_525_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_526_);
v___x_528_ = v___x_516_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_526_);
lean_ctor_set_uint64(v_reuseFailAlloc_537_, sizeof(void*)*1, v_tid_513_);
v___x_528_ = v_reuseFailAlloc_537_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 4, v___x_528_);
v___x_530_ = v___x_511_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_env_502_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_nextMacroScope_503_);
lean_ctor_set(v_reuseFailAlloc_536_, 2, v_ngen_504_);
lean_ctor_set(v_reuseFailAlloc_536_, 3, v_auxDeclNGen_505_);
lean_ctor_set(v_reuseFailAlloc_536_, 4, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_536_, 5, v_cache_506_);
lean_ctor_set(v_reuseFailAlloc_536_, 6, v_messages_507_);
lean_ctor_set(v_reuseFailAlloc_536_, 7, v_infoState_508_);
lean_ctor_set(v_reuseFailAlloc_536_, 8, v_snapshotTasks_509_);
v___x_530_ = v_reuseFailAlloc_536_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_531_ = lean_st_ref_set(v___y_492_, v___x_530_);
v___x_532_ = lean_box(0);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_532_);
v___x_534_ = v___x_498_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_541_, lean_object* v_msg_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_541_, v_msg_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_548_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1));
v___x_552_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0));
v___x_553_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_552_, v___x_551_);
return v___x_553_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_554_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4);
v___x_560_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
lean_ctor_set(v___x_560_, 2, v___x_559_);
lean_ctor_set(v___x_560_, 3, v___x_559_);
lean_ctor_set(v___x_560_, 4, v___x_559_);
lean_ctor_set(v___x_560_, 5, v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_cls_575_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8));
v___x_576_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15));
v___x_577_ = l_Lean_Name_append(v___x_576_, v_cls_575_);
return v___x_577_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(lean_object* v_mod_588_, uint8_t v_isMeta_589_, lean_object* v_hint_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_env_599_; uint8_t v_isExporting_600_; lean_object* v___x_601_; lean_object* v_env_602_; lean_object* v___x_603_; lean_object* v_entry_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___x_650_; uint8_t v___x_651_; uint8_t v___x_652_; 
v___x_598_ = lean_st_ref_get(v___y_596_);
v_env_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc_ref(v_env_599_);
lean_dec(v___x_598_);
v_isExporting_600_ = lean_ctor_get_uint8(v_env_599_, sizeof(void*)*8);
lean_dec_ref(v_env_599_);
v___x_601_ = lean_st_ref_get(v___y_596_);
v_env_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc_ref(v_env_602_);
lean_dec(v___x_601_);
v___x_603_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2);
lean_inc(v_mod_588_);
v_entry_604_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_604_, 0, v_mod_588_);
lean_ctor_set_uint8(v_entry_604_, sizeof(void*)*1, v_isExporting_600_);
lean_ctor_set_uint8(v_entry_604_, sizeof(void*)*1 + 1, v_isMeta_589_);
v___x_605_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_606_ = lean_box(1);
v___x_607_ = lean_box(0);
v___x_650_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_603_, v___x_605_, v_env_602_, v___x_606_, v___x_607_);
v___x_651_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v___x_650_, v_entry_604_);
lean_dec(v___x_650_);
v___x_652_ = lean_bool_not(v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec_ref_known(v_entry_604_, 1);
lean_dec(v_hint_590_);
lean_dec(v_mod_588_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
else
{
lean_object* v_options_655_; uint8_t v_hasTrace_656_; 
v_options_655_ = lean_ctor_get(v___y_595_, 2);
v_hasTrace_656_ = lean_ctor_get_uint8(v_options_655_, sizeof(void*)*1);
if (v_hasTrace_656_ == 0)
{
lean_dec(v_hint_590_);
lean_dec(v_mod_588_);
v___y_609_ = v___y_594_;
v___y_610_ = v___y_596_;
goto v___jp_608_;
}
else
{
lean_object* v_inheritedTraceOptions_657_; lean_object* v_cls_658_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_inheritedTraceOptions_657_ = lean_ctor_get(v___y_595_, 13);
v_cls_658_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8));
v___x_678_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16);
v___x_679_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_657_, v_options_655_, v___x_678_);
if (v___x_679_ == 0)
{
lean_dec(v_hint_590_);
lean_dec(v_mod_588_);
v___y_609_ = v___y_594_;
v___y_610_ = v___y_596_;
goto v___jp_608_;
}
else
{
lean_object* v___x_680_; lean_object* v___y_682_; 
v___x_680_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18);
if (v_isExporting_600_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23));
v___y_682_ = v___x_689_;
goto v___jp_681_;
}
else
{
lean_object* v___x_690_; 
v___x_690_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24));
v___y_682_ = v___x_690_;
goto v___jp_681_;
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_inc_ref(v___y_682_);
v___x_683_ = l_Lean_stringToMessageData(v___y_682_);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_680_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
if (v_isMeta_589_ == 0)
{
lean_object* v___x_687_; 
v___x_687_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21));
v___y_665_ = v___x_686_;
v___y_666_ = v___x_687_;
goto v___jp_664_;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22));
v___y_665_ = v___x_686_;
v___y_666_ = v___x_688_;
goto v___jp_664_;
}
}
}
v___jp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___y_660_);
lean_ctor_set(v___x_662_, 1, v___y_661_);
v___x_663_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_658_, v___x_662_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec_ref_known(v___x_663_, 1);
v___y_609_ = v___y_594_;
v___y_610_ = v___y_596_;
goto v___jp_608_;
}
else
{
lean_dec_ref_known(v_entry_604_, 1);
return v___x_663_;
}
}
v___jp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
lean_inc_ref(v___y_666_);
v___x_667_ = l_Lean_stringToMessageData(v___y_666_);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___y_665_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10);
v___x_670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = l_Lean_MessageData_ofName(v_mod_588_);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_Name_isAnonymous(v_hint_590_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12);
v___x_675_ = l_Lean_MessageData_ofName(v_hint_590_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___y_660_ = v___x_672_;
v___y_661_ = v___x_676_;
goto v___jp_659_;
}
else
{
lean_object* v___x_677_; 
lean_dec(v_hint_590_);
v___x_677_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13);
v___y_660_ = v___x_672_;
v___y_661_ = v___x_677_;
goto v___jp_659_;
}
}
}
}
v___jp_608_:
{
lean_object* v___x_611_; lean_object* v_toEnvExtension_612_; lean_object* v_env_613_; lean_object* v_nextMacroScope_614_; lean_object* v_ngen_615_; lean_object* v_auxDeclNGen_616_; lean_object* v_traceState_617_; lean_object* v_messages_618_; lean_object* v_infoState_619_; lean_object* v_snapshotTasks_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_648_; 
v___x_611_ = lean_st_ref_take(v___y_610_);
v_toEnvExtension_612_ = lean_ctor_get(v___x_605_, 0);
v_env_613_ = lean_ctor_get(v___x_611_, 0);
v_nextMacroScope_614_ = lean_ctor_get(v___x_611_, 1);
v_ngen_615_ = lean_ctor_get(v___x_611_, 2);
v_auxDeclNGen_616_ = lean_ctor_get(v___x_611_, 3);
v_traceState_617_ = lean_ctor_get(v___x_611_, 4);
v_messages_618_ = lean_ctor_get(v___x_611_, 6);
v_infoState_619_ = lean_ctor_get(v___x_611_, 7);
v_snapshotTasks_620_ = lean_ctor_get(v___x_611_, 8);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v___x_611_, 5);
lean_dec(v_unused_649_);
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_648_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_snapshotTasks_620_);
lean_inc(v_infoState_619_);
lean_inc(v_messages_618_);
lean_inc(v_traceState_617_);
lean_inc(v_auxDeclNGen_616_);
lean_inc(v_ngen_615_);
lean_inc(v_nextMacroScope_614_);
lean_inc(v_env_613_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_648_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_asyncMode_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v_asyncMode_624_ = lean_ctor_get(v_toEnvExtension_612_, 2);
v___x_625_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_605_, v_env_613_, v_entry_604_, v_asyncMode_624_, v___x_607_);
v___x_626_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 5, v___x_626_);
lean_ctor_set(v___x_622_, 0, v___x_625_);
v___x_628_ = v___x_622_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_647_, 1, v_nextMacroScope_614_);
lean_ctor_set(v_reuseFailAlloc_647_, 2, v_ngen_615_);
lean_ctor_set(v_reuseFailAlloc_647_, 3, v_auxDeclNGen_616_);
lean_ctor_set(v_reuseFailAlloc_647_, 4, v_traceState_617_);
lean_ctor_set(v_reuseFailAlloc_647_, 5, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_647_, 6, v_messages_618_);
lean_ctor_set(v_reuseFailAlloc_647_, 7, v_infoState_619_);
lean_ctor_set(v_reuseFailAlloc_647_, 8, v_snapshotTasks_620_);
v___x_628_ = v_reuseFailAlloc_647_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_mctx_631_; lean_object* v_zetaDeltaFVarIds_632_; lean_object* v_postponed_633_; lean_object* v_diag_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v___x_629_ = lean_st_ref_set(v___y_610_, v___x_628_);
v___x_630_ = lean_st_ref_take(v___y_609_);
v_mctx_631_ = lean_ctor_get(v___x_630_, 0);
v_zetaDeltaFVarIds_632_ = lean_ctor_get(v___x_630_, 2);
v_postponed_633_ = lean_ctor_get(v___x_630_, 3);
v_diag_634_ = lean_ctor_get(v___x_630_, 4);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v___x_630_, 1);
lean_dec(v_unused_646_);
v___x_636_ = v___x_630_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_diag_634_);
lean_inc(v_postponed_633_);
lean_inc(v_zetaDeltaFVarIds_632_);
lean_inc(v_mctx_631_);
lean_dec(v___x_630_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6);
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 1, v___x_638_);
v___x_640_ = v___x_636_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_mctx_631_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_zetaDeltaFVarIds_632_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_postponed_633_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v_diag_634_);
v___x_640_ = v_reuseFailAlloc_644_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_st_ref_set(v___y_609_, v___x_640_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___boxed(lean_object* v_mod_691_, lean_object* v_isMeta_692_, lean_object* v_hint_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
uint8_t v_isMeta_boxed_701_; lean_object* v_res_702_; 
v_isMeta_boxed_701_ = lean_unbox(v_isMeta_692_);
v_res_702_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_mod_691_, v_isMeta_boxed_701_, v_hint_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(lean_object* v___x_703_, lean_object* v_declName_704_, lean_object* v_as_705_, size_t v_sz_706_, size_t v_i_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = lean_usize_dec_lt(v_i_707_, v_sz_706_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; 
lean_dec(v_declName_704_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_b_708_);
return v___x_717_;
}
else
{
lean_object* v___x_718_; lean_object* v_modules_719_; lean_object* v___x_720_; lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v_toImport_723_; lean_object* v_module_724_; uint8_t v___x_725_; lean_object* v___x_726_; 
v___x_718_ = l_Lean_Environment_header(v___x_703_);
v_modules_719_ = lean_ctor_get(v___x_718_, 3);
lean_inc_ref(v_modules_719_);
lean_dec_ref(v___x_718_);
v___x_720_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_721_ = lean_array_uget_borrowed(v_as_705_, v_i_707_);
v___x_722_ = lean_array_get(v___x_720_, v_modules_719_, v_a_721_);
lean_dec_ref(v_modules_719_);
v_toImport_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_ref(v_toImport_723_);
lean_dec(v___x_722_);
v_module_724_ = lean_ctor_get(v_toImport_723_, 0);
lean_inc(v_module_724_);
lean_dec_ref(v_toImport_723_);
v___x_725_ = 0;
lean_inc(v_declName_704_);
v___x_726_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_module_724_, v___x_725_, v_declName_704_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_727_; size_t v___x_728_; size_t v___x_729_; 
lean_dec_ref_known(v___x_726_, 1);
v___x_727_ = lean_box(0);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_707_, v___x_728_);
v_i_707_ = v___x_729_;
v_b_708_ = v___x_727_;
goto _start;
}
else
{
lean_dec(v_declName_704_);
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1___boxed(lean_object* v___x_731_, lean_object* v_declName_732_, lean_object* v_as_733_, lean_object* v_sz_734_, lean_object* v_i_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
size_t v_sz_boxed_744_; size_t v_i_boxed_745_; lean_object* v_res_746_; 
v_sz_boxed_744_ = lean_unbox_usize(v_sz_734_);
lean_dec(v_sz_734_);
v_i_boxed_745_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(v___x_731_, v_declName_732_, v_as_733_, v_sz_boxed_744_, v_i_boxed_745_, v_b_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_as_733_);
lean_dec_ref(v___x_731_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(lean_object* v_a_747_, lean_object* v_x_748_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_749_; 
v___x_749_ = lean_box(0);
return v___x_749_;
}
else
{
lean_object* v_key_750_; lean_object* v_value_751_; lean_object* v_tail_752_; uint8_t v___x_753_; 
v_key_750_ = lean_ctor_get(v_x_748_, 0);
v_value_751_ = lean_ctor_get(v_x_748_, 1);
v_tail_752_ = lean_ctor_get(v_x_748_, 2);
v___x_753_ = lean_name_eq(v_key_750_, v_a_747_);
if (v___x_753_ == 0)
{
v_x_748_ = v_tail_752_;
goto _start;
}
else
{
lean_object* v___x_755_; 
lean_inc(v_value_751_);
v___x_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_755_, 0, v_value_751_);
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_756_, lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_756_, v_x_757_);
lean_dec(v_x_757_);
lean_dec(v_a_756_);
return v_res_758_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_759_; uint64_t v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(1723u);
v___x_760_ = lean_uint64_of_nat(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(lean_object* v_m_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_buckets_763_; lean_object* v___x_764_; uint64_t v___y_766_; 
v_buckets_763_ = lean_ctor_get(v_m_761_, 1);
v___x_764_ = lean_array_get_size(v_buckets_763_);
if (lean_obj_tag(v_a_762_) == 0)
{
uint64_t v___x_780_; 
v___x_780_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0);
v___y_766_ = v___x_780_;
goto v___jp_765_;
}
else
{
uint64_t v_hash_781_; 
v_hash_781_ = lean_ctor_get_uint64(v_a_762_, sizeof(void*)*2);
v___y_766_ = v_hash_781_;
goto v___jp_765_;
}
v___jp_765_:
{
uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v_fold_769_; uint64_t v___x_770_; uint64_t v___x_771_; uint64_t v___x_772_; size_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_767_ = 32ULL;
v___x_768_ = lean_uint64_shift_right(v___y_766_, v___x_767_);
v_fold_769_ = lean_uint64_xor(v___y_766_, v___x_768_);
v___x_770_ = 16ULL;
v___x_771_ = lean_uint64_shift_right(v_fold_769_, v___x_770_);
v___x_772_ = lean_uint64_xor(v_fold_769_, v___x_771_);
v___x_773_ = lean_uint64_to_usize(v___x_772_);
v___x_774_ = lean_usize_of_nat(v___x_764_);
v___x_775_ = ((size_t)1ULL);
v___x_776_ = lean_usize_sub(v___x_774_, v___x_775_);
v___x_777_ = lean_usize_land(v___x_773_, v___x_776_);
v___x_778_ = lean_array_uget_borrowed(v_buckets_763_, v___x_777_);
v___x_779_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_762_, v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___boxed(lean_object* v_m_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v_m_782_, v_a_783_);
lean_dec(v_a_783_);
lean_dec_ref(v_m_782_);
return v_res_784_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1));
v___x_788_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0));
v___x_789_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_788_, v___x_787_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(lean_object* v_declName_792_, uint8_t v_isMeta_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_env_805_; lean_object* v___y_807_; lean_object* v___x_820_; 
v___x_801_ = lean_st_ref_get(v___y_799_);
v_env_805_ = lean_ctor_get(v___x_801_, 0);
lean_inc_ref(v_env_805_);
lean_dec(v___x_801_);
v___x_820_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_805_, v_declName_792_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_dec_ref(v_env_805_);
lean_dec(v_declName_792_);
goto v___jp_802_;
}
else
{
lean_object* v_val_821_; lean_object* v___x_822_; lean_object* v_modules_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_val_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = l_Lean_Environment_header(v_env_805_);
v_modules_823_ = lean_ctor_get(v___x_822_, 3);
lean_inc_ref(v_modules_823_);
lean_dec_ref(v___x_822_);
v___x_824_ = lean_array_get_size(v_modules_823_);
v___x_825_ = lean_nat_dec_lt(v_val_821_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec_ref(v_modules_823_);
lean_dec(v_val_821_);
lean_dec_ref(v_env_805_);
lean_dec(v_declName_792_);
goto v___jp_802_;
}
else
{
lean_object* v___x_826_; lean_object* v_env_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___y_831_; 
v___x_826_ = lean_st_ref_get(v___y_799_);
v_env_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc_ref(v_env_827_);
lean_dec(v___x_826_);
v___x_828_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2);
v___x_829_ = lean_array_fget(v_modules_823_, v_val_821_);
lean_dec(v_val_821_);
lean_dec_ref(v_modules_823_);
if (v_isMeta_793_ == 0)
{
lean_dec_ref(v_env_827_);
v___y_831_ = v_isMeta_793_;
goto v___jp_830_;
}
else
{
uint8_t v___x_842_; uint8_t v___x_843_; 
lean_inc(v_declName_792_);
v___x_842_ = l_Lean_isMarkedMeta(v_env_827_, v_declName_792_);
v___x_843_ = lean_bool_not(v___x_842_);
v___y_831_ = v___x_843_;
goto v___jp_830_;
}
v___jp_830_:
{
lean_object* v_toImport_832_; lean_object* v_module_833_; lean_object* v___x_834_; 
v_toImport_832_ = lean_ctor_get(v___x_829_, 0);
lean_inc_ref(v_toImport_832_);
lean_dec(v___x_829_);
v_module_833_ = lean_ctor_get(v_toImport_832_, 0);
lean_inc(v_module_833_);
lean_dec_ref(v_toImport_832_);
lean_inc(v_declName_792_);
v___x_834_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_module_833_, v___y_831_, v_declName_792_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref_known(v___x_834_, 1);
v___x_835_ = l_Lean_indirectModUseExt;
v___x_836_ = lean_box(1);
v___x_837_ = lean_box(0);
lean_inc_ref(v_env_805_);
v___x_838_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_828_, v___x_835_, v_env_805_, v___x_836_, v___x_837_);
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v___x_838_, v_declName_792_);
lean_dec(v___x_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; 
v___x_840_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3));
v___y_807_ = v___x_840_;
goto v___jp_806_;
}
else
{
lean_object* v_val_841_; 
v_val_841_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_839_, 1);
v___y_807_ = v_val_841_;
goto v___jp_806_;
}
}
else
{
lean_dec_ref(v_env_805_);
lean_dec(v_declName_792_);
return v___x_834_;
}
}
}
}
v___jp_802_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(0);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
v___jp_806_:
{
lean_object* v___x_808_; size_t v_sz_809_; size_t v___x_810_; lean_object* v___x_811_; 
v___x_808_ = lean_box(0);
v_sz_809_ = lean_array_size(v___y_807_);
v___x_810_ = ((size_t)0ULL);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(v_env_805_, v_declName_792_, v___y_807_, v_sz_809_, v___x_810_, v___x_808_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec_ref(v___y_807_);
lean_dec_ref(v_env_805_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v___x_811_, 0);
lean_dec(v_unused_819_);
v___x_813_ = v___x_811_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_dec(v___x_811_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_808_);
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_808_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___boxed(lean_object* v_declName_844_, lean_object* v_isMeta_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
uint8_t v_isMeta_boxed_853_; lean_object* v_res_854_; 
v_isMeta_boxed_853_ = lean_unbox(v_isMeta_845_);
v_res_854_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(v_declName_844_, v_isMeta_boxed_853_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(lean_object* v___x_855_, lean_object* v___x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_855_, v___x_856_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; uint8_t v___x_866_; lean_object* v___x_867_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc_n(v_a_865_, 2);
lean_dec_ref_known(v___x_864_, 1);
v___x_866_ = 0;
v___x_867_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(v_a_865_, v___x_866_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_867_, 0);
lean_dec(v_unused_875_);
v___x_869_ = v___x_867_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_dec(v___x_867_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_a_865_);
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_865_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_865_);
v_a_876_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_867_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_867_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed(lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(v___x_884_, v___x_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(lean_object* v___y_894_, uint8_t v_isExporting_895_, lean_object* v___x_896_, lean_object* v___y_897_, lean_object* v___x_898_, lean_object* v_a_x3f_899_){
_start:
{
lean_object* v___x_901_; lean_object* v_env_902_; lean_object* v_nextMacroScope_903_; lean_object* v_ngen_904_; lean_object* v_auxDeclNGen_905_; lean_object* v_traceState_906_; lean_object* v_messages_907_; lean_object* v_infoState_908_; lean_object* v_snapshotTasks_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_934_; 
v___x_901_ = lean_st_ref_take(v___y_894_);
v_env_902_ = lean_ctor_get(v___x_901_, 0);
v_nextMacroScope_903_ = lean_ctor_get(v___x_901_, 1);
v_ngen_904_ = lean_ctor_get(v___x_901_, 2);
v_auxDeclNGen_905_ = lean_ctor_get(v___x_901_, 3);
v_traceState_906_ = lean_ctor_get(v___x_901_, 4);
v_messages_907_ = lean_ctor_get(v___x_901_, 6);
v_infoState_908_ = lean_ctor_get(v___x_901_, 7);
v_snapshotTasks_909_ = lean_ctor_get(v___x_901_, 8);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v___x_901_, 5);
lean_dec(v_unused_935_);
v___x_911_ = v___x_901_;
v_isShared_912_ = v_isSharedCheck_934_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_snapshotTasks_909_);
lean_inc(v_infoState_908_);
lean_inc(v_messages_907_);
lean_inc(v_traceState_906_);
lean_inc(v_auxDeclNGen_905_);
lean_inc(v_ngen_904_);
lean_inc(v_nextMacroScope_903_);
lean_inc(v_env_902_);
lean_dec(v___x_901_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_934_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_913_ = l_Lean_Environment_setExporting(v_env_902_, v_isExporting_895_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 5, v___x_896_);
lean_ctor_set(v___x_911_, 0, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_nextMacroScope_903_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_ngen_904_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_auxDeclNGen_905_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_traceState_906_);
lean_ctor_set(v_reuseFailAlloc_933_, 5, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_933_, 6, v_messages_907_);
lean_ctor_set(v_reuseFailAlloc_933_, 7, v_infoState_908_);
lean_ctor_set(v_reuseFailAlloc_933_, 8, v_snapshotTasks_909_);
v___x_915_ = v_reuseFailAlloc_933_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v_mctx_918_; lean_object* v_zetaDeltaFVarIds_919_; lean_object* v_postponed_920_; lean_object* v_diag_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_931_; 
v___x_916_ = lean_st_ref_set(v___y_894_, v___x_915_);
v___x_917_ = lean_st_ref_take(v___y_897_);
v_mctx_918_ = lean_ctor_get(v___x_917_, 0);
v_zetaDeltaFVarIds_919_ = lean_ctor_get(v___x_917_, 2);
v_postponed_920_ = lean_ctor_get(v___x_917_, 3);
v_diag_921_ = lean_ctor_get(v___x_917_, 4);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v___x_917_, 1);
lean_dec(v_unused_932_);
v___x_923_ = v___x_917_;
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_diag_921_);
lean_inc(v_postponed_920_);
lean_inc(v_zetaDeltaFVarIds_919_);
lean_inc(v_mctx_918_);
lean_dec(v___x_917_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v___x_898_);
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_mctx_918_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_zetaDeltaFVarIds_919_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_postponed_920_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v_diag_921_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_st_ref_set(v___y_897_, v___x_926_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0___boxed(lean_object* v___y_936_, lean_object* v_isExporting_937_, lean_object* v___x_938_, lean_object* v___y_939_, lean_object* v___x_940_, lean_object* v_a_x3f_941_, lean_object* v___y_942_){
_start:
{
uint8_t v_isExporting_boxed_943_; lean_object* v_res_944_; 
v_isExporting_boxed_943_ = lean_unbox(v_isExporting_937_);
v_res_944_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_936_, v_isExporting_boxed_943_, v___x_938_, v___y_939_, v___x_940_, v_a_x3f_941_);
lean_dec(v_a_x3f_941_);
lean_dec(v___y_939_);
lean_dec(v___y_936_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(lean_object* v_x_945_, uint8_t v_isExporting_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v___x_954_; lean_object* v_env_955_; uint8_t v_isExporting_956_; uint8_t v___y_1023_; lean_object* v___x_1025_; uint8_t v_isModule_1026_; uint8_t v___x_1027_; 
v___x_954_ = lean_st_ref_get(v___y_952_);
v_env_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc_ref(v_env_955_);
lean_dec(v___x_954_);
v_isExporting_956_ = lean_ctor_get_uint8(v_env_955_, sizeof(void*)*8);
v___x_1025_ = l_Lean_Environment_header(v_env_955_);
lean_dec_ref(v_env_955_);
v_isModule_1026_ = lean_ctor_get_uint8(v___x_1025_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1025_);
v___x_1027_ = lean_bool_not(v_isModule_1026_);
if (v___x_1027_ == 0)
{
if (v_isExporting_956_ == 0)
{
if (v_isExporting_946_ == 0)
{
lean_object* v___x_1028_; 
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
v___x_1028_ = lean_apply_7(v_x_945_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, lean_box(0));
return v___x_1028_;
}
else
{
goto v___jp_957_;
}
}
else
{
v___y_1023_ = v_isExporting_946_;
goto v___jp_1022_;
}
}
else
{
v___y_1023_ = v___x_1027_;
goto v___jp_1022_;
}
v___jp_957_:
{
lean_object* v___x_958_; lean_object* v_env_959_; lean_object* v_nextMacroScope_960_; lean_object* v_ngen_961_; lean_object* v_auxDeclNGen_962_; lean_object* v_traceState_963_; lean_object* v_messages_964_; lean_object* v_infoState_965_; lean_object* v_snapshotTasks_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_1020_; 
v___x_958_ = lean_st_ref_take(v___y_952_);
v_env_959_ = lean_ctor_get(v___x_958_, 0);
v_nextMacroScope_960_ = lean_ctor_get(v___x_958_, 1);
v_ngen_961_ = lean_ctor_get(v___x_958_, 2);
v_auxDeclNGen_962_ = lean_ctor_get(v___x_958_, 3);
v_traceState_963_ = lean_ctor_get(v___x_958_, 4);
v_messages_964_ = lean_ctor_get(v___x_958_, 6);
v_infoState_965_ = lean_ctor_get(v___x_958_, 7);
v_snapshotTasks_966_ = lean_ctor_get(v___x_958_, 8);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_958_, 5);
lean_dec(v_unused_1021_);
v___x_968_ = v___x_958_;
v_isShared_969_ = v_isSharedCheck_1020_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_snapshotTasks_966_);
lean_inc(v_infoState_965_);
lean_inc(v_messages_964_);
lean_inc(v_traceState_963_);
lean_inc(v_auxDeclNGen_962_);
lean_inc(v_ngen_961_);
lean_inc(v_nextMacroScope_960_);
lean_inc(v_env_959_);
lean_dec(v___x_958_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_1020_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_970_ = l_Lean_Environment_setExporting(v_env_959_, v_isExporting_946_);
v___x_971_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 5, v___x_971_);
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_973_ = v___x_968_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_970_);
lean_ctor_set(v_reuseFailAlloc_1019_, 1, v_nextMacroScope_960_);
lean_ctor_set(v_reuseFailAlloc_1019_, 2, v_ngen_961_);
lean_ctor_set(v_reuseFailAlloc_1019_, 3, v_auxDeclNGen_962_);
lean_ctor_set(v_reuseFailAlloc_1019_, 4, v_traceState_963_);
lean_ctor_set(v_reuseFailAlloc_1019_, 5, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_1019_, 6, v_messages_964_);
lean_ctor_set(v_reuseFailAlloc_1019_, 7, v_infoState_965_);
lean_ctor_set(v_reuseFailAlloc_1019_, 8, v_snapshotTasks_966_);
v___x_973_ = v_reuseFailAlloc_1019_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_mctx_976_; lean_object* v_zetaDeltaFVarIds_977_; lean_object* v_postponed_978_; lean_object* v_diag_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_1017_; 
v___x_974_ = lean_st_ref_set(v___y_952_, v___x_973_);
v___x_975_ = lean_st_ref_take(v___y_950_);
v_mctx_976_ = lean_ctor_get(v___x_975_, 0);
v_zetaDeltaFVarIds_977_ = lean_ctor_get(v___x_975_, 2);
v_postponed_978_ = lean_ctor_get(v___x_975_, 3);
v_diag_979_ = lean_ctor_get(v___x_975_, 4);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; 
v_unused_1018_ = lean_ctor_get(v___x_975_, 1);
lean_dec(v_unused_1018_);
v___x_981_ = v___x_975_;
v_isShared_982_ = v_isSharedCheck_1017_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_diag_979_);
lean_inc(v_postponed_978_);
lean_inc(v_zetaDeltaFVarIds_977_);
lean_inc(v_mctx_976_);
lean_dec(v___x_975_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_1017_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v___x_983_);
v___x_985_ = v___x_981_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_mctx_976_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_983_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_zetaDeltaFVarIds_977_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_postponed_978_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v_diag_979_);
v___x_985_ = v_reuseFailAlloc_1016_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_986_; lean_object* v_r_987_; 
v___x_986_ = lean_st_ref_set(v___y_950_, v___x_985_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
v_r_987_ = lean_apply_7(v_x_945_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, lean_box(0));
if (lean_obj_tag(v_r_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1004_; 
v_a_988_ = lean_ctor_get(v_r_987_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_r_987_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_990_ = v_r_987_;
v_isShared_991_ = v_isSharedCheck_1004_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v_r_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1004_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
lean_inc(v_a_988_);
if (v_isShared_991_ == 0)
{
lean_ctor_set_tag(v___x_990_, 1);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_1003_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
v___x_994_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_952_, v_isExporting_956_, v___x_971_, v___y_950_, v___x_983_, v___x_993_);
lean_dec_ref(v___x_993_);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; 
v_unused_1002_ = lean_ctor_get(v___x_994_, 0);
lean_dec(v_unused_1002_);
v___x_996_ = v___x_994_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_dec(v___x_994_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v_a_988_);
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_988_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
v_a_1005_ = lean_ctor_get(v_r_987_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v_r_987_, 1);
v___x_1006_ = lean_box(0);
v___x_1007_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_952_, v_isExporting_956_, v___x_971_, v___y_950_, v___x_983_, v___x_1006_);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v___x_1007_, 0);
lean_dec(v_unused_1015_);
v___x_1009_ = v___x_1007_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v___x_1007_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 1);
lean_ctor_set(v___x_1009_, 0, v_a_1005_);
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1005_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
}
}
v___jp_1022_:
{
if (v___y_1023_ == 0)
{
goto v___jp_957_;
}
else
{
lean_object* v___x_1024_; 
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
v___x_1024_ = lean_apply_7(v_x_945_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, lean_box(0));
return v___x_1024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___boxed(lean_object* v_x_1029_, lean_object* v_isExporting_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
uint8_t v_isExporting_boxed_1038_; lean_object* v_res_1039_; 
v_isExporting_boxed_1038_ = lean_unbox(v_isExporting_1030_);
v_res_1039_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1029_, v_isExporting_boxed_1038_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(lean_object* v_x_1040_, uint8_t v_when_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
if (v_when_1041_ == 0)
{
lean_object* v___x_1049_; 
lean_inc(v___y_1047_);
lean_inc_ref(v___y_1046_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
v___x_1049_ = lean_apply_7(v_x_1040_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, lean_box(0));
return v___x_1049_;
}
else
{
uint8_t v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = 0;
v___x_1051_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1040_, v___x_1050_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg___boxed(lean_object* v_x_1052_, lean_object* v_when_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
uint8_t v_when_boxed_1061_; lean_object* v_res_1062_; 
v_when_boxed_1061_ = lean_unbox(v_when_1053_);
v_res_1062_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v_x_1052_, v_when_boxed_1061_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(lean_object* v___x_1064_, lean_object* v___x_1065_, lean_object* v_____r_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1074_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12));
v___x_1075_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13));
v___x_1076_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0));
v___x_1077_ = l_Lean_Name_mkStr4(v___x_1064_, v___x_1074_, v___x_1075_, v___x_1076_);
lean_inc(v___x_1065_);
v___x_1078_ = l_Lean_Syntax_isOfKind(v___x_1065_, v___x_1077_);
lean_dec(v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v___x_1065_);
v___x_1079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; 
v___x_1080_ = lean_unsigned_to_nat(2u);
v___x_1081_ = l_Lean_Syntax_getArg(v___x_1065_, v___x_1080_);
lean_dec(v___x_1065_);
v___x_1082_ = lean_box(0);
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1083_, 0, v___x_1081_);
lean_closure_set(v___f_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v___f_1083_, v___x_1078_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___boxed(lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_____r_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1085_, v___x_1086_, v_____r_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec_ref(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1095_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1));
v___x_1102_ = l_Lean_mkConst(v___x_1101_, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2);
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_fileName_1119_; lean_object* v_fileMap_1120_; lean_object* v_options_1121_; lean_object* v_currRecDepth_1122_; lean_object* v_maxRecDepth_1123_; lean_object* v_ref_1124_; lean_object* v_currNamespace_1125_; lean_object* v_openDecls_1126_; lean_object* v_initHeartbeats_1127_; lean_object* v_maxHeartbeats_1128_; lean_object* v_quotContext_1129_; lean_object* v_currMacroScope_1130_; uint8_t v_diag_1131_; lean_object* v_cancelTk_x3f_1132_; uint8_t v_suppressElabErrors_1133_; lean_object* v_inheritedTraceOptions_1134_; lean_object* v___x_1135_; lean_object* v_a_1137_; lean_object* v___y_1166_; lean_object* v___x_1176_; lean_object* v_ref_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_fileName_1119_ = lean_ctor_get(v_a_1116_, 0);
v_fileMap_1120_ = lean_ctor_get(v_a_1116_, 1);
v_options_1121_ = lean_ctor_get(v_a_1116_, 2);
v_currRecDepth_1122_ = lean_ctor_get(v_a_1116_, 3);
v_maxRecDepth_1123_ = lean_ctor_get(v_a_1116_, 4);
v_ref_1124_ = lean_ctor_get(v_a_1116_, 5);
v_currNamespace_1125_ = lean_ctor_get(v_a_1116_, 6);
v_openDecls_1126_ = lean_ctor_get(v_a_1116_, 7);
v_initHeartbeats_1127_ = lean_ctor_get(v_a_1116_, 8);
v_maxHeartbeats_1128_ = lean_ctor_get(v_a_1116_, 9);
v_quotContext_1129_ = lean_ctor_get(v_a_1116_, 10);
v_currMacroScope_1130_ = lean_ctor_get(v_a_1116_, 11);
v_diag_1131_ = lean_ctor_get_uint8(v_a_1116_, sizeof(void*)*14);
v_cancelTk_x3f_1132_ = lean_ctor_get(v_a_1116_, 12);
v_suppressElabErrors_1133_ = lean_ctor_get_uint8(v_a_1116_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1134_ = lean_ctor_get(v_a_1116_, 13);
v___x_1135_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11));
lean_inc(v_a_1111_);
v___x_1176_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_a_1111_);
v_ref_1177_ = l_Lean_replaceRef(v_a_1111_, v_ref_1124_);
lean_inc_ref(v_inheritedTraceOptions_1134_);
lean_inc(v_cancelTk_x3f_1132_);
lean_inc(v_currMacroScope_1130_);
lean_inc(v_quotContext_1129_);
lean_inc(v_maxHeartbeats_1128_);
lean_inc(v_initHeartbeats_1127_);
lean_inc(v_openDecls_1126_);
lean_inc(v_currNamespace_1125_);
lean_inc(v_maxRecDepth_1123_);
lean_inc(v_currRecDepth_1122_);
lean_inc_ref(v_options_1121_);
lean_inc_ref(v_fileMap_1120_);
lean_inc_ref(v_fileName_1119_);
v___x_1178_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1178_, 0, v_fileName_1119_);
lean_ctor_set(v___x_1178_, 1, v_fileMap_1120_);
lean_ctor_set(v___x_1178_, 2, v_options_1121_);
lean_ctor_set(v___x_1178_, 3, v_currRecDepth_1122_);
lean_ctor_set(v___x_1178_, 4, v_maxRecDepth_1123_);
lean_ctor_set(v___x_1178_, 5, v_ref_1177_);
lean_ctor_set(v___x_1178_, 6, v_currNamespace_1125_);
lean_ctor_set(v___x_1178_, 7, v_openDecls_1126_);
lean_ctor_set(v___x_1178_, 8, v_initHeartbeats_1127_);
lean_ctor_set(v___x_1178_, 9, v_maxHeartbeats_1128_);
lean_ctor_set(v___x_1178_, 10, v_quotContext_1129_);
lean_ctor_set(v___x_1178_, 11, v_currMacroScope_1130_);
lean_ctor_set(v___x_1178_, 12, v_cancelTk_x3f_1132_);
lean_ctor_set(v___x_1178_, 13, v_inheritedTraceOptions_1134_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*14, v_diag_1131_);
lean_ctor_set_uint8(v___x_1178_, sizeof(void*)*14 + 1, v_suppressElabErrors_1133_);
v___x_1179_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5));
lean_inc(v___x_1176_);
v___x_1180_ = l_Lean_Syntax_isOfKind(v___x_1176_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1135_, v___x_1176_, v___x_1181_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v___x_1178_, v_a_1117_);
lean_dec_ref_known(v___x_1178_, 14);
v___y_1166_ = v___x_1182_;
goto v___jp_1165_;
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = l_Lean_Syntax_getArg(v___x_1176_, v___x_1183_);
v___x_1185_ = l_Lean_Syntax_isNameLit_x3f(v___x_1184_);
lean_dec(v___x_1184_);
if (lean_obj_tag(v___x_1185_) == 1)
{
lean_object* v_val_1186_; 
lean_dec_ref_known(v___x_1178_, 14);
lean_dec(v___x_1176_);
v_val_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_val_1186_);
lean_dec_ref_known(v___x_1185_, 1);
v_a_1137_ = v_val_1186_;
goto v___jp_1136_;
}
else
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
lean_dec(v___x_1185_);
v___x_1187_ = lean_box(0);
v___x_1188_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(v___x_1135_, v___x_1176_, v___x_1187_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v___x_1178_, v_a_1117_);
lean_dec_ref_known(v___x_1178_, 14);
v___y_1166_ = v___x_1188_;
goto v___jp_1165_;
}
}
v___jp_1136_:
{
lean_object* v___x_1138_; lean_object* v_infoState_1139_; uint8_t v_enabled_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1138_ = lean_st_ref_get(v_a_1117_);
v_infoState_1139_ = lean_ctor_get(v___x_1138_, 7);
lean_inc_ref(v_infoState_1139_);
lean_dec(v___x_1138_);
v_enabled_1140_ = lean_ctor_get_uint8(v_infoState_1139_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1139_);
lean_inc(v_a_1137_);
v___x_1141_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1137_);
lean_inc_ref(v___x_1141_);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v_a_1137_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
if (v_enabled_1140_ == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref(v___x_1141_);
lean_dec(v_a_1111_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1144_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3);
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_box(0);
v___x_1147_ = 0;
v___x_1148_ = l_Lean_Elab_Term_addTermInfo_x27(v_a_1111_, v___x_1141_, v___x_1144_, v___x_1145_, v___x_1146_, v___x_1147_, v___x_1147_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1155_ == 0)
{
lean_object* v_unused_1156_; 
v_unused_1156_ = lean_ctor_get(v___x_1148_, 0);
lean_dec(v_unused_1156_);
v___x_1150_ = v___x_1148_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_dec(v___x_1148_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1142_);
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1142_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref_known(v___x_1142_, 2);
v_a_1157_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1148_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1148_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
v___jp_1165_:
{
if (lean_obj_tag(v___y_1166_) == 0)
{
lean_object* v_a_1167_; 
v_a_1167_ = lean_ctor_get(v___y_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___y_1166_, 1);
v_a_1137_ = v_a_1167_;
goto v___jp_1136_;
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v_a_1111_);
v_a_1168_ = lean_ctor_get(v___y_1166_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___y_1166_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___y_1166_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___y_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed(lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_);
lean_dec(v_a_1195_);
lean_dec_ref(v_a_1194_);
lean_dec(v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_a_1190_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(lean_object* v_00_u03b1_1198_, lean_object* v_x_1199_, uint8_t v_isExporting_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_1199_, v_isExporting_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___boxed(lean_object* v_00_u03b1_1209_, lean_object* v_x_1210_, lean_object* v_isExporting_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v_isExporting_boxed_1219_; lean_object* v_res_1220_; 
v_isExporting_boxed_1219_ = lean_unbox(v_isExporting_1211_);
v_res_1220_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(v_00_u03b1_1209_, v_x_1210_, v_isExporting_boxed_1219_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(lean_object* v_00_u03b1_1221_, lean_object* v_x_1222_, uint8_t v_when_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v_x_1222_, v_when_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_x_1233_, lean_object* v_when_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v_when_boxed_1242_; lean_object* v_res_1243_; 
v_when_boxed_1242_ = lean_unbox(v_when_1234_);
v_res_1243_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(v_00_u03b1_1232_, v_x_1233_, v_when_boxed_1242_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(lean_object* v_00_u03b2_1244_, lean_object* v_m_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v_m_1245_, v_a_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1248_, lean_object* v_m_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(v_00_u03b2_1248_, v_m_1249_, v_a_1250_);
lean_dec(v_a_1250_);
lean_dec_ref(v_m_1249_);
return v_res_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v_x_1253_, v_x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(v_00_u03b2_1256_, v_x_1257_, v_x_1258_);
lean_dec_ref(v_x_1258_);
lean_dec_ref(v_x_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(lean_object* v_cls_1261_, lean_object* v_msg_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_1261_, v_msg_1262_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1271_, lean_object* v_msg_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(v_cls_1271_, v_msg_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1281_, lean_object* v_a_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_1282_, v_x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1285_, lean_object* v_a_1286_, lean_object* v_x_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(v_00_u03b2_1285_, v_a_1286_, v_x_1287_);
lean_dec(v_x_1287_);
lean_dec(v_a_1286_);
return v_res_1288_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, size_t v_x_1291_, lean_object* v_x_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1290_, v_x_1291_, v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
size_t v_x_11553__boxed_1298_; uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_x_11553__boxed_1298_ = lean_unbox_usize(v_x_1296_);
lean_dec(v_x_1296_);
v_res_1299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1294_, v_x_1295_, v_x_11553__boxed_1298_, v_x_1297_);
lean_dec_ref(v_x_1297_);
lean_dec_ref(v_x_1295_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(lean_object* v_00_u03b2_1301_, lean_object* v_keys_1302_, lean_object* v_vals_1303_, lean_object* v_heq_1304_, lean_object* v_i_1305_, lean_object* v_k_1306_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_keys_1302_, v_i_1305_, v_k_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(lean_object* v_00_u03b2_1308_, lean_object* v_keys_1309_, lean_object* v_vals_1310_, lean_object* v_heq_1311_, lean_object* v_i_1312_, lean_object* v_k_1313_){
_start:
{
uint8_t v_res_1314_; lean_object* v_r_1315_; 
v_res_1314_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b2_1308_, v_keys_1309_, v_vals_1310_, v_heq_1311_, v_i_1312_, v_k_1313_);
lean_dec_ref(v_k_1313_);
lean_dec_ref(v_vals_1310_);
lean_dec_ref(v_keys_1309_);
v_r_1315_ = lean_box(v_res_1314_);
return v_r_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(lean_object* v_ev_1317_, lean_object* v___x_1318_, lean_object* v___x_1319_, lean_object* v_typeExpr_1320_, lean_object* v_stx_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v___x_1329_; 
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
v___x_1329_ = lean_apply_8(v_ev_1317_, v_stx_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, lean_box(0));
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1351_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1351_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1351_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_fst_1334_; lean_object* v_snd_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1350_; 
v_fst_1334_ = lean_ctor_get(v_a_1330_, 0);
v_snd_1335_ = lean_ctor_get(v_a_1330_, 1);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_a_1330_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1337_ = v_a_1330_;
v_isShared_1338_ = v_isSharedCheck_1350_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_snd_1335_);
lean_inc(v_fst_1334_);
lean_dec(v_a_1330_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1350_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_fst_1334_);
v___x_1340_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0));
v___x_1341_ = l_Lean_Name_mkStr2(v___x_1318_, v___x_1340_);
v___x_1342_ = l_Lean_Expr_const___override(v___x_1341_, v___x_1319_);
v___x_1343_ = l_Lean_mkAppB(v___x_1342_, v_typeExpr_1320_, v_snd_1335_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v___x_1343_);
lean_ctor_set(v___x_1337_, 0, v___x_1339_);
v___x_1345_ = v___x_1337_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1347_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1345_);
v___x_1347_ = v___x_1332_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v_typeExpr_1320_);
lean_dec(v___x_1319_);
lean_dec_ref(v___x_1318_);
v_a_1352_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1329_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1329_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___boxed(lean_object* v_ev_1360_, lean_object* v___x_1361_, lean_object* v___x_1362_, lean_object* v_typeExpr_1363_, lean_object* v_stx_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1360_, v___x_1361_, v___x_1362_, v_typeExpr_1363_, v_stx_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
return v_res_1372_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1));
v___x_1378_ = l_Lean_Expr_const___override(v___x_1377_, v___x_1376_);
return v___x_1378_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1394_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8));
v___x_1395_ = l_Lean_Expr_const___override(v___x_1394_, v___x_1393_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(lean_object* v_typeExpr_1396_, lean_object* v_ev_1397_, lean_object* v_stx_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_a_1413_; lean_object* v_snd_1414_; lean_object* v___y_1440_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1406_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0));
v___x_1407_ = lean_unsigned_to_nat(0u);
v___x_1408_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1409_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
lean_inc_ref(v_typeExpr_1396_);
v___x_1410_ = l_Lean_Expr_app___override(v___x_1409_, v_typeExpr_1396_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
lean_inc(v_stx_1398_);
v___x_1443_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1398_);
v___x_1444_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4));
v___x_1445_ = l_Lean_Syntax_matchesIdent(v___x_1443_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v_fileName_1446_; lean_object* v_fileMap_1447_; lean_object* v_options_1448_; lean_object* v_currRecDepth_1449_; lean_object* v_maxRecDepth_1450_; lean_object* v_ref_1451_; lean_object* v_currNamespace_1452_; lean_object* v_openDecls_1453_; lean_object* v_initHeartbeats_1454_; lean_object* v_maxHeartbeats_1455_; lean_object* v_quotContext_1456_; lean_object* v_currMacroScope_1457_; uint8_t v_diag_1458_; lean_object* v_cancelTk_x3f_1459_; uint8_t v_suppressElabErrors_1460_; lean_object* v_inheritedTraceOptions_1461_; lean_object* v_ref_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_fileName_1446_ = lean_ctor_get(v_a_1403_, 0);
v_fileMap_1447_ = lean_ctor_get(v_a_1403_, 1);
v_options_1448_ = lean_ctor_get(v_a_1403_, 2);
v_currRecDepth_1449_ = lean_ctor_get(v_a_1403_, 3);
v_maxRecDepth_1450_ = lean_ctor_get(v_a_1403_, 4);
v_ref_1451_ = lean_ctor_get(v_a_1403_, 5);
v_currNamespace_1452_ = lean_ctor_get(v_a_1403_, 6);
v_openDecls_1453_ = lean_ctor_get(v_a_1403_, 7);
v_initHeartbeats_1454_ = lean_ctor_get(v_a_1403_, 8);
v_maxHeartbeats_1455_ = lean_ctor_get(v_a_1403_, 9);
v_quotContext_1456_ = lean_ctor_get(v_a_1403_, 10);
v_currMacroScope_1457_ = lean_ctor_get(v_a_1403_, 11);
v_diag_1458_ = lean_ctor_get_uint8(v_a_1403_, sizeof(void*)*14);
v_cancelTk_x3f_1459_ = lean_ctor_get(v_a_1403_, 12);
v_suppressElabErrors_1460_ = lean_ctor_get_uint8(v_a_1403_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1461_ = lean_ctor_get(v_a_1403_, 13);
v_ref_1462_ = l_Lean_replaceRef(v_stx_1398_, v_ref_1451_);
lean_inc_ref(v_inheritedTraceOptions_1461_);
lean_inc(v_cancelTk_x3f_1459_);
lean_inc(v_currMacroScope_1457_);
lean_inc(v_quotContext_1456_);
lean_inc(v_maxHeartbeats_1455_);
lean_inc(v_initHeartbeats_1454_);
lean_inc(v_openDecls_1453_);
lean_inc(v_currNamespace_1452_);
lean_inc(v_maxRecDepth_1450_);
lean_inc(v_currRecDepth_1449_);
lean_inc_ref(v_options_1448_);
lean_inc_ref(v_fileMap_1447_);
lean_inc_ref(v_fileName_1446_);
v___x_1463_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1463_, 0, v_fileName_1446_);
lean_ctor_set(v___x_1463_, 1, v_fileMap_1447_);
lean_ctor_set(v___x_1463_, 2, v_options_1448_);
lean_ctor_set(v___x_1463_, 3, v_currRecDepth_1449_);
lean_ctor_set(v___x_1463_, 4, v_maxRecDepth_1450_);
lean_ctor_set(v___x_1463_, 5, v_ref_1462_);
lean_ctor_set(v___x_1463_, 6, v_currNamespace_1452_);
lean_ctor_set(v___x_1463_, 7, v_openDecls_1453_);
lean_ctor_set(v___x_1463_, 8, v_initHeartbeats_1454_);
lean_ctor_set(v___x_1463_, 9, v_maxHeartbeats_1455_);
lean_ctor_set(v___x_1463_, 10, v_quotContext_1456_);
lean_ctor_set(v___x_1463_, 11, v_currMacroScope_1457_);
lean_ctor_set(v___x_1463_, 12, v_cancelTk_x3f_1459_);
lean_ctor_set(v___x_1463_, 13, v_inheritedTraceOptions_1461_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*14, v_diag_1458_);
lean_ctor_set_uint8(v___x_1463_, sizeof(void*)*14 + 1, v_suppressElabErrors_1460_);
v___x_1464_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15));
lean_inc(v___x_1443_);
v___x_1465_ = l_Lean_Syntax_isOfKind(v___x_1443_, v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6));
lean_inc(v___x_1443_);
v___x_1467_ = l_Lean_Syntax_isOfKind(v___x_1443_, v___x_1466_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v___x_1443_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1468_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1469_ = l_Lean_Syntax_getArg(v___x_1443_, v___x_1407_);
v___x_1470_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7));
v___x_1471_ = l_Lean_Syntax_matchesIdent(v___x_1469_, v___x_1470_);
if (v___x_1471_ == 0)
{
uint8_t v___x_1472_; 
lean_inc(v___x_1469_);
v___x_1472_ = l_Lean_Syntax_isOfKind(v___x_1469_, v___x_1464_);
if (v___x_1472_ == 0)
{
lean_object* v___x_1473_; 
lean_dec(v___x_1469_);
v___x_1473_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v___x_1443_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1473_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1474_ = lean_unsigned_to_nat(1u);
v___x_1475_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1474_);
lean_dec(v___x_1469_);
v___x_1476_ = l_Lean_Syntax_matchesIdent(v___x_1475_, v___x_1470_);
lean_dec(v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v___x_1443_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1477_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = l_Lean_Syntax_getArg(v___x_1443_, v___x_1474_);
lean_inc(v___x_1478_);
v___x_1479_ = l_Lean_Syntax_matchesNull(v___x_1478_, v___x_1474_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_dec(v___x_1478_);
v___x_1480_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v___x_1443_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1480_;
goto v___jp_1439_;
}
else
{
lean_object* v_stx_1481_; lean_object* v___x_1482_; 
lean_dec(v___x_1443_);
v_stx_1481_ = l_Lean_Syntax_getArg(v___x_1478_, v___x_1407_);
lean_dec(v___x_1478_);
v___x_1482_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v_stx_1481_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1482_;
goto v___jp_1439_;
}
}
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; uint8_t v___x_1485_; 
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = l_Lean_Syntax_getArg(v___x_1443_, v___x_1483_);
lean_inc(v___x_1484_);
v___x_1485_ = l_Lean_Syntax_matchesNull(v___x_1484_, v___x_1483_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1486_; 
lean_inc(v___x_1469_);
v___x_1486_ = l_Lean_Syntax_isOfKind(v___x_1469_, v___x_1464_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
lean_dec(v___x_1484_);
lean_dec(v___x_1469_);
v___x_1487_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v___x_1443_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1487_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = l_Lean_Syntax_getArg(v___x_1469_, v___x_1483_);
lean_dec(v___x_1469_);
v___x_1489_ = l_Lean_Syntax_matchesIdent(v___x_1488_, v___x_1470_);
lean_dec(v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec(v___x_1484_);
v___x_1490_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v___x_1443_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1490_;
goto v___jp_1439_;
}
else
{
if (v___x_1485_ == 0)
{
lean_object* v___x_1491_; 
lean_dec(v___x_1484_);
v___x_1491_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v___x_1443_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1491_;
goto v___jp_1439_;
}
else
{
lean_object* v_stx_1492_; lean_object* v___x_1493_; 
lean_dec(v___x_1443_);
v_stx_1492_ = l_Lean_Syntax_getArg(v___x_1484_, v___x_1407_);
lean_dec(v___x_1484_);
v___x_1493_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v_stx_1492_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1493_;
goto v___jp_1439_;
}
}
}
}
else
{
lean_object* v_stx_1494_; lean_object* v___x_1495_; 
lean_dec(v___x_1469_);
lean_dec(v___x_1443_);
v_stx_1494_ = l_Lean_Syntax_getArg(v___x_1484_, v___x_1407_);
lean_dec(v___x_1484_);
v___x_1495_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v_stx_1494_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1495_;
goto v___jp_1439_;
}
}
}
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = l_Lean_Syntax_getArg(v___x_1443_, v___x_1496_);
v___x_1498_ = l_Lean_Syntax_matchesIdent(v___x_1497_, v___x_1444_);
lean_dec(v___x_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_1397_, v___x_1406_, v___x_1408_, v_typeExpr_1396_, v___x_1443_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v___x_1463_, v_a_1404_);
lean_dec_ref_known(v___x_1463_, 14);
v___y_1440_ = v___x_1499_;
goto v___jp_1439_;
}
else
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec_ref_known(v___x_1463_, 14);
lean_dec(v___x_1443_);
lean_dec_ref(v_ev_1397_);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9);
v___x_1502_ = l_Lean_Expr_app___override(v___x_1501_, v_typeExpr_1396_);
lean_inc_ref(v___x_1502_);
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1500_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v_a_1413_ = v___x_1503_;
v_snd_1414_ = v___x_1502_;
goto v___jp_1412_;
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v___x_1443_);
lean_dec_ref(v_ev_1397_);
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9);
v___x_1506_ = l_Lean_Expr_app___override(v___x_1505_, v_typeExpr_1396_);
lean_inc_ref(v___x_1506_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1504_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v_a_1413_ = v___x_1507_;
v_snd_1414_ = v___x_1506_;
goto v___jp_1412_;
}
v___jp_1412_:
{
lean_object* v___x_1415_; lean_object* v_infoState_1416_; uint8_t v_enabled_1417_; 
v___x_1415_ = lean_st_ref_get(v_a_1404_);
v_infoState_1416_ = lean_ctor_get(v___x_1415_, 7);
lean_inc_ref(v_infoState_1416_);
lean_dec(v___x_1415_);
v_enabled_1417_ = lean_ctor_get_uint8(v_infoState_1416_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1416_);
if (v_enabled_1417_ == 0)
{
lean_object* v___x_1418_; 
lean_dec_ref(v_snd_1414_);
lean_dec_ref_known(v___x_1411_, 1);
lean_dec(v_stx_1398_);
v___x_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1418_, 0, v_a_1413_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = lean_box(0);
v___x_1421_ = 0;
v___x_1422_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1398_, v_snd_1414_, v___x_1411_, v___x_1419_, v___x_1420_, v___x_1421_, v___x_1421_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1422_, 0);
lean_dec(v_unused_1430_);
v___x_1424_ = v___x_1422_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v___x_1422_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_a_1413_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1413_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v_a_1413_);
v_a_1431_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1422_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1422_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
v___jp_1439_:
{
if (lean_obj_tag(v___y_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v_snd_1442_; 
v_a_1441_ = lean_ctor_get(v___y_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___y_1440_, 1);
v_snd_1442_ = lean_ctor_get(v_a_1441_, 1);
lean_inc(v_snd_1442_);
v_a_1413_ = v_a_1441_;
v_snd_1414_ = v_snd_1442_;
goto v___jp_1412_;
}
else
{
lean_dec_ref_known(v___x_1411_, 1);
lean_dec(v_stx_1398_);
return v___y_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___boxed(lean_object* v_typeExpr_1508_, lean_object* v_ev_1509_, lean_object* v_stx_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v_typeExpr_1508_, v_ev_1509_, v_stx_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(lean_object* v_00_u03b1_1519_, lean_object* v_typeExpr_1520_, lean_object* v_ev_1521_, lean_object* v_stx_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(v_typeExpr_1520_, v_ev_1521_, v_stx_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed(lean_object* v_00_u03b1_1531_, lean_object* v_typeExpr_1532_, lean_object* v_ev_1533_, lean_object* v_stx_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v_res_1542_; 
v_res_1542_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(v_00_u03b1_1531_, v_typeExpr_1532_, v_ev_1533_, v_stx_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
return v_res_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(uint8_t v___x_1543_, lean_object* v_as_1544_, size_t v_i_1545_, size_t v_stop_1546_, lean_object* v_b_1547_){
_start:
{
lean_object* v___y_1549_; uint8_t v___x_1553_; 
v___x_1553_ = lean_usize_dec_eq(v_i_1545_, v_stop_1546_);
if (v___x_1553_ == 0)
{
lean_object* v_fst_1554_; uint8_t v___x_1555_; 
v_fst_1554_ = lean_ctor_get(v_b_1547_, 0);
v___x_1555_ = lean_unbox(v_fst_1554_);
if (v___x_1555_ == 0)
{
lean_object* v_snd_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1564_; 
v_snd_1556_ = lean_ctor_get(v_b_1547_, 1);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_b_1547_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v_b_1547_, 0);
lean_dec(v_unused_1565_);
v___x_1558_ = v_b_1547_;
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_snd_1556_);
lean_dec(v_b_1547_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1560_ = lean_box(v___x_1543_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1560_);
v___x_1562_ = v___x_1558_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_snd_1556_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
v___y_1549_ = v___x_1562_;
goto v___jp_1548_;
}
}
}
else
{
lean_object* v_snd_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1576_; 
v_snd_1566_ = lean_ctor_get(v_b_1547_, 1);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_b_1547_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v_b_1547_, 0);
lean_dec(v_unused_1577_);
v___x_1568_ = v_b_1547_;
v_isShared_1569_ = v_isSharedCheck_1576_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snd_1566_);
lean_dec(v_b_1547_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1576_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1570_ = lean_array_uget_borrowed(v_as_1544_, v_i_1545_);
lean_inc(v___x_1570_);
v___x_1571_ = lean_array_push(v_snd_1566_, v___x_1570_);
v___x_1572_ = lean_box(v___x_1553_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1571_);
lean_ctor_set(v___x_1568_, 0, v___x_1572_);
v___x_1574_ = v___x_1568_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1571_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
v___y_1549_ = v___x_1574_;
goto v___jp_1548_;
}
}
}
}
else
{
return v_b_1547_;
}
v___jp_1548_:
{
size_t v___x_1550_; size_t v___x_1551_; 
v___x_1550_ = ((size_t)1ULL);
v___x_1551_ = lean_usize_add(v_i_1545_, v___x_1550_);
v_i_1545_ = v___x_1551_;
v_b_1547_ = v___y_1549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3___boxed(lean_object* v___x_1578_, lean_object* v_as_1579_, lean_object* v_i_1580_, lean_object* v_stop_1581_, lean_object* v_b_1582_){
_start:
{
uint8_t v___x_1661__boxed_1583_; size_t v_i_boxed_1584_; size_t v_stop_boxed_1585_; lean_object* v_res_1586_; 
v___x_1661__boxed_1583_ = lean_unbox(v___x_1578_);
v_i_boxed_1584_ = lean_unbox_usize(v_i_1580_);
lean_dec(v_i_1580_);
v_stop_boxed_1585_ = lean_unbox_usize(v_stop_1581_);
lean_dec(v_stop_1581_);
v_res_1586_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1661__boxed_1583_, v_as_1579_, v_i_boxed_1584_, v_stop_boxed_1585_, v_b_1582_);
lean_dec_ref(v_as_1579_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(lean_object* v_ev_1587_, size_t v_sz_1588_, size_t v_i_1589_, lean_object* v_bs_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v___x_1598_; 
v___x_1598_ = lean_usize_dec_lt(v_i_1589_, v_sz_1588_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
lean_dec_ref(v_ev_1587_);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_bs_1590_);
return v___x_1599_;
}
else
{
lean_object* v_v_1600_; lean_object* v___x_1601_; 
v_v_1600_ = lean_array_uget_borrowed(v_bs_1590_, v_i_1589_);
lean_inc_ref(v_ev_1587_);
lean_inc(v___y_1596_);
lean_inc_ref(v___y_1595_);
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v_v_1600_);
v___x_1601_ = lean_apply_8(v_ev_1587_, v_v_1600_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, lean_box(0));
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v_bs_x27_1604_; size_t v___x_1605_; size_t v___x_1606_; lean_object* v___x_1607_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = lean_unsigned_to_nat(0u);
v_bs_x27_1604_ = lean_array_uset(v_bs_1590_, v_i_1589_, v___x_1603_);
v___x_1605_ = ((size_t)1ULL);
v___x_1606_ = lean_usize_add(v_i_1589_, v___x_1605_);
v___x_1607_ = lean_array_uset(v_bs_x27_1604_, v_i_1589_, v_a_1602_);
v_i_1589_ = v___x_1606_;
v_bs_1590_ = v___x_1607_;
goto _start;
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec_ref(v_bs_1590_);
lean_dec_ref(v_ev_1587_);
v_a_1609_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1601_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1601_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg___boxed(lean_object* v_ev_1617_, lean_object* v_sz_1618_, lean_object* v_i_1619_, lean_object* v_bs_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
size_t v_sz_boxed_1628_; size_t v_i_boxed_1629_; lean_object* v_res_1630_; 
v_sz_boxed_1628_ = lean_unbox_usize(v_sz_1618_);
lean_dec(v_sz_1618_);
v_i_boxed_1629_ = lean_unbox_usize(v_i_1619_);
lean_dec(v_i_1619_);
v_res_1630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1617_, v_sz_boxed_1628_, v_i_boxed_1629_, v_bs_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
return v_res_1630_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1636_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2));
v___x_1638_ = l_Lean_Expr_const___override(v___x_1637_, v___x_1636_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(lean_object* v_typeExpr_1639_, lean_object* v_as_1640_, size_t v_i_1641_, size_t v_stop_1642_, lean_object* v_b_1643_){
_start:
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_usize_dec_eq(v_i_1641_, v_stop_1642_);
if (v___x_1644_ == 0)
{
size_t v___x_1645_; size_t v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1645_ = ((size_t)1ULL);
v___x_1646_ = lean_usize_sub(v_i_1641_, v___x_1645_);
v___x_1647_ = lean_array_uget_borrowed(v_as_1640_, v___x_1646_);
v___x_1648_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3);
lean_inc(v___x_1647_);
lean_inc_ref(v_typeExpr_1639_);
v___x_1649_ = l_Lean_mkApp3(v___x_1648_, v_typeExpr_1639_, v___x_1647_, v_b_1643_);
v_i_1641_ = v___x_1646_;
v_b_1643_ = v___x_1649_;
goto _start;
}
else
{
lean_dec_ref(v_typeExpr_1639_);
return v_b_1643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___boxed(lean_object* v_typeExpr_1651_, lean_object* v_as_1652_, lean_object* v_i_1653_, lean_object* v_stop_1654_, lean_object* v_b_1655_){
_start:
{
size_t v_i_boxed_1656_; size_t v_stop_boxed_1657_; lean_object* v_res_1658_; 
v_i_boxed_1656_ = lean_unbox_usize(v_i_1653_);
lean_dec(v_i_1653_);
v_stop_boxed_1657_ = lean_unbox_usize(v_stop_1654_);
lean_dec(v_stop_1654_);
v_res_1658_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(v_typeExpr_1651_, v_as_1652_, v_i_boxed_1656_, v_stop_boxed_1657_, v_b_1655_);
lean_dec_ref(v_as_1652_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(size_t v_sz_1659_, size_t v_i_1660_, lean_object* v_bs_1661_){
_start:
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_usize_dec_lt(v_i_1660_, v_sz_1659_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_bs_1661_);
return v___x_1663_;
}
else
{
lean_object* v_v_1664_; lean_object* v___x_1665_; lean_object* v_bs_x27_1666_; size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v_v_1664_ = lean_array_uget(v_bs_1661_, v_i_1660_);
v___x_1665_ = lean_unsigned_to_nat(0u);
v_bs_x27_1666_ = lean_array_uset(v_bs_1661_, v_i_1660_, v___x_1665_);
v___x_1667_ = ((size_t)1ULL);
v___x_1668_ = lean_usize_add(v_i_1660_, v___x_1667_);
v___x_1669_ = lean_array_uset(v_bs_x27_1666_, v_i_1660_, v_v_1664_);
v_i_1660_ = v___x_1668_;
v_bs_1661_ = v___x_1669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0___boxed(lean_object* v_sz_1671_, lean_object* v_i_1672_, lean_object* v_bs_1673_){
_start:
{
size_t v_sz_boxed_1674_; size_t v_i_boxed_1675_; lean_object* v_res_1676_; 
v_sz_boxed_1674_ = lean_unbox_usize(v_sz_1671_);
lean_dec(v_sz_1671_);
v_i_boxed_1675_ = lean_unbox_usize(v_i_1672_);
lean_dec(v_i_1672_);
v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_boxed_1674_, v_i_boxed_1675_, v_bs_1673_);
return v_res_1676_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1680_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0));
v___x_1681_ = l_Lean_Expr_const___override(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1690_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5));
v___x_1691_ = l_Lean_Expr_const___override(v___x_1690_, v___x_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(lean_object* v_typeExpr_1694_, lean_object* v_ev_1695_, lean_object* v_stx_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_fileName_1704_; lean_object* v_fileMap_1705_; lean_object* v_options_1706_; lean_object* v_currRecDepth_1707_; lean_object* v_maxRecDepth_1708_; lean_object* v_ref_1709_; lean_object* v_currNamespace_1710_; lean_object* v_openDecls_1711_; lean_object* v_initHeartbeats_1712_; lean_object* v_maxHeartbeats_1713_; lean_object* v_quotContext_1714_; lean_object* v_currMacroScope_1715_; uint8_t v_diag_1716_; lean_object* v_cancelTk_x3f_1717_; uint8_t v_suppressElabErrors_1718_; lean_object* v_inheritedTraceOptions_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v_a_1725_; lean_object* v_snd_1726_; lean_object* v___y_1752_; lean_object* v___y_1753_; lean_object* v___y_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_fileName_1704_ = lean_ctor_get(v_a_1701_, 0);
v_fileMap_1705_ = lean_ctor_get(v_a_1701_, 1);
v_options_1706_ = lean_ctor_get(v_a_1701_, 2);
v_currRecDepth_1707_ = lean_ctor_get(v_a_1701_, 3);
v_maxRecDepth_1708_ = lean_ctor_get(v_a_1701_, 4);
v_ref_1709_ = lean_ctor_get(v_a_1701_, 5);
v_currNamespace_1710_ = lean_ctor_get(v_a_1701_, 6);
v_openDecls_1711_ = lean_ctor_get(v_a_1701_, 7);
v_initHeartbeats_1712_ = lean_ctor_get(v_a_1701_, 8);
v_maxHeartbeats_1713_ = lean_ctor_get(v_a_1701_, 9);
v_quotContext_1714_ = lean_ctor_get(v_a_1701_, 10);
v_currMacroScope_1715_ = lean_ctor_get(v_a_1701_, 11);
v_diag_1716_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*14);
v_cancelTk_x3f_1717_ = lean_ctor_get(v_a_1701_, 12);
v_suppressElabErrors_1718_ = lean_ctor_get_uint8(v_a_1701_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1719_ = lean_ctor_get(v_a_1701_, 13);
v___x_1720_ = lean_unsigned_to_nat(0u);
v___x_1721_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
lean_inc_ref(v_typeExpr_1694_);
v___x_1722_ = l_Lean_Expr_app___override(v___x_1721_, v_typeExpr_1694_);
v___x_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_inc(v_stx_1696_);
v___x_1758_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1696_);
v___x_1759_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3));
lean_inc(v___x_1758_);
v___x_1760_ = l_Lean_Syntax_isOfKind(v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec(v___x_1758_);
lean_dec_ref_known(v___x_1723_, 1);
lean_dec(v_stx_1696_);
lean_dec_ref(v_ev_1695_);
lean_dec_ref(v_typeExpr_1694_);
v___x_1761_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1757_ = v___x_1761_;
goto v___jp_1756_;
}
else
{
lean_object* v_ref_1762_; lean_object* v___x_1763_; lean_object* v___y_1765_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_ref_1762_ = l_Lean_replaceRef(v_stx_1696_, v_ref_1709_);
lean_inc_ref(v_inheritedTraceOptions_1719_);
lean_inc(v_cancelTk_x3f_1717_);
lean_inc(v_currMacroScope_1715_);
lean_inc(v_quotContext_1714_);
lean_inc(v_maxHeartbeats_1713_);
lean_inc(v_initHeartbeats_1712_);
lean_inc(v_openDecls_1711_);
lean_inc(v_currNamespace_1710_);
lean_inc(v_maxRecDepth_1708_);
lean_inc(v_currRecDepth_1707_);
lean_inc_ref(v_options_1706_);
lean_inc_ref(v_fileMap_1705_);
lean_inc_ref(v_fileName_1704_);
v___x_1763_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1763_, 0, v_fileName_1704_);
lean_ctor_set(v___x_1763_, 1, v_fileMap_1705_);
lean_ctor_set(v___x_1763_, 2, v_options_1706_);
lean_ctor_set(v___x_1763_, 3, v_currRecDepth_1707_);
lean_ctor_set(v___x_1763_, 4, v_maxRecDepth_1708_);
lean_ctor_set(v___x_1763_, 5, v_ref_1762_);
lean_ctor_set(v___x_1763_, 6, v_currNamespace_1710_);
lean_ctor_set(v___x_1763_, 7, v_openDecls_1711_);
lean_ctor_set(v___x_1763_, 8, v_initHeartbeats_1712_);
lean_ctor_set(v___x_1763_, 9, v_maxHeartbeats_1713_);
lean_ctor_set(v___x_1763_, 10, v_quotContext_1714_);
lean_ctor_set(v___x_1763_, 11, v_currMacroScope_1715_);
lean_ctor_set(v___x_1763_, 12, v_cancelTk_x3f_1717_);
lean_ctor_set(v___x_1763_, 13, v_inheritedTraceOptions_1719_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*14, v_diag_1716_);
lean_ctor_set_uint8(v___x_1763_, sizeof(void*)*14 + 1, v_suppressElabErrors_1718_);
v___x_1791_ = lean_unsigned_to_nat(1u);
v___x_1792_ = l_Lean_Syntax_getArg(v___x_1758_, v___x_1791_);
lean_dec(v___x_1758_);
v___x_1793_ = l_Lean_Syntax_getArgs(v___x_1792_);
lean_dec(v___x_1792_);
v___x_1794_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7));
v___x_1795_ = lean_array_get_size(v___x_1793_);
v___x_1796_ = lean_nat_dec_lt(v___x_1720_, v___x_1795_);
if (v___x_1796_ == 0)
{
lean_dec_ref(v___x_1793_);
v___y_1765_ = v___x_1794_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1797_ = lean_box(v___x_1760_);
v___x_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
lean_ctor_set(v___x_1798_, 1, v___x_1794_);
v___x_1799_ = lean_nat_dec_le(v___x_1795_, v___x_1795_);
if (v___x_1799_ == 0)
{
if (v___x_1796_ == 0)
{
lean_dec_ref_known(v___x_1798_, 2);
lean_dec_ref(v___x_1793_);
v___y_1765_ = v___x_1794_;
goto v___jp_1764_;
}
else
{
size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; lean_object* v_snd_1803_; 
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = lean_usize_of_nat(v___x_1795_);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1760_, v___x_1793_, v___x_1800_, v___x_1801_, v___x_1798_);
lean_dec_ref(v___x_1793_);
v_snd_1803_ = lean_ctor_get(v___x_1802_, 1);
lean_inc(v_snd_1803_);
lean_dec_ref(v___x_1802_);
v___y_1765_ = v_snd_1803_;
goto v___jp_1764_;
}
}
else
{
size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; lean_object* v_snd_1807_; 
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = lean_usize_of_nat(v___x_1795_);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1760_, v___x_1793_, v___x_1804_, v___x_1805_, v___x_1798_);
lean_dec_ref(v___x_1793_);
v_snd_1807_ = lean_ctor_get(v___x_1806_, 1);
lean_inc(v_snd_1807_);
lean_dec_ref(v___x_1806_);
v___y_1765_ = v_snd_1807_;
goto v___jp_1764_;
}
}
v___jp_1764_:
{
size_t v_sz_1766_; size_t v___x_1767_; lean_object* v___x_1768_; 
v_sz_1766_ = lean_array_size(v___y_1765_);
v___x_1767_ = ((size_t)0ULL);
v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_1766_, v___x_1767_, v___y_1765_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v___x_1769_; 
lean_dec_ref_known(v___x_1763_, 14);
lean_dec_ref_known(v___x_1723_, 1);
lean_dec(v_stx_1696_);
lean_dec_ref(v_ev_1695_);
lean_dec_ref(v_typeExpr_1694_);
v___x_1769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1757_ = v___x_1769_;
goto v___jp_1756_;
}
else
{
lean_object* v_val_1770_; size_t v_sz_1771_; lean_object* v___x_1772_; 
v_val_1770_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_val_1770_);
lean_dec_ref_known(v___x_1768_, 1);
v_sz_1771_ = lean_array_size(v_val_1770_);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1695_, v_sz_1771_, v___x_1767_, v_val_1770_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v___x_1763_, v_a_1702_);
lean_dec_ref_known(v___x_1763_, 14);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; lean_object* v_fst_1775_; lean_object* v_snd_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Array_unzip___redArg(v_a_1773_);
lean_dec(v_a_1773_);
v_fst_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_fst_1775_);
v_snd_1776_ = lean_ctor_get(v___x_1774_, 1);
lean_inc(v_snd_1776_);
lean_dec_ref(v___x_1774_);
v___x_1777_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6);
lean_inc_ref(v_typeExpr_1694_);
v___x_1778_ = l_Lean_Expr_app___override(v___x_1777_, v_typeExpr_1694_);
v___x_1779_ = lean_array_get_size(v_snd_1776_);
v___x_1780_ = lean_nat_dec_lt(v___x_1720_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec(v_snd_1776_);
lean_dec_ref(v_typeExpr_1694_);
v___y_1752_ = v_fst_1775_;
v___y_1753_ = v___x_1778_;
goto v___jp_1751_;
}
else
{
size_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_usize_of_nat(v___x_1779_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(v_typeExpr_1694_, v_snd_1776_, v___x_1781_, v___x_1767_, v___x_1778_);
lean_dec(v_snd_1776_);
v___y_1752_ = v_fst_1775_;
v___y_1753_ = v___x_1782_;
goto v___jp_1751_;
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec_ref_known(v___x_1723_, 1);
lean_dec(v_stx_1696_);
lean_dec_ref(v_typeExpr_1694_);
v_a_1783_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1772_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1772_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
}
v___jp_1724_:
{
lean_object* v___x_1727_; lean_object* v_infoState_1728_; uint8_t v_enabled_1729_; 
v___x_1727_ = lean_st_ref_get(v_a_1702_);
v_infoState_1728_ = lean_ctor_get(v___x_1727_, 7);
lean_inc_ref(v_infoState_1728_);
lean_dec(v___x_1727_);
v_enabled_1729_ = lean_ctor_get_uint8(v_infoState_1728_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1728_);
if (v_enabled_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v_snd_1726_);
lean_dec_ref_known(v___x_1723_, 1);
lean_dec(v_stx_1696_);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_a_1725_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1731_ = lean_box(0);
v___x_1732_ = lean_box(0);
v___x_1733_ = 0;
v___x_1734_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1696_, v_snd_1726_, v___x_1723_, v___x_1731_, v___x_1732_, v___x_1733_, v___x_1733_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1734_, 0);
lean_dec(v_unused_1742_);
v___x_1736_ = v___x_1734_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_dec(v___x_1734_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v_a_1725_);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1725_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_a_1725_);
v_a_1743_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1734_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1734_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
v___jp_1751_:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_array_to_list(v___y_1752_);
lean_inc_ref(v___y_1753_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v___y_1753_);
v_a_1725_ = v___x_1755_;
v_snd_1726_ = v___y_1753_;
goto v___jp_1724_;
}
v___jp_1756_:
{
return v___y_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___boxed(lean_object* v_typeExpr_1808_, lean_object* v_ev_1809_, lean_object* v_stx_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v_typeExpr_1808_, v_ev_1809_, v_stx_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(lean_object* v_00_u03b1_1819_, lean_object* v_typeExpr_1820_, lean_object* v_ev_1821_, lean_object* v_stx_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(v_typeExpr_1820_, v_ev_1821_, v_stx_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed(lean_object* v_00_u03b1_1831_, lean_object* v_typeExpr_1832_, lean_object* v_ev_1833_, lean_object* v_stx_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(v_00_u03b1_1831_, v_typeExpr_1832_, v_ev_1833_, v_stx_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(lean_object* v_00_u03b1_1843_, lean_object* v_ev_1844_, size_t v_sz_1845_, size_t v_i_1846_, lean_object* v_bs_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1844_, v_sz_1845_, v_i_1846_, v_bs_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___boxed(lean_object* v_00_u03b1_1856_, lean_object* v_ev_1857_, lean_object* v_sz_1858_, lean_object* v_i_1859_, lean_object* v_bs_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
size_t v_sz_boxed_1868_; size_t v_i_boxed_1869_; lean_object* v_res_1870_; 
v_sz_boxed_1868_ = lean_unbox_usize(v_sz_1858_);
lean_dec(v_sz_1858_);
v_i_boxed_1869_ = lean_unbox_usize(v_i_1859_);
lean_dec(v_i_1859_);
v_res_1870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(v_00_u03b1_1856_, v_ev_1857_, v_sz_boxed_1868_, v_i_boxed_1869_, v_bs_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(lean_object* v_typeExpr_1871_, lean_object* v_as_1872_, size_t v_i_1873_, size_t v_stop_1874_, lean_object* v_b_1875_){
_start:
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_usize_dec_eq(v_i_1873_, v_stop_1874_);
if (v___x_1876_ == 0)
{
size_t v___x_1877_; size_t v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1877_ = ((size_t)1ULL);
v___x_1878_ = lean_usize_sub(v_i_1873_, v___x_1877_);
v___x_1879_ = lean_array_uget_borrowed(v_as_1872_, v___x_1878_);
v___x_1880_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3);
lean_inc(v___x_1879_);
lean_inc_ref(v_typeExpr_1871_);
v___x_1881_ = l_Lean_mkApp3(v___x_1880_, v_typeExpr_1871_, v___x_1879_, v_b_1875_);
v_i_1873_ = v___x_1878_;
v_b_1875_ = v___x_1881_;
goto _start;
}
else
{
lean_dec_ref(v_typeExpr_1871_);
return v_b_1875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0___boxed(lean_object* v_typeExpr_1883_, lean_object* v_as_1884_, lean_object* v_i_1885_, lean_object* v_stop_1886_, lean_object* v_b_1887_){
_start:
{
size_t v_i_boxed_1888_; size_t v_stop_boxed_1889_; lean_object* v_res_1890_; 
v_i_boxed_1888_ = lean_unbox_usize(v_i_1885_);
lean_dec(v_i_1885_);
v_stop_boxed_1889_ = lean_unbox_usize(v_stop_1886_);
lean_dec(v_stop_1886_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(v_typeExpr_1883_, v_as_1884_, v_i_boxed_1888_, v_stop_boxed_1889_, v_b_1887_);
lean_dec_ref(v_as_1884_);
return v_res_1890_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1895_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1));
v___x_1896_ = l_Lean_Expr_const___override(v___x_1895_, v___x_1894_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(lean_object* v_typeExpr_1901_, lean_object* v_ev_1902_, lean_object* v_stx_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_fileName_1911_; lean_object* v_fileMap_1912_; lean_object* v_options_1913_; lean_object* v_currRecDepth_1914_; lean_object* v_maxRecDepth_1915_; lean_object* v_ref_1916_; lean_object* v_currNamespace_1917_; lean_object* v_openDecls_1918_; lean_object* v_initHeartbeats_1919_; lean_object* v_maxHeartbeats_1920_; lean_object* v_quotContext_1921_; lean_object* v_currMacroScope_1922_; uint8_t v_diag_1923_; lean_object* v_cancelTk_x3f_1924_; uint8_t v_suppressElabErrors_1925_; lean_object* v_inheritedTraceOptions_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v_a_1933_; lean_object* v_snd_1934_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_fileName_1911_ = lean_ctor_get(v_a_1908_, 0);
v_fileMap_1912_ = lean_ctor_get(v_a_1908_, 1);
v_options_1913_ = lean_ctor_get(v_a_1908_, 2);
v_currRecDepth_1914_ = lean_ctor_get(v_a_1908_, 3);
v_maxRecDepth_1915_ = lean_ctor_get(v_a_1908_, 4);
v_ref_1916_ = lean_ctor_get(v_a_1908_, 5);
v_currNamespace_1917_ = lean_ctor_get(v_a_1908_, 6);
v_openDecls_1918_ = lean_ctor_get(v_a_1908_, 7);
v_initHeartbeats_1919_ = lean_ctor_get(v_a_1908_, 8);
v_maxHeartbeats_1920_ = lean_ctor_get(v_a_1908_, 9);
v_quotContext_1921_ = lean_ctor_get(v_a_1908_, 10);
v_currMacroScope_1922_ = lean_ctor_get(v_a_1908_, 11);
v_diag_1923_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*14);
v_cancelTk_x3f_1924_ = lean_ctor_get(v_a_1908_, 12);
v_suppressElabErrors_1925_ = lean_ctor_get_uint8(v_a_1908_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1926_ = lean_ctor_get(v_a_1908_, 13);
v___x_1927_ = lean_unsigned_to_nat(0u);
v___x_1928_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_1929_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
lean_inc_ref(v_typeExpr_1901_);
v___x_1930_ = l_Lean_Expr_app___override(v___x_1929_, v_typeExpr_1901_);
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_inc(v_stx_1903_);
v___x_1970_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_1903_);
v___x_1971_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5));
lean_inc(v___x_1970_);
v___x_1972_ = l_Lean_Syntax_isOfKind(v___x_1970_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_dec(v___x_1970_);
lean_dec_ref_known(v___x_1931_, 1);
lean_dec(v_stx_1903_);
lean_dec_ref(v_ev_1902_);
lean_dec_ref(v_typeExpr_1901_);
v___x_1973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1969_ = v___x_1973_;
goto v___jp_1968_;
}
else
{
lean_object* v_ref_1974_; lean_object* v___x_1975_; lean_object* v___y_1977_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_ref_1974_ = l_Lean_replaceRef(v_stx_1903_, v_ref_1916_);
lean_inc_ref(v_inheritedTraceOptions_1926_);
lean_inc(v_cancelTk_x3f_1924_);
lean_inc(v_currMacroScope_1922_);
lean_inc(v_quotContext_1921_);
lean_inc(v_maxHeartbeats_1920_);
lean_inc(v_initHeartbeats_1919_);
lean_inc(v_openDecls_1918_);
lean_inc(v_currNamespace_1917_);
lean_inc(v_maxRecDepth_1915_);
lean_inc(v_currRecDepth_1914_);
lean_inc_ref(v_options_1913_);
lean_inc_ref(v_fileMap_1912_);
lean_inc_ref(v_fileName_1911_);
v___x_1975_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1975_, 0, v_fileName_1911_);
lean_ctor_set(v___x_1975_, 1, v_fileMap_1912_);
lean_ctor_set(v___x_1975_, 2, v_options_1913_);
lean_ctor_set(v___x_1975_, 3, v_currRecDepth_1914_);
lean_ctor_set(v___x_1975_, 4, v_maxRecDepth_1915_);
lean_ctor_set(v___x_1975_, 5, v_ref_1974_);
lean_ctor_set(v___x_1975_, 6, v_currNamespace_1917_);
lean_ctor_set(v___x_1975_, 7, v_openDecls_1918_);
lean_ctor_set(v___x_1975_, 8, v_initHeartbeats_1919_);
lean_ctor_set(v___x_1975_, 9, v_maxHeartbeats_1920_);
lean_ctor_set(v___x_1975_, 10, v_quotContext_1921_);
lean_ctor_set(v___x_1975_, 11, v_currMacroScope_1922_);
lean_ctor_set(v___x_1975_, 12, v_cancelTk_x3f_1924_);
lean_ctor_set(v___x_1975_, 13, v_inheritedTraceOptions_1926_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*14, v_diag_1923_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*14 + 1, v_suppressElabErrors_1925_);
v___x_2004_ = lean_unsigned_to_nat(1u);
v___x_2005_ = l_Lean_Syntax_getArg(v___x_1970_, v___x_2004_);
lean_dec(v___x_1970_);
v___x_2006_ = l_Lean_Syntax_getArgs(v___x_2005_);
lean_dec(v___x_2005_);
v___x_2007_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7));
v___x_2008_ = lean_array_get_size(v___x_2006_);
v___x_2009_ = lean_nat_dec_lt(v___x_1927_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v___x_2006_);
v___y_1977_ = v___x_2007_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2010_ = lean_box(v___x_1972_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v___x_2007_);
v___x_2012_ = lean_nat_dec_le(v___x_2008_, v___x_2008_);
if (v___x_2012_ == 0)
{
if (v___x_2009_ == 0)
{
lean_dec_ref_known(v___x_2011_, 2);
lean_dec_ref(v___x_2006_);
v___y_1977_ = v___x_2007_;
goto v___jp_1976_;
}
else
{
size_t v___x_2013_; size_t v___x_2014_; lean_object* v___x_2015_; lean_object* v_snd_2016_; 
v___x_2013_ = ((size_t)0ULL);
v___x_2014_ = lean_usize_of_nat(v___x_2008_);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1972_, v___x_2006_, v___x_2013_, v___x_2014_, v___x_2011_);
lean_dec_ref(v___x_2006_);
v_snd_2016_ = lean_ctor_get(v___x_2015_, 1);
lean_inc(v_snd_2016_);
lean_dec_ref(v___x_2015_);
v___y_1977_ = v_snd_2016_;
goto v___jp_1976_;
}
}
else
{
size_t v___x_2017_; size_t v___x_2018_; lean_object* v___x_2019_; lean_object* v_snd_2020_; 
v___x_2017_ = ((size_t)0ULL);
v___x_2018_ = lean_usize_of_nat(v___x_2008_);
v___x_2019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1972_, v___x_2006_, v___x_2017_, v___x_2018_, v___x_2011_);
lean_dec_ref(v___x_2006_);
v_snd_2020_ = lean_ctor_get(v___x_2019_, 1);
lean_inc(v_snd_2020_);
lean_dec_ref(v___x_2019_);
v___y_1977_ = v_snd_2020_;
goto v___jp_1976_;
}
}
v___jp_1976_:
{
size_t v_sz_1978_; size_t v___x_1979_; lean_object* v___x_1980_; 
v_sz_1978_ = lean_array_size(v___y_1977_);
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_1978_, v___x_1979_, v___y_1977_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v___x_1981_; 
lean_dec_ref_known(v___x_1975_, 14);
lean_dec_ref_known(v___x_1931_, 1);
lean_dec(v_stx_1903_);
lean_dec_ref(v_ev_1902_);
lean_dec_ref(v_typeExpr_1901_);
v___x_1981_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_1969_ = v___x_1981_;
goto v___jp_1968_;
}
else
{
lean_object* v_val_1982_; size_t v_sz_1983_; lean_object* v___x_1984_; 
v_val_1982_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v___x_1980_, 1);
v_sz_1983_ = lean_array_size(v_val_1982_);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_1902_, v_sz_1983_, v___x_1979_, v_val_1982_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v___x_1975_, v_a_1909_);
lean_dec_ref_known(v___x_1975_, 14);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l_Array_unzip___redArg(v_a_1985_);
lean_dec(v_a_1985_);
v_fst_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_fst_1987_);
v_snd_1988_ = lean_ctor_get(v___x_1986_, 1);
lean_inc(v_snd_1988_);
lean_dec_ref(v___x_1986_);
v___x_1989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0));
v___x_1990_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6);
lean_inc_ref(v_typeExpr_1901_);
v___x_1991_ = l_Lean_Expr_app___override(v___x_1990_, v_typeExpr_1901_);
v___x_1992_ = lean_array_get_size(v_snd_1988_);
v___x_1993_ = lean_nat_dec_lt(v___x_1927_, v___x_1992_);
if (v___x_1993_ == 0)
{
lean_dec(v_snd_1988_);
v___y_1960_ = v___x_1989_;
v___y_1961_ = v_fst_1987_;
v___y_1962_ = v___x_1991_;
goto v___jp_1959_;
}
else
{
size_t v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_usize_of_nat(v___x_1992_);
lean_inc_ref(v_typeExpr_1901_);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(v_typeExpr_1901_, v_snd_1988_, v___x_1994_, v___x_1979_, v___x_1991_);
lean_dec(v_snd_1988_);
v___y_1960_ = v___x_1989_;
v___y_1961_ = v_fst_1987_;
v___y_1962_ = v___x_1995_;
goto v___jp_1959_;
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec_ref_known(v___x_1931_, 1);
lean_dec(v_stx_1903_);
lean_dec_ref(v_typeExpr_1901_);
v_a_1996_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1984_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1984_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
v___jp_1932_:
{
lean_object* v___x_1935_; lean_object* v_infoState_1936_; uint8_t v_enabled_1937_; 
v___x_1935_ = lean_st_ref_get(v_a_1909_);
v_infoState_1936_ = lean_ctor_get(v___x_1935_, 7);
lean_inc_ref(v_infoState_1936_);
lean_dec(v___x_1935_);
v_enabled_1937_ = lean_ctor_get_uint8(v_infoState_1936_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1936_);
if (v_enabled_1937_ == 0)
{
lean_object* v___x_1938_; 
lean_dec_ref(v_snd_1934_);
lean_dec_ref_known(v___x_1931_, 1);
lean_dec(v_stx_1903_);
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_a_1933_);
return v___x_1938_;
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_box(0);
v___x_1941_ = 0;
v___x_1942_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_1903_, v_snd_1934_, v___x_1931_, v___x_1939_, v___x_1940_, v___x_1941_, v___x_1941_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1949_ == 0)
{
lean_object* v_unused_1950_; 
v_unused_1950_ = lean_ctor_get(v___x_1942_, 0);
lean_dec(v_unused_1950_);
v___x_1944_ = v___x_1942_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_dec(v___x_1942_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v_a_1933_);
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1933_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_a_1933_);
v_a_1951_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1942_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1942_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
v___jp_1959_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1963_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3));
lean_inc_ref(v___y_1960_);
v___x_1964_ = l_Lean_Name_mkStr2(v___y_1960_, v___x_1963_);
v___x_1965_ = l_Lean_Expr_const___override(v___x_1964_, v___x_1928_);
v___x_1966_ = l_Lean_mkAppB(v___x_1965_, v_typeExpr_1901_, v___y_1962_);
lean_inc_ref(v___x_1966_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___y_1961_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v_a_1933_ = v___x_1967_;
v_snd_1934_ = v___x_1966_;
goto v___jp_1932_;
}
v___jp_1968_:
{
return v___y_1969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___boxed(lean_object* v_typeExpr_2021_, lean_object* v_ev_2022_, lean_object* v_stx_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(v_typeExpr_2021_, v_ev_2022_, v_stx_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(lean_object* v_00_u03b1_2032_, lean_object* v_typeExpr_2033_, lean_object* v_ev_2034_, lean_object* v_stx_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(v_typeExpr_2033_, v_ev_2034_, v_stx_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed(lean_object* v_00_u03b1_2044_, lean_object* v_typeExpr_2045_, lean_object* v_ev_2046_, lean_object* v_stx_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(v_00_u03b1_2044_, v_typeExpr_2045_, v_ev_2046_, v_stx_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2055_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9);
v___x_2060_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8);
v___x_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___x_2059_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2);
v___x_2063_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1));
v___x_2064_ = l_Lean_Expr_const___override(v___x_2063_, v___x_2062_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2);
v___x_2085_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11));
v___x_2086_ = l_Lean_Expr_const___override(v___x_2085_, v___x_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(lean_object* v_typeExpr_2087_, lean_object* v_typeExpr_x27_2088_, lean_object* v_ev_2089_, lean_object* v_ev_x27_2090_, lean_object* v_stx_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_fileName_2099_; lean_object* v_fileMap_2100_; lean_object* v_options_2101_; lean_object* v_currRecDepth_2102_; lean_object* v_maxRecDepth_2103_; lean_object* v_ref_2104_; lean_object* v_currNamespace_2105_; lean_object* v_openDecls_2106_; lean_object* v_initHeartbeats_2107_; lean_object* v_maxHeartbeats_2108_; lean_object* v_quotContext_2109_; lean_object* v_currMacroScope_2110_; uint8_t v_diag_2111_; lean_object* v_cancelTk_x3f_2112_; uint8_t v_suppressElabErrors_2113_; lean_object* v_inheritedTraceOptions_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_a_2120_; lean_object* v_snd_2121_; lean_object* v___y_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
v_fileName_2099_ = lean_ctor_get(v_a_2096_, 0);
v_fileMap_2100_ = lean_ctor_get(v_a_2096_, 1);
v_options_2101_ = lean_ctor_get(v_a_2096_, 2);
v_currRecDepth_2102_ = lean_ctor_get(v_a_2096_, 3);
v_maxRecDepth_2103_ = lean_ctor_get(v_a_2096_, 4);
v_ref_2104_ = lean_ctor_get(v_a_2096_, 5);
v_currNamespace_2105_ = lean_ctor_get(v_a_2096_, 6);
v_openDecls_2106_ = lean_ctor_get(v_a_2096_, 7);
v_initHeartbeats_2107_ = lean_ctor_get(v_a_2096_, 8);
v_maxHeartbeats_2108_ = lean_ctor_get(v_a_2096_, 9);
v_quotContext_2109_ = lean_ctor_get(v_a_2096_, 10);
v_currMacroScope_2110_ = lean_ctor_get(v_a_2096_, 11);
v_diag_2111_ = lean_ctor_get_uint8(v_a_2096_, sizeof(void*)*14);
v_cancelTk_x3f_2112_ = lean_ctor_get(v_a_2096_, 12);
v_suppressElabErrors_2113_ = lean_ctor_get_uint8(v_a_2096_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2114_ = lean_ctor_get(v_a_2096_, 13);
v___x_2115_ = lean_unsigned_to_nat(0u);
v___x_2116_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3);
lean_inc_ref(v_typeExpr_x27_2088_);
lean_inc_ref(v_typeExpr_2087_);
v___x_2117_ = l_Lean_mkAppB(v___x_2116_, v_typeExpr_2087_, v_typeExpr_x27_2088_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_inc(v_stx_2091_);
v___x_2148_ = l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(v_stx_2091_);
v___x_2149_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5));
lean_inc(v___x_2148_);
v___x_2150_ = l_Lean_Syntax_isOfKind(v___x_2148_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec(v___x_2148_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
lean_dec_ref(v_ev_x27_2090_);
lean_dec_ref(v_ev_2089_);
lean_dec_ref(v_typeExpr_x27_2088_);
lean_dec_ref(v_typeExpr_2087_);
v___x_2151_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2147_ = v___x_2151_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2152_ = l_Lean_Syntax_getArg(v___x_2148_, v___x_2115_);
v___x_2153_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7));
lean_inc(v___x_2152_);
v___x_2154_ = l_Lean_Syntax_isOfKind(v___x_2152_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
lean_dec(v___x_2152_);
lean_dec(v___x_2148_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
lean_dec_ref(v_ev_x27_2090_);
lean_dec_ref(v_ev_2089_);
lean_dec_ref(v_typeExpr_x27_2088_);
lean_dec_ref(v_typeExpr_2087_);
v___x_2155_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2147_ = v___x_2155_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; uint8_t v___x_2159_; 
v___x_2156_ = lean_unsigned_to_nat(1u);
v___x_2157_ = l_Lean_Syntax_getArg(v___x_2152_, v___x_2156_);
lean_dec(v___x_2152_);
v___x_2158_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9));
lean_inc(v___x_2157_);
v___x_2159_ = l_Lean_Syntax_isOfKind(v___x_2157_, v___x_2158_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; 
lean_dec(v___x_2157_);
lean_dec(v___x_2148_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
lean_dec_ref(v_ev_x27_2090_);
lean_dec_ref(v_ev_2089_);
lean_dec_ref(v_typeExpr_x27_2088_);
lean_dec_ref(v_typeExpr_2087_);
v___x_2160_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2147_ = v___x_2160_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2161_ = l_Lean_Syntax_getArg(v___x_2157_, v___x_2115_);
lean_dec(v___x_2157_);
v___x_2162_ = lean_box(0);
v___x_2163_ = l_Lean_Syntax_matchesIdent(v___x_2161_, v___x_2162_);
lean_dec(v___x_2161_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; 
lean_dec(v___x_2148_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
lean_dec_ref(v_ev_x27_2090_);
lean_dec_ref(v_ev_2089_);
lean_dec_ref(v_typeExpr_x27_2088_);
lean_dec_ref(v_typeExpr_2087_);
v___x_2164_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2147_ = v___x_2164_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = l_Lean_Syntax_getArg(v___x_2148_, v___x_2156_);
lean_dec(v___x_2148_);
v___x_2166_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2165_);
v___x_2167_ = l_Lean_Syntax_matchesNull(v___x_2165_, v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; 
lean_dec(v___x_2165_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
lean_dec_ref(v_ev_x27_2090_);
lean_dec_ref(v_ev_2089_);
lean_dec_ref(v_typeExpr_x27_2088_);
lean_dec_ref(v_typeExpr_2087_);
v___x_2168_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2147_ = v___x_2168_;
goto v___jp_2146_;
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v___x_2169_ = lean_unsigned_to_nat(2u);
v___x_2170_ = l_Lean_Syntax_getArg(v___x_2165_, v___x_2169_);
lean_inc(v___x_2170_);
v___x_2171_ = l_Lean_Syntax_matchesNull(v___x_2170_, v___x_2156_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; 
lean_dec(v___x_2170_);
lean_dec(v___x_2165_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
lean_dec_ref(v_ev_x27_2090_);
lean_dec_ref(v_ev_2089_);
lean_dec_ref(v_typeExpr_x27_2088_);
lean_dec_ref(v_typeExpr_2087_);
v___x_2172_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
v___y_2147_ = v___x_2172_;
goto v___jp_2146_;
}
else
{
lean_object* v_ref_2173_; lean_object* v___x_2174_; lean_object* v_x_2175_; lean_object* v___x_2176_; 
v_ref_2173_ = l_Lean_replaceRef(v_stx_2091_, v_ref_2104_);
lean_inc_ref(v_inheritedTraceOptions_2114_);
lean_inc(v_cancelTk_x3f_2112_);
lean_inc(v_currMacroScope_2110_);
lean_inc(v_quotContext_2109_);
lean_inc(v_maxHeartbeats_2108_);
lean_inc(v_initHeartbeats_2107_);
lean_inc(v_openDecls_2106_);
lean_inc(v_currNamespace_2105_);
lean_inc(v_maxRecDepth_2103_);
lean_inc(v_currRecDepth_2102_);
lean_inc_ref(v_options_2101_);
lean_inc_ref(v_fileMap_2100_);
lean_inc_ref(v_fileName_2099_);
v___x_2174_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2174_, 0, v_fileName_2099_);
lean_ctor_set(v___x_2174_, 1, v_fileMap_2100_);
lean_ctor_set(v___x_2174_, 2, v_options_2101_);
lean_ctor_set(v___x_2174_, 3, v_currRecDepth_2102_);
lean_ctor_set(v___x_2174_, 4, v_maxRecDepth_2103_);
lean_ctor_set(v___x_2174_, 5, v_ref_2173_);
lean_ctor_set(v___x_2174_, 6, v_currNamespace_2105_);
lean_ctor_set(v___x_2174_, 7, v_openDecls_2106_);
lean_ctor_set(v___x_2174_, 8, v_initHeartbeats_2107_);
lean_ctor_set(v___x_2174_, 9, v_maxHeartbeats_2108_);
lean_ctor_set(v___x_2174_, 10, v_quotContext_2109_);
lean_ctor_set(v___x_2174_, 11, v_currMacroScope_2110_);
lean_ctor_set(v___x_2174_, 12, v_cancelTk_x3f_2112_);
lean_ctor_set(v___x_2174_, 13, v_inheritedTraceOptions_2114_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*14, v_diag_2111_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*14 + 1, v_suppressElabErrors_2113_);
v_x_2175_ = l_Lean_Syntax_getArg(v___x_2165_, v___x_2115_);
lean_dec(v___x_2165_);
lean_inc(v_a_2097_);
lean_inc_ref(v___x_2174_);
lean_inc(v_a_2095_);
lean_inc_ref(v_a_2094_);
lean_inc(v_a_2093_);
lean_inc_ref(v_a_2092_);
v___x_2176_ = lean_apply_8(v_ev_2089_, v_x_2175_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v___x_2174_, v_a_2097_, lean_box(0));
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v_fst_2178_; lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2208_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v_fst_2178_ = lean_ctor_get(v_a_2177_, 0);
v_snd_2179_ = lean_ctor_get(v_a_2177_, 1);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_a_2177_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2181_ = v_a_2177_;
v_isShared_2182_ = v_isSharedCheck_2208_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_inc(v_fst_2178_);
lean_dec(v_a_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2208_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_x_x27_2183_; lean_object* v___x_2184_; 
v_x_x27_2183_ = l_Lean_Syntax_getArg(v___x_2170_, v___x_2115_);
lean_dec(v___x_2170_);
lean_inc(v_a_2097_);
lean_inc(v_a_2095_);
lean_inc_ref(v_a_2094_);
lean_inc(v_a_2093_);
lean_inc_ref(v_a_2092_);
v___x_2184_ = lean_apply_8(v_ev_x27_2090_, v_x_x27_2183_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v___x_2174_, v_a_2097_, lean_box(0));
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v_fst_2186_; lean_object* v_snd_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2199_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v_fst_2186_ = lean_ctor_get(v_a_2185_, 0);
v_snd_2187_ = lean_ctor_get(v_a_2185_, 1);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_a_2185_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2189_ = v_a_2185_;
v_isShared_2190_ = v_isSharedCheck_2199_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snd_2187_);
lean_inc(v_fst_2186_);
lean_dec(v_a_2185_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2199_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 1, v_fst_2186_);
lean_ctor_set(v___x_2189_, 0, v_fst_2178_);
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_fst_2178_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_fst_2186_);
v___x_2192_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2193_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12);
v___x_2194_ = l_Lean_mkApp4(v___x_2193_, v_typeExpr_2087_, v_typeExpr_x27_2088_, v_snd_2179_, v_snd_2187_);
lean_inc_ref(v___x_2194_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v___x_2194_);
lean_ctor_set(v___x_2181_, 0, v___x_2192_);
v___x_2196_ = v___x_2181_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
v_a_2120_ = v___x_2196_;
v_snd_2121_ = v___x_2194_;
goto v___jp_2119_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_del_object(v___x_2181_);
lean_dec(v_snd_2179_);
lean_dec(v_fst_2178_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
lean_dec_ref(v_typeExpr_x27_2088_);
lean_dec_ref(v_typeExpr_2087_);
v_a_2200_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2184_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2184_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
lean_dec_ref_known(v___x_2174_, 14);
lean_dec(v___x_2170_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
lean_dec_ref(v_ev_x27_2090_);
lean_dec_ref(v_typeExpr_x27_2088_);
lean_dec_ref(v_typeExpr_2087_);
v_a_2209_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___x_2176_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2176_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
}
}
}
v___jp_2119_:
{
lean_object* v___x_2122_; lean_object* v_infoState_2123_; uint8_t v_enabled_2124_; 
v___x_2122_ = lean_st_ref_get(v_a_2097_);
v_infoState_2123_ = lean_ctor_get(v___x_2122_, 7);
lean_inc_ref(v_infoState_2123_);
lean_dec(v___x_2122_);
v_enabled_2124_ = lean_ctor_get_uint8(v_infoState_2123_, sizeof(void*)*3);
lean_dec_ref(v_infoState_2123_);
if (v_enabled_2124_ == 0)
{
lean_object* v___x_2125_; 
lean_dec_ref(v_snd_2121_);
lean_dec_ref_known(v___x_2118_, 1);
lean_dec(v_stx_2091_);
v___x_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2125_, 0, v_a_2120_);
return v___x_2125_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; 
v___x_2126_ = lean_box(0);
v___x_2127_ = lean_box(0);
v___x_2128_ = 0;
v___x_2129_ = l_Lean_Elab_Term_addTermInfo_x27(v_stx_2091_, v_snd_2121_, v___x_2118_, v___x_2126_, v___x_2127_, v___x_2128_, v___x_2128_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v___x_2129_, 0);
lean_dec(v_unused_2137_);
v___x_2131_ = v___x_2129_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_dec(v___x_2129_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v_a_2120_);
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2120_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_a_2120_);
v_a_2138_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2129_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2129_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
v___jp_2146_:
{
return v___y_2147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___boxed(lean_object* v_typeExpr_2217_, lean_object* v_typeExpr_x27_2218_, lean_object* v_ev_2219_, lean_object* v_ev_x27_2220_, lean_object* v_stx_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(v_typeExpr_2217_, v_typeExpr_x27_2218_, v_ev_2219_, v_ev_x27_2220_, v_stx_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(lean_object* v_00_u03b1_2230_, lean_object* v_00_u03b1_x27_2231_, lean_object* v_typeExpr_2232_, lean_object* v_typeExpr_x27_2233_, lean_object* v_ev_2234_, lean_object* v_ev_x27_2235_, lean_object* v_stx_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(v_typeExpr_2232_, v_typeExpr_x27_2233_, v_ev_2234_, v_ev_x27_2235_, v_stx_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_00_u03b1_x27_2246_, lean_object* v_typeExpr_2247_, lean_object* v_typeExpr_x27_2248_, lean_object* v_ev_2249_, lean_object* v_ev_x27_2250_, lean_object* v_stx_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(v_00_u03b1_2245_, v_00_u03b1_x27_2246_, v_typeExpr_2247_, v_typeExpr_x27_2248_, v_ev_2249_, v_ev_x27_2250_, v_stx_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_object* v_00_u03b1_2260_, lean_object* v_c_2261_, lean_object* v_f_2262_, lean_object* v_x_2263_){
_start:
{
lean_object* v_fst_2264_; lean_object* v_snd_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2276_; 
v_fst_2264_ = lean_ctor_get(v_x_2263_, 0);
v_snd_2265_ = lean_ctor_get(v_x_2263_, 1);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_x_2263_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2267_ = v_x_2263_;
v_isShared_2268_ = v_isSharedCheck_2276_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_snd_2265_);
lean_inc(v_fst_2264_);
lean_dec(v_x_2263_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2276_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2269_ = lean_apply_1(v_f_2262_, v_fst_2264_);
v___x_2270_ = lean_box(0);
v___x_2271_ = l_Lean_Expr_const___override(v_c_2261_, v___x_2270_);
v___x_2272_ = l_Lean_Expr_app___override(v___x_2271_, v_snd_2265_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2272_);
lean_ctor_set(v___x_2267_, 0, v___x_2269_);
v___x_2274_ = v___x_2267_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(uint8_t v_v_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2278_, 0, v_v_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed(lean_object* v_v_2279_){
_start:
{
uint8_t v_v_boxed_2280_; lean_object* v_res_2281_; 
v_v_boxed_2280_ = lean_unbox(v_v_2279_);
v_res_2281_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(v_v_boxed_2280_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2(lean_object* v_v_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2283_, 0, v_v_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3(lean_object* v_v_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_v_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4(lean_object* v_v_2286_){
_start:
{
lean_object* v___x_2287_; 
v___x_2287_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_v_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5(lean_object* v_v_2288_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_v_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(lean_object* v_stx_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v___y_2330_; lean_object* v___y_2331_; uint8_t v___y_2332_; lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_Meta_saveState___redArg(v_a_2325_, v_a_2327_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
lean_inc(v_stx_2321_);
v___x_2345_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(v_stx_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2344_);
lean_dec(v_stx_2321_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2356_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2356_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___f_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___f_2350_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1));
v___x_2351_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3));
v___x_2352_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2351_, v___f_2350_, v_a_2346_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2352_);
v___x_2354_ = v___x_2348_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2544_; 
v_a_2357_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2359_ = v___x_2345_;
v_isShared_2360_ = v_isSharedCheck_2544_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2345_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2544_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___f_2361_; lean_object* v___f_2362_; lean_object* v___f_2363_; lean_object* v___y_2365_; lean_object* v___y_2366_; uint8_t v___y_2367_; lean_object* v___y_2409_; lean_object* v___y_2410_; uint8_t v___y_2411_; lean_object* v___f_2452_; lean_object* v___y_2454_; lean_object* v___y_2455_; uint8_t v___y_2456_; lean_object* v___x_2498_; 
v___f_2361_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4));
v___f_2362_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5));
v___f_2363_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6));
v___f_2452_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11));
lean_inc(v_a_2357_);
if (v_isShared_2360_ == 0)
{
v___x_2498_ = v___x_2359_;
goto v_reusejp_2497_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2357_);
v___x_2498_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2497_;
}
v___jp_2364_:
{
if (v___y_2367_ == 0)
{
lean_object* v___x_2368_; 
lean_dec_ref(v___y_2366_);
v___x_2368_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2365_, v_a_2325_, v_a_2327_);
lean_dec_ref(v___y_2365_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v___x_2369_; 
lean_dec_ref_known(v___x_2368_, 1);
v___x_2369_ = l_Lean_Meta_saveState___redArg(v_a_2325_, v_a_2327_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
v___x_2371_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(v_stx_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_a_2370_);
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2381_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2381_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2379_; 
v___x_2376_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8));
v___x_2377_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2376_, v___f_2363_, v_a_2372_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2377_);
v___x_2379_ = v___x_2374_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2391_; 
v_a_2382_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2384_ = v___x_2371_;
v_isShared_2385_ = v_isSharedCheck_2391_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2371_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2391_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
lean_inc(v_a_2382_);
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
uint8_t v___x_2388_; 
v___x_2388_ = l_Lean_Exception_isInterrupt(v_a_2382_);
if (v___x_2388_ == 0)
{
uint8_t v___x_2389_; 
v___x_2389_ = l_Lean_Exception_isRuntime(v_a_2382_);
v___y_2330_ = v___x_2387_;
v___y_2331_ = v_a_2370_;
v___y_2332_ = v___x_2389_;
goto v___jp_2329_;
}
else
{
lean_dec(v_a_2382_);
v___y_2330_ = v___x_2387_;
v___y_2331_ = v_a_2370_;
v___y_2332_ = v___x_2388_;
goto v___jp_2329_;
}
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_stx_2321_);
v_a_2392_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2369_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2369_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_stx_2321_);
v_a_2400_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2368_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2368_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
else
{
lean_dec_ref(v___y_2365_);
lean_dec(v_stx_2321_);
return v___y_2366_;
}
}
v___jp_2408_:
{
if (v___y_2411_ == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref(v___y_2409_);
v___x_2412_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2410_, v_a_2325_, v_a_2327_);
lean_dec_ref(v___y_2410_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; 
lean_dec_ref_known(v___x_2412_, 1);
v___x_2413_ = l_Lean_Meta_saveState___redArg(v_a_2325_, v_a_2327_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
lean_inc(v_stx_2321_);
v___x_2415_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(v_stx_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2425_; 
lean_dec(v_a_2414_);
lean_dec(v_stx_2321_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2425_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2425_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2420_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10));
v___x_2421_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2420_, v___f_2362_, v_a_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2421_);
v___x_2423_ = v___x_2418_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2435_; 
v_a_2426_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2428_ = v___x_2415_;
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2415_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
lean_inc(v_a_2426_);
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
uint8_t v___x_2432_; 
v___x_2432_ = l_Lean_Exception_isInterrupt(v_a_2426_);
if (v___x_2432_ == 0)
{
uint8_t v___x_2433_; 
v___x_2433_ = l_Lean_Exception_isRuntime(v_a_2426_);
v___y_2365_ = v_a_2414_;
v___y_2366_ = v___x_2431_;
v___y_2367_ = v___x_2433_;
goto v___jp_2364_;
}
else
{
lean_dec(v_a_2426_);
v___y_2365_ = v_a_2414_;
v___y_2366_ = v___x_2431_;
v___y_2367_ = v___x_2432_;
goto v___jp_2364_;
}
}
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v_stx_2321_);
v_a_2436_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2413_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2413_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_stx_2321_);
v_a_2444_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2412_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2412_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_dec_ref(v___y_2410_);
lean_dec(v_stx_2321_);
return v___y_2409_;
}
}
v___jp_2453_:
{
if (v___y_2456_ == 0)
{
lean_object* v___x_2457_; 
lean_dec_ref(v___y_2455_);
v___x_2457_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2454_, v_a_2325_, v_a_2327_);
lean_dec_ref(v___y_2454_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v___x_2458_; 
lean_dec_ref_known(v___x_2457_, 1);
v___x_2458_ = l_Lean_Meta_saveState___redArg(v_a_2325_, v_a_2327_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
lean_inc(v_stx_2321_);
v___x_2460_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(v_stx_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_a_2459_);
lean_dec(v_stx_2321_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2470_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2470_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2468_; 
v___x_2465_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13));
v___x_2466_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2465_, v___f_2452_, v_a_2461_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2466_);
v___x_2468_ = v___x_2463_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2480_; 
v_a_2471_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2473_ = v___x_2460_;
v_isShared_2474_ = v_isSharedCheck_2480_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2460_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2480_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
lean_inc(v_a_2471_);
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
uint8_t v___x_2477_; 
v___x_2477_ = l_Lean_Exception_isInterrupt(v_a_2471_);
if (v___x_2477_ == 0)
{
uint8_t v___x_2478_; 
v___x_2478_ = l_Lean_Exception_isRuntime(v_a_2471_);
v___y_2409_ = v___x_2476_;
v___y_2410_ = v_a_2459_;
v___y_2411_ = v___x_2478_;
goto v___jp_2408_;
}
else
{
lean_dec(v_a_2471_);
v___y_2409_ = v___x_2476_;
v___y_2410_ = v_a_2459_;
v___y_2411_ = v___x_2477_;
goto v___jp_2408_;
}
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec(v_stx_2321_);
v_a_2481_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2458_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2458_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v_stx_2321_);
v_a_2489_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2457_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2457_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
else
{
lean_dec_ref(v___y_2454_);
lean_dec(v_stx_2321_);
return v___y_2455_;
}
}
v_reusejp_2497_:
{
uint8_t v___y_2500_; uint8_t v___x_2541_; 
v___x_2541_ = l_Lean_Exception_isInterrupt(v_a_2357_);
if (v___x_2541_ == 0)
{
uint8_t v___x_2542_; 
v___x_2542_ = l_Lean_Exception_isRuntime(v_a_2357_);
v___y_2500_ = v___x_2542_;
goto v___jp_2499_;
}
else
{
lean_dec(v_a_2357_);
v___y_2500_ = v___x_2541_;
goto v___jp_2499_;
}
v___jp_2499_:
{
if (v___y_2500_ == 0)
{
lean_object* v___x_2501_; 
lean_dec_ref(v___x_2498_);
v___x_2501_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2344_, v_a_2325_, v_a_2327_);
lean_dec(v_a_2344_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v___x_2502_; 
lean_dec_ref_known(v___x_2501_, 1);
v___x_2502_ = l_Lean_Meta_saveState___redArg(v_a_2325_, v_a_2327_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; lean_object* v___x_2504_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
lean_inc(v_stx_2321_);
v___x_2504_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(v_stx_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2514_; 
lean_dec(v_a_2503_);
lean_dec(v_stx_2321_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2514_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2514_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2509_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15));
v___x_2510_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(lean_box(0), v___x_2509_, v___f_2361_, v_a_2505_);
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2510_);
v___x_2512_ = v___x_2507_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2524_; 
v_a_2515_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2517_ = v___x_2504_;
v_isShared_2518_ = v_isSharedCheck_2524_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2504_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2524_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
lean_inc(v_a_2515_);
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
uint8_t v___x_2521_; 
v___x_2521_ = l_Lean_Exception_isInterrupt(v_a_2515_);
if (v___x_2521_ == 0)
{
uint8_t v___x_2522_; 
v___x_2522_ = l_Lean_Exception_isRuntime(v_a_2515_);
v___y_2454_ = v_a_2503_;
v___y_2455_ = v___x_2520_;
v___y_2456_ = v___x_2522_;
goto v___jp_2453_;
}
else
{
lean_dec(v_a_2515_);
v___y_2454_ = v_a_2503_;
v___y_2455_ = v___x_2520_;
v___y_2456_ = v___x_2521_;
goto v___jp_2453_;
}
}
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
lean_dec(v_stx_2321_);
v_a_2525_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v___x_2502_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2502_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_stx_2321_);
v_a_2533_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2501_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2501_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_dec(v_a_2344_);
lean_dec(v_stx_2321_);
return v___x_2498_;
}
}
}
}
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_stx_2321_);
v_a_2545_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2343_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2343_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
v___jp_2329_:
{
if (v___y_2332_ == 0)
{
lean_object* v___x_2333_; 
lean_dec_ref(v___y_2330_);
v___x_2333_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2331_, v_a_2325_, v_a_2327_);
lean_dec_ref(v___y_2331_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2334_; 
lean_dec_ref_known(v___x_2333_, 1);
v___x_2334_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
return v___x_2334_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_a_2335_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2333_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2333_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_dec_ref(v___y_2331_);
return v___y_2330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed(lean_object* v_stx_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(v_stx_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
return v_res_2561_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2);
v___x_2564_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0));
v___x_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v___x_2563_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool(void){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1);
return v___x_2566_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2);
v___x_2569_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0));
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2569_);
lean_ctor_set(v___x_2570_, 1, v___x_2568_);
return v___x_2570_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat(void){
_start:
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2);
v___x_2574_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0));
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___x_2573_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt(void){
_start:
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1);
return v___x_2576_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2);
v___x_2579_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0));
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2578_);
return v___x_2580_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instString(void){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1);
return v___x_2581_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2583_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2);
v___x_2584_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0));
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v___x_2583_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instName(void){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(lean_object* v_inst_2587_){
_start:
{
lean_object* v_evalTerm_2588_; lean_object* v_typeExpr_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2599_; 
v_evalTerm_2588_ = lean_ctor_get(v_inst_2587_, 0);
v_typeExpr_2589_ = lean_ctor_get(v_inst_2587_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_inst_2587_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2591_ = v_inst_2587_;
v_isShared_2592_ = v_isSharedCheck_2599_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_typeExpr_2589_);
lean_inc(v_evalTerm_2588_);
lean_dec(v_inst_2587_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2599_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
lean_inc_ref(v_typeExpr_2589_);
v___x_2593_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed), 11, 3);
lean_closure_set(v___x_2593_, 0, lean_box(0));
lean_closure_set(v___x_2593_, 1, v_typeExpr_2589_);
lean_closure_set(v___x_2593_, 2, v_evalTerm_2588_);
v___x_2594_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
v___x_2595_ = l_Lean_Expr_app___override(v___x_2594_, v_typeExpr_2589_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v___x_2595_);
lean_ctor_set(v___x_2591_, 0, v___x_2593_);
v___x_2597_ = v___x_2591_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2593_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instOption(lean_object* v_00_u03b1_2600_, lean_object* v_inst_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(v_inst_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(lean_object* v_inst_2603_){
_start:
{
lean_object* v_evalTerm_2604_; lean_object* v_typeExpr_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2615_; 
v_evalTerm_2604_ = lean_ctor_get(v_inst_2603_, 0);
v_typeExpr_2605_ = lean_ctor_get(v_inst_2603_, 1);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_inst_2603_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2607_ = v_inst_2603_;
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_typeExpr_2605_);
lean_inc(v_evalTerm_2604_);
lean_dec(v_inst_2603_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2613_; 
lean_inc_ref(v_typeExpr_2605_);
v___x_2609_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed), 11, 3);
lean_closure_set(v___x_2609_, 0, lean_box(0));
lean_closure_set(v___x_2609_, 1, v_typeExpr_2605_);
lean_closure_set(v___x_2609_, 2, v_evalTerm_2604_);
v___x_2610_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
v___x_2611_ = l_Lean_Expr_app___override(v___x_2610_, v_typeExpr_2605_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 1, v___x_2611_);
lean_ctor_set(v___x_2607_, 0, v___x_2609_);
v___x_2613_ = v___x_2607_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2609_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instList(lean_object* v_00_u03b1_2616_, lean_object* v_inst_2617_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(v_inst_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(lean_object* v_inst_2619_){
_start:
{
lean_object* v_evalTerm_2620_; lean_object* v_typeExpr_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2631_; 
v_evalTerm_2620_ = lean_ctor_get(v_inst_2619_, 0);
v_typeExpr_2621_ = lean_ctor_get(v_inst_2619_, 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_inst_2619_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2623_ = v_inst_2619_;
v_isShared_2624_ = v_isSharedCheck_2631_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_typeExpr_2621_);
lean_inc(v_evalTerm_2620_);
lean_dec(v_inst_2619_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2631_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2629_; 
lean_inc_ref(v_typeExpr_2621_);
v___x_2625_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed), 11, 3);
lean_closure_set(v___x_2625_, 0, lean_box(0));
lean_closure_set(v___x_2625_, 1, v_typeExpr_2621_);
lean_closure_set(v___x_2625_, 2, v_evalTerm_2620_);
v___x_2626_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
v___x_2627_ = l_Lean_Expr_app___override(v___x_2626_, v_typeExpr_2621_);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 1, v___x_2627_);
lean_ctor_set(v___x_2623_, 0, v___x_2625_);
v___x_2629_ = v___x_2623_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v___x_2625_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v___x_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instArray(lean_object* v_00_u03b1_2632_, lean_object* v_inst_2633_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(v_inst_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(lean_object* v_inst_2635_, lean_object* v_inst_2636_){
_start:
{
lean_object* v_evalTerm_2637_; lean_object* v_typeExpr_2638_; lean_object* v_evalTerm_2639_; lean_object* v_typeExpr_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2650_; 
v_evalTerm_2637_ = lean_ctor_get(v_inst_2635_, 0);
lean_inc_ref(v_evalTerm_2637_);
v_typeExpr_2638_ = lean_ctor_get(v_inst_2635_, 1);
lean_inc_ref(v_typeExpr_2638_);
lean_dec_ref(v_inst_2635_);
v_evalTerm_2639_ = lean_ctor_get(v_inst_2636_, 0);
v_typeExpr_2640_ = lean_ctor_get(v_inst_2636_, 1);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_inst_2636_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2642_ = v_inst_2636_;
v_isShared_2643_ = v_isSharedCheck_2650_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_typeExpr_2640_);
lean_inc(v_evalTerm_2639_);
lean_dec(v_inst_2636_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2650_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
lean_inc_ref(v_typeExpr_2640_);
lean_inc_ref(v_typeExpr_2638_);
v___x_2644_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed), 14, 6);
lean_closure_set(v___x_2644_, 0, lean_box(0));
lean_closure_set(v___x_2644_, 1, lean_box(0));
lean_closure_set(v___x_2644_, 2, v_typeExpr_2638_);
lean_closure_set(v___x_2644_, 3, v_typeExpr_2640_);
lean_closure_set(v___x_2644_, 4, v_evalTerm_2637_);
lean_closure_set(v___x_2644_, 5, v_evalTerm_2639_);
v___x_2645_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3);
v___x_2646_ = l_Lean_mkAppB(v___x_2645_, v_typeExpr_2638_, v_typeExpr_2640_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 1, v___x_2646_);
lean_ctor_set(v___x_2642_, 0, v___x_2644_);
v___x_2648_ = v___x_2642_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instProd(lean_object* v_00_u03b1_2651_, lean_object* v_00_u03b1_x27_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(v_inst_2653_, v_inst_2654_);
return v___x_2655_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2(void){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1));
v___x_2662_ = l_Lean_Expr_const___override(v___x_2661_, v___x_2660_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2663_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2);
v___x_2664_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0));
v___x_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v___x_2663_);
return v___x_2665_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue(void){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3);
return v___x_2666_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_box(0);
v___x_2668_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
v___x_2669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
lean_ctor_set(v___x_2669_, 1, v___x_2667_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg(){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_obj_once(&l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0, &l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0);
v___x_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___boxed(lean_object* v___y_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(lean_object* v_00_u03b1_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___boxed(lean_object* v_00_u03b1_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(v_00_u03b1_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(lean_object* v_e_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2695_ = l_Lean_Expr_cleanupAnnotations(v_e_2689_);
v___x_2696_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8));
v___x_2697_ = l_Lean_Expr_isConstOf(v___x_2695_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; uint8_t v___x_2699_; 
v___x_2698_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5));
v___x_2699_ = l_Lean_Expr_isConstOf(v___x_2695_, v___x_2698_);
lean_dec_ref(v___x_2695_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2700_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_box(v___x_2699_);
v___x_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2701_);
return v___x_2702_;
}
}
else
{
uint8_t v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_dec_ref(v___x_2695_);
v___x_2703_ = 0;
v___x_2704_ = lean_box(v___x_2703_);
v___x_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
return v___x_2705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed(lean_object* v_e_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(v_e_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
return v_res_2712_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___x_2715_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1));
v___x_2716_ = l_Lean_stringToMessageData(v___x_2715_);
return v___x_2716_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3(void){
_start:
{
uint8_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2717_ = 0;
v___x_2718_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1));
v___x_2719_ = l_Lean_MessageData_ofConstName(v___x_2718_, v___x_2717_);
return v___x_2719_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3);
v___x_2721_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_2722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v___x_2720_);
return v___x_2722_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6(void){
_start:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5));
v___x_2725_ = l_Lean_stringToMessageData(v___x_2724_);
return v___x_2725_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_2727_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4);
v___x_2728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v___x_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(lean_object* v_e_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2735_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0));
v___x_2736_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7);
v___x_2737_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_2735_, v_e_2729_, v___x_2736_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed(lean_object* v_e_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v_e_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(lean_object* v_e_2745_){
_start:
{
lean_object* v___y_2748_; lean_object* v___x_2758_; 
lean_inc_ref(v_e_2745_);
v___x_2758_ = l_Lean_Expr_nat_x3f(v_e_2745_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_Expr_rawNatLit_x3f(v_e_2745_);
v___y_2748_ = v___x_2759_;
goto v___jp_2747_;
}
else
{
lean_dec_ref(v_e_2745_);
v___y_2748_ = v___x_2758_;
goto v___jp_2747_;
}
v___jp_2747_:
{
if (lean_obj_tag(v___y_2748_) == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2749_;
}
else
{
lean_object* v_val_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
v_val_2750_ = lean_ctor_get(v___y_2748_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___y_2748_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___y_2748_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_val_2750_);
lean_dec(v___y_2748_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
lean_ctor_set_tag(v___x_2752_, 0);
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_val_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg___boxed(lean_object* v_e_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2760_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(lean_object* v_e_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
lean_object* v___x_2769_; 
v___x_2769_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2763_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed(lean_object* v_e_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(v_e_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
lean_dec(v_a_2772_);
lean_dec_ref(v_a_2771_);
return v_res_2776_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1(void){
_start:
{
uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2778_ = 0;
v___x_2779_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1));
v___x_2780_ = l_Lean_MessageData_ofConstName(v___x_2779_, v___x_2778_);
return v___x_2780_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1);
v___x_2782_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_2783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2781_);
return v___x_2783_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2784_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_2785_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2);
v___x_2786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v___x_2784_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(lean_object* v_e_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2793_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0));
v___x_2794_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3);
v___x_2795_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_2793_, v_e_2787_, v___x_2794_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed(lean_object* v_e_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_e_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_a_2798_);
lean_dec_ref(v_a_2797_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(lean_object* v_msg_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_ref_2809_; lean_object* v___x_2810_; lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2819_; 
v_ref_2809_ = lean_ctor_get(v___y_2806_, 5);
v___x_2810_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msg_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2813_ = v___x_2810_;
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2810_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_inc(v_ref_2809_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v_ref_2809_);
lean_ctor_set(v___x_2815_, 1, v_a_2811_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 1);
lean_ctor_set(v___x_2813_, 0, v___x_2815_);
v___x_2817_ = v___x_2813_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v_msg_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
return v_res_2826_;
}
}
static lean_object* _init_l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0));
v___x_2829_ = l_Lean_stringToMessageData(v___x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(lean_object* v_x_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
if (lean_obj_tag(v_x_2830_) == 0)
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_obj_once(&l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1, &l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1_once, _init_l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1);
v___x_2837_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v___x_2836_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
return v___x_2837_;
}
else
{
lean_object* v_val_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
v_val_2838_ = lean_ctor_get(v_x_2830_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_x_2830_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v_x_2830_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_val_2838_);
lean_dec(v_x_2830_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set_tag(v___x_2840_, 0);
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_val_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___boxed(lean_object* v_x_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v_x_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(lean_object* v_e_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v___y_2867_; lean_object* v___y_2868_; uint8_t v___y_2869_; lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Meta_saveState___redArg(v_a_2862_, v_a_2864_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
lean_inc_ref(v_e_2860_);
v___x_2927_ = l_Lean_Expr_int_x3f(v_e_2860_);
v___x_2928_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v___x_2927_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_dec(v_a_2926_);
lean_dec_ref(v_e_2860_);
return v___x_2928_;
}
else
{
lean_object* v_a_2929_; uint8_t v___y_2931_; uint8_t v___x_2971_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
v___x_2971_ = l_Lean_Exception_isInterrupt(v_a_2929_);
if (v___x_2971_ == 0)
{
uint8_t v___x_2972_; 
v___x_2972_ = l_Lean_Exception_isRuntime(v_a_2929_);
v___y_2931_ = v___x_2972_;
goto v___jp_2930_;
}
else
{
lean_dec(v_a_2929_);
v___y_2931_ = v___x_2971_;
goto v___jp_2930_;
}
v___jp_2930_:
{
if (v___y_2931_ == 0)
{
lean_object* v___x_2932_; 
lean_dec_ref_known(v___x_2928_, 1);
v___x_2932_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2926_, v_a_2862_, v_a_2864_);
lean_dec(v_a_2926_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v___x_2933_; 
lean_dec_ref_known(v___x_2932_, 1);
v___x_2933_ = l_Lean_Meta_saveState___redArg(v_a_2862_, v_a_2864_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
lean_inc_ref(v_e_2860_);
v___x_2935_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_2860_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_a_2934_);
lean_dec_ref(v_e_2860_);
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2944_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2940_ = lean_nat_to_int(v_a_2936_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2940_);
v___x_2942_ = v___x_2938_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2954_; 
v_a_2945_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2947_ = v___x_2935_;
v_isShared_2948_ = v_isSharedCheck_2954_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2935_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2954_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
lean_inc(v_a_2945_);
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
uint8_t v___x_2951_; 
v___x_2951_ = l_Lean_Exception_isInterrupt(v_a_2945_);
if (v___x_2951_ == 0)
{
uint8_t v___x_2952_; 
v___x_2952_ = l_Lean_Exception_isRuntime(v_a_2945_);
v___y_2867_ = v_a_2934_;
v___y_2868_ = v___x_2950_;
v___y_2869_ = v___x_2952_;
goto v___jp_2866_;
}
else
{
lean_dec(v_a_2945_);
v___y_2867_ = v_a_2934_;
v___y_2868_ = v___x_2950_;
v___y_2869_ = v___x_2951_;
goto v___jp_2866_;
}
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec_ref(v_e_2860_);
v_a_2955_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2933_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2933_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v_e_2860_);
v_a_2963_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2932_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2932_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_dec(v_a_2926_);
lean_dec_ref(v_e_2860_);
return v___x_2928_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_dec_ref(v_e_2860_);
v_a_2973_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2925_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2925_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
v___jp_2866_:
{
if (v___y_2869_ == 0)
{
lean_object* v___x_2870_; 
lean_dec_ref(v___y_2868_);
v___x_2870_ = l_Lean_Meta_SavedState_restore___redArg(v___y_2867_, v_a_2862_, v_a_2864_);
lean_dec_ref(v___y_2867_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v___x_2871_; uint8_t v___x_2872_; 
lean_dec_ref_known(v___x_2870_, 1);
v___x_2871_ = l_Lean_Expr_cleanupAnnotations(v_e_2860_);
v___x_2872_ = l_Lean_Expr_isApp(v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
lean_dec_ref(v___x_2871_);
v___x_2873_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2873_;
}
else
{
lean_object* v_arg_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_arg_2874_ = lean_ctor_get(v___x_2871_, 1);
lean_inc_ref(v_arg_2874_);
v___x_2875_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2871_);
v___x_2876_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1));
v___x_2877_ = l_Lean_Expr_isConstOf(v___x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2878_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2));
v___x_2879_ = l_Lean_Expr_isConstOf(v___x_2875_, v___x_2878_);
lean_dec_ref(v___x_2875_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; 
lean_dec_ref(v_arg_2874_);
v___x_2880_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_2880_;
}
else
{
lean_object* v___x_2881_; 
v___x_2881_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_2874_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2890_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2884_ = v___x_2881_;
v_isShared_2885_ = v_isSharedCheck_2890_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2890_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
v___x_2886_ = lean_nat_to_int(v_a_2882_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2886_);
v___x_2888_ = v___x_2884_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_a_2891_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2881_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2881_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
else
{
lean_object* v___x_2899_; 
lean_dec_ref(v___x_2875_);
v___x_2899_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_2874_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2908_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_2908_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2908_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2904_ = lean_int_neg_succ_of_nat(v_a_2900_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2904_);
v___x_2906_ = v___x_2902_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v_a_2909_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2899_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2899_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v_e_2860_);
v_a_2917_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2870_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2870_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_dec_ref(v___y_2867_);
lean_dec_ref(v_e_2860_);
return v___y_2868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed(lean_object* v_e_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(v_e_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(lean_object* v_00_u03b1_2988_, lean_object* v_x_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v_x_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___boxed(lean_object* v_00_u03b1_2996_, lean_object* v_x_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(v_00_u03b1_2996_, v_x_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(lean_object* v_00_u03b1_3004_, lean_object* v_msg_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v_msg_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_msg_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(v_00_u03b1_3012_, v_msg_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
return v_res_3019_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1(void){
_start:
{
uint8_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = 0;
v___x_3022_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1));
v___x_3023_ = l_Lean_MessageData_ofConstName(v___x_3022_, v___x_3021_);
return v___x_3023_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3024_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1);
v___x_3025_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_3024_);
return v___x_3026_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3028_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(lean_object* v_e_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0));
v___x_3037_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3);
v___x_3038_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3036_, v_e_3030_, v___x_3037_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed(lean_object* v_e_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(v_e_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(lean_object* v_x_3046_){
_start:
{
if (lean_obj_tag(v_x_3046_) == 9)
{
lean_object* v_a_3048_; 
v_a_3048_ = lean_ctor_get(v_x_3046_, 0);
lean_inc_ref(v_a_3048_);
lean_dec_ref_known(v_x_3046_, 1);
if (lean_obj_tag(v_a_3048_) == 1)
{
lean_object* v_val_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
v_val_3049_ = lean_ctor_get(v_a_3048_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v_a_3048_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v_a_3048_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_val_3049_);
lean_dec(v_a_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 0);
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_val_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
else
{
lean_object* v___x_3057_; 
lean_dec_ref(v_a_3048_);
v___x_3057_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3057_;
}
}
else
{
lean_object* v___x_3058_; 
lean_dec_ref(v_x_3046_);
v___x_3058_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg___boxed(lean_object* v_x_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_x_3059_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(lean_object* v_x_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_x_3062_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed(lean_object* v_x_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(v_x_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_);
lean_dec(v_a_3073_);
lean_dec_ref(v_a_3072_);
lean_dec(v_a_3071_);
lean_dec_ref(v_a_3070_);
return v_res_3075_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1(void){
_start:
{
uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3077_ = 0;
v___x_3078_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1));
v___x_3079_ = l_Lean_MessageData_ofConstName(v___x_3078_, v___x_3077_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1);
v___x_3081_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3084_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2);
v___x_3085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(lean_object* v_e_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3092_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0));
v___x_3093_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3);
v___x_3094_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3092_, v_e_3086_, v___x_3093_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed(lean_object* v_e_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(v_e_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(lean_object* v_e_3102_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Expr_name_x3f(v_e_3102_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3105_;
}
else
{
lean_object* v_val_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
v_val_3106_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3104_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_val_3106_);
lean_dec(v___x_3104_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
lean_ctor_set_tag(v___x_3108_, 0);
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_val_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg___boxed(lean_object* v_e_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3114_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(lean_object* v_e_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3117_);
return v___x_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed(lean_object* v_e_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(v_e_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
return v_res_3130_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1(void){
_start:
{
uint8_t v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3132_ = 0;
v___x_3133_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1));
v___x_3134_ = l_Lean_MessageData_ofConstName(v___x_3133_, v___x_3132_);
return v___x_3134_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1);
v___x_3136_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v___x_3135_);
return v___x_3137_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3138_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3139_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3139_);
lean_ctor_set(v___x_3140_, 1, v___x_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(lean_object* v_e_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3147_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0));
v___x_3148_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3);
v___x_3149_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3147_, v_e_3141_, v___x_3148_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed(lean_object* v_e_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(v_e_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(lean_object* v_ev_3160_, lean_object* v_e_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
v___x_3167_ = l_Lean_Expr_cleanupAnnotations(v_e_3161_);
v___x_3168_ = l_Lean_Expr_isApp(v___x_3167_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3169_; 
lean_dec_ref(v___x_3167_);
lean_dec_ref(v_ev_3160_);
v___x_3169_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3169_;
}
else
{
lean_object* v_arg_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; 
v_arg_3170_ = lean_ctor_get(v___x_3167_, 1);
lean_inc_ref(v_arg_3170_);
v___x_3171_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3167_);
v___x_3172_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8));
v___x_3173_ = l_Lean_Expr_isConstOf(v___x_3171_, v___x_3172_);
if (v___x_3173_ == 0)
{
uint8_t v___x_3174_; 
v___x_3174_ = l_Lean_Expr_isApp(v___x_3171_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
lean_dec_ref(v___x_3171_);
lean_dec_ref(v_arg_3170_);
lean_dec_ref(v_ev_3160_);
v___x_3175_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3175_;
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3171_);
v___x_3177_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0));
v___x_3178_ = l_Lean_Expr_isConstOf(v___x_3176_, v___x_3177_);
lean_dec_ref(v___x_3176_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; 
lean_dec_ref(v_arg_3170_);
lean_dec_ref(v_ev_3160_);
v___x_3179_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3179_;
}
else
{
lean_object* v___x_3180_; 
lean_inc(v_a_3165_);
lean_inc_ref(v_a_3164_);
lean_inc(v_a_3163_);
lean_inc_ref(v_a_3162_);
v___x_3180_ = lean_apply_6(v_ev_3160_, v_arg_3170_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, lean_box(0));
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3189_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3189_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3189_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
v___x_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3185_, 0, v_a_3181_);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3185_);
v___x_3187_ = v___x_3183_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
v_a_3190_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3180_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3180_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
}
else
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
lean_dec_ref(v___x_3171_);
lean_dec_ref(v_arg_3170_);
lean_dec_ref(v_ev_3160_);
v___x_3198_ = lean_box(0);
v___x_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
return v___x_3199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___boxed(lean_object* v_ev_3200_, lean_object* v_e_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(v_ev_3200_, v_e_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec_ref(v_a_3202_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(lean_object* v_00_u03b1_3208_, lean_object* v_ev_3209_, lean_object* v_e_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(v_ev_3209_, v_e_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed(lean_object* v_00_u03b1_3217_, lean_object* v_ev_3218_, lean_object* v_e_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(v_00_u03b1_3217_, v_ev_3218_, v_e_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
lean_dec(v_a_3221_);
lean_dec_ref(v_a_3220_);
return v_res_3225_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0(void){
_start:
{
uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = 0;
v___x_3227_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1));
v___x_3228_ = l_Lean_MessageData_ofConstName(v___x_3227_, v___x_3226_);
return v___x_3228_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0);
v___x_3230_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3233_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set(v___x_3234_, 1, v___x_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(lean_object* v_ev_3235_, lean_object* v_e_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Meta_saveState___redArg(v_a_3238_, v_a_3240_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
lean_inc_ref(v_ev_3235_);
v___x_3244_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed), 8, 2);
lean_closure_set(v___x_3244_, 0, lean_box(0));
lean_closure_set(v___x_3244_, 1, v_ev_3235_);
v___x_3245_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2);
lean_inc_ref(v_e_3236_);
v___x_3246_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3244_, v_e_3236_, v___x_3245_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_dec(v_a_3243_);
lean_dec_ref(v_e_3236_);
lean_dec_ref(v_ev_3235_);
return v___x_3246_;
}
else
{
lean_object* v_a_3247_; uint8_t v___y_3249_; uint8_t v___x_3284_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
v___x_3284_ = l_Lean_Exception_isInterrupt(v_a_3247_);
if (v___x_3284_ == 0)
{
uint8_t v___x_3285_; 
v___x_3285_ = l_Lean_Exception_isRuntime(v_a_3247_);
v___y_3249_ = v___x_3285_;
goto v___jp_3248_;
}
else
{
lean_dec(v_a_3247_);
v___y_3249_ = v___x_3284_;
goto v___jp_3248_;
}
v___jp_3248_:
{
if (v___y_3249_ == 0)
{
lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3282_; 
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3282_ == 0)
{
lean_object* v_unused_3283_; 
v_unused_3283_ = lean_ctor_get(v___x_3246_, 0);
lean_dec(v_unused_3283_);
v___x_3251_ = v___x_3246_;
v_isShared_3252_ = v_isSharedCheck_3282_;
goto v_resetjp_3250_;
}
else
{
lean_dec(v___x_3246_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3282_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3243_, v_a_3238_, v_a_3240_);
lean_dec(v_a_3243_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v___x_3254_; 
lean_dec_ref_known(v___x_3253_, 1);
lean_inc(v_a_3240_);
lean_inc_ref(v_a_3239_);
lean_inc(v_a_3238_);
lean_inc_ref(v_a_3237_);
v___x_3254_ = lean_apply_6(v_ev_3235_, v_e_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, lean_box(0));
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3265_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3265_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3265_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v_a_3255_);
v___x_3260_ = v___x_3251_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3262_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3260_);
v___x_3262_ = v___x_3257_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_del_object(v___x_3251_);
v_a_3266_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3254_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3254_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_del_object(v___x_3251_);
lean_dec_ref(v_e_3236_);
lean_dec_ref(v_ev_3235_);
v_a_3274_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3253_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3253_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
else
{
lean_dec(v_a_3243_);
lean_dec_ref(v_e_3236_);
lean_dec_ref(v_ev_3235_);
return v___x_3246_;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec_ref(v_e_3236_);
lean_dec_ref(v_ev_3235_);
v_a_3286_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3242_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3242_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___boxed(lean_object* v_ev_3294_, lean_object* v_e_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_){
_start:
{
lean_object* v_res_3301_; 
v_res_3301_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(v_ev_3294_, v_e_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_);
lean_dec(v_a_3299_);
lean_dec_ref(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(lean_object* v_00_u03b1_3302_, lean_object* v_ev_3303_, lean_object* v_e_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(v_ev_3303_, v_e_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed(lean_object* v_00_u03b1_3311_, lean_object* v_ev_3312_, lean_object* v_e_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_){
_start:
{
lean_object* v_res_3319_; 
v_res_3319_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(v_00_u03b1_3311_, v_ev_3312_, v_e_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
lean_dec(v_a_3317_);
lean_dec_ref(v_a_3316_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
return v_res_3319_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3321_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0));
v___x_3322_ = l_Lean_stringToMessageData(v___x_3321_);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2(void){
_start:
{
uint8_t v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3323_ = 0;
v___x_3324_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0));
v___x_3325_ = l_Lean_MessageData_ofConstName(v___x_3324_, v___x_3323_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(lean_object* v_ev_3326_, lean_object* v_e_3327_, uint8_t v_didWHNF_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
lean_inc_ref(v_e_3327_);
v___x_3361_ = l_Lean_Expr_cleanupAnnotations(v_e_3327_);
v___x_3362_ = l_Lean_Expr_isApp(v___x_3361_);
if (v___x_3362_ == 0)
{
lean_dec_ref(v___x_3361_);
v___y_3335_ = v_a_3329_;
v___y_3336_ = v_a_3330_;
v___y_3337_ = v_a_3331_;
v___y_3338_ = v_a_3332_;
goto v___jp_3334_;
}
else
{
lean_object* v_arg_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v_arg_3363_ = lean_ctor_get(v___x_3361_, 1);
lean_inc_ref(v_arg_3363_);
v___x_3364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3361_);
v___x_3365_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5));
v___x_3366_ = l_Lean_Expr_isConstOf(v___x_3364_, v___x_3365_);
if (v___x_3366_ == 0)
{
uint8_t v___x_3367_; 
v___x_3367_ = l_Lean_Expr_isApp(v___x_3364_);
if (v___x_3367_ == 0)
{
lean_dec_ref(v___x_3364_);
lean_dec_ref(v_arg_3363_);
v___y_3335_ = v_a_3329_;
v___y_3336_ = v_a_3330_;
v___y_3337_ = v_a_3331_;
v___y_3338_ = v_a_3332_;
goto v___jp_3334_;
}
else
{
lean_object* v_arg_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v_arg_3368_ = lean_ctor_get(v___x_3364_, 1);
lean_inc_ref(v_arg_3368_);
v___x_3369_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3364_);
v___x_3370_ = l_Lean_Expr_isApp(v___x_3369_);
if (v___x_3370_ == 0)
{
lean_dec_ref(v___x_3369_);
lean_dec_ref(v_arg_3368_);
lean_dec_ref(v_arg_3363_);
v___y_3335_ = v_a_3329_;
v___y_3336_ = v_a_3330_;
v___y_3337_ = v_a_3331_;
v___y_3338_ = v_a_3332_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3371_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3369_);
v___x_3372_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2));
v___x_3373_ = l_Lean_Expr_isConstOf(v___x_3371_, v___x_3372_);
lean_dec_ref(v___x_3371_);
if (v___x_3373_ == 0)
{
lean_dec_ref(v_arg_3368_);
lean_dec_ref(v_arg_3363_);
v___y_3335_ = v_a_3329_;
v___y_3336_ = v_a_3330_;
v___y_3337_ = v_a_3331_;
v___y_3338_ = v_a_3332_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3374_; 
lean_dec_ref(v_e_3327_);
lean_inc_ref(v_ev_3326_);
lean_inc(v_a_3332_);
lean_inc_ref(v_a_3331_);
lean_inc(v_a_3330_);
lean_inc_ref(v_a_3329_);
v___x_3374_ = lean_apply_6(v_ev_3326_, v_arg_3368_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, lean_box(0));
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3376_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v___x_3376_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3326_, v_arg_3363_, v___x_3366_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3385_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3379_ = v___x_3376_;
v_isShared_3380_ = v_isSharedCheck_3385_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3376_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3385_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3381_, 0, v_a_3375_);
lean_ctor_set(v___x_3381_, 1, v_a_3377_);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3381_);
v___x_3383_ = v___x_3379_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
else
{
lean_dec(v_a_3375_);
return v___x_3376_;
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_ev_3326_);
v_a_3386_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3374_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3374_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v___x_3364_);
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_e_3327_);
lean_dec_ref(v_ev_3326_);
v___x_3394_ = lean_box(0);
v___x_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
return v___x_3395_;
}
}
v___jp_3334_:
{
if (v_didWHNF_3328_ == 0)
{
lean_object* v___x_3339_; 
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
v___x_3339_ = lean_whnf(v_e_3327_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; uint8_t v___x_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = 1;
v_e_3327_ = v_a_3340_;
v_didWHNF_3328_ = v___x_3341_;
v_a_3329_ = v___y_3335_;
v_a_3330_ = v___y_3336_;
v_a_3331_ = v___y_3337_;
v_a_3332_ = v___y_3338_;
goto _start;
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec_ref(v_ev_3326_);
v_a_3343_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3339_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3339_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
lean_dec_ref(v_ev_3326_);
v___x_3351_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1);
v___x_3352_ = l_Lean_indentExpr(v_e_3327_);
v___x_3353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3351_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2);
v___x_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v___x_3359_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
return v___x_3360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___boxed(lean_object* v_ev_3396_, lean_object* v_e_3397_, lean_object* v_didWHNF_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
uint8_t v_didWHNF_boxed_3404_; lean_object* v_res_3405_; 
v_didWHNF_boxed_3404_ = lean_unbox(v_didWHNF_3398_);
v_res_3405_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3396_, v_e_3397_, v_didWHNF_boxed_3404_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(lean_object* v_00_u03b1_3406_, lean_object* v_ev_3407_, lean_object* v_e_3408_, uint8_t v_didWHNF_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3407_, v_e_3408_, v_didWHNF_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___boxed(lean_object* v_00_u03b1_3416_, lean_object* v_ev_3417_, lean_object* v_e_3418_, lean_object* v_didWHNF_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
uint8_t v_didWHNF_boxed_3425_; lean_object* v_res_3426_; 
v_didWHNF_boxed_3425_ = lean_unbox(v_didWHNF_3419_);
v_res_3426_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(v_00_u03b1_3416_, v_ev_3417_, v_e_3418_, v_didWHNF_boxed_3425_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(lean_object* v_ev_3433_, lean_object* v_e_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v_e_x27_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3465_ = l_Lean_Expr_cleanupAnnotations(v_e_3434_);
v___x_3466_ = l_Lean_Expr_isApp(v___x_3465_);
if (v___x_3466_ == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref(v___x_3465_);
lean_dec_ref(v_ev_3433_);
v___x_3467_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3467_;
}
else
{
lean_object* v_arg_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v_arg_3468_ = lean_ctor_get(v___x_3465_, 1);
lean_inc_ref(v_arg_3468_);
v___x_3469_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3465_);
v___x_3470_ = l_Lean_Expr_isApp(v___x_3469_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; 
lean_dec_ref(v___x_3469_);
lean_dec_ref(v_arg_3468_);
lean_dec_ref(v_ev_3433_);
v___x_3471_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3471_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3472_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3469_);
v___x_3473_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0));
v___x_3474_ = l_Lean_Expr_isConstOf(v___x_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; uint8_t v___x_3476_; 
v___x_3475_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1));
v___x_3476_ = l_Lean_Expr_isConstOf(v___x_3472_, v___x_3475_);
lean_dec_ref(v___x_3472_);
if (v___x_3476_ == 0)
{
lean_object* v___x_3477_; 
lean_dec_ref(v_arg_3468_);
lean_dec_ref(v_ev_3433_);
v___x_3477_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3477_;
}
else
{
v_e_x27_3441_ = v_arg_3468_;
v___y_3442_ = v___y_3435_;
v___y_3443_ = v___y_3436_;
v___y_3444_ = v___y_3437_;
v___y_3445_ = v___y_3438_;
goto v___jp_3440_;
}
}
else
{
lean_dec_ref(v___x_3472_);
v_e_x27_3441_ = v_arg_3468_;
v___y_3442_ = v___y_3435_;
v___y_3443_ = v___y_3436_;
v___y_3444_ = v___y_3437_;
v___y_3445_ = v___y_3438_;
goto v___jp_3440_;
}
}
}
v___jp_3440_:
{
uint8_t v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = 0;
v___x_3447_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_ev_3433_, v_e_x27_3441_, v___x_3446_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3456_; 
v_a_3448_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3450_ = v___x_3447_;
v_isShared_3451_ = v_isSharedCheck_3456_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v___x_3447_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3456_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v___x_3454_; 
v___x_3452_ = lean_array_mk(v_a_3448_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3452_);
v___x_3454_ = v___x_3450_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
v_a_3457_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3447_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3447_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed(lean_object* v_ev_3478_, lean_object* v_e_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(v_ev_3478_, v_e_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
return v_res_3485_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0(void){
_start:
{
uint8_t v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3486_ = 0;
v___x_3487_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1));
v___x_3488_ = l_Lean_MessageData_ofConstName(v___x_3487_, v___x_3486_);
return v___x_3488_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3489_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0);
v___x_3490_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v___x_3489_);
return v___x_3491_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3492_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3493_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1);
v___x_3494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___x_3492_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(lean_object* v_ev_3495_, lean_object* v_e_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_){
_start:
{
lean_object* v___f_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___f_3502_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3502_, 0, v_ev_3495_);
v___x_3503_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2);
v___x_3504_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___f_3502_, v_e_3496_, v___x_3503_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___boxed(lean_object* v_ev_3505_, lean_object* v_e_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(v_ev_3505_, v_e_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_a_3508_);
lean_dec_ref(v_a_3507_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(lean_object* v_00_u03b1_3513_, lean_object* v_ev_3514_, lean_object* v_e_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v___x_3521_; 
v___x_3521_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(v_ev_3514_, v_e_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed(lean_object* v_00_u03b1_3522_, lean_object* v_ev_3523_, lean_object* v_e_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(v_00_u03b1_3522_, v_ev_3523_, v_e_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(lean_object* v_e_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; uint8_t v___y_3542_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; uint8_t v___y_3558_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; uint8_t v___y_3603_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; uint8_t v___y_3650_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; uint8_t v___y_3697_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___x_3773_; uint8_t v___x_3774_; 
lean_inc_ref(v_e_3531_);
v___x_3773_ = l_Lean_Expr_cleanupAnnotations(v_e_3531_);
v___x_3774_ = l_Lean_Expr_isApp(v___x_3773_);
if (v___x_3774_ == 0)
{
lean_dec_ref(v___x_3773_);
v___y_3738_ = v_a_3532_;
v___y_3739_ = v_a_3533_;
v___y_3740_ = v_a_3534_;
v___y_3741_ = v_a_3535_;
goto v___jp_3737_;
}
else
{
lean_object* v_arg_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v_arg_3775_ = lean_ctor_get(v___x_3773_, 1);
lean_inc_ref(v_arg_3775_);
v___x_3776_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3773_);
v___x_3777_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8));
v___x_3778_ = l_Lean_Expr_isConstOf(v___x_3776_, v___x_3777_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; uint8_t v___x_3780_; 
v___x_3779_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10));
v___x_3780_ = l_Lean_Expr_isConstOf(v___x_3776_, v___x_3779_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; uint8_t v___x_3782_; 
v___x_3781_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13));
v___x_3782_ = l_Lean_Expr_isConstOf(v___x_3776_, v___x_3781_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; uint8_t v___x_3784_; 
v___x_3783_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15));
v___x_3784_ = l_Lean_Expr_isConstOf(v___x_3776_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3785_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3));
v___x_3786_ = l_Lean_Expr_isConstOf(v___x_3776_, v___x_3785_);
lean_dec_ref(v___x_3776_);
if (v___x_3786_ == 0)
{
lean_dec_ref(v_arg_3775_);
v___y_3738_ = v_a_3532_;
v___y_3739_ = v_a_3533_;
v___y_3740_ = v_a_3534_;
v___y_3741_ = v_a_3535_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3787_; 
lean_dec_ref(v_e_3531_);
v___x_3787_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(v_arg_3775_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3797_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3790_ = v___x_3787_;
v_isShared_3791_ = v_isSharedCheck_3797_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3787_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3797_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3792_; uint8_t v___x_3793_; lean_object* v___x_3795_; 
v___x_3792_ = lean_alloc_ctor(1, 0, 1);
v___x_3793_ = lean_unbox(v_a_3788_);
lean_dec(v_a_3788_);
lean_ctor_set_uint8(v___x_3792_, 0, v___x_3793_);
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v___x_3792_);
v___x_3795_ = v___x_3790_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3792_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
v_a_3798_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3787_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3787_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
else
{
lean_object* v___x_3806_; 
lean_dec_ref(v___x_3776_);
lean_dec_ref(v_e_3531_);
v___x_3806_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(v_arg_3775_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3815_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3809_ = v___x_3806_;
v_isShared_3810_ = v_isSharedCheck_3815_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3806_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3815_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_a_3807_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set(v___x_3809_, 0, v___x_3811_);
v___x_3813_ = v___x_3809_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
v_a_3816_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3806_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3806_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
else
{
lean_object* v___x_3824_; 
lean_dec_ref(v___x_3776_);
lean_dec_ref(v_e_3531_);
v___x_3824_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(v_arg_3775_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3833_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3833_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3831_; 
v___x_3829_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3829_, 0, v_a_3825_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3829_);
v___x_3831_ = v___x_3827_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3829_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
v_a_3834_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3824_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3824_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
else
{
lean_object* v___x_3842_; 
lean_dec_ref(v___x_3776_);
lean_dec_ref(v_e_3531_);
v___x_3842_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(v_arg_3775_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3851_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3845_ = v___x_3842_;
v_isShared_3846_ = v_isSharedCheck_3851_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3842_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3851_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v_a_3843_);
if (v_isShared_3846_ == 0)
{
lean_ctor_set(v___x_3845_, 0, v___x_3847_);
v___x_3849_ = v___x_3845_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
v_a_3852_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3842_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3842_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
else
{
lean_object* v___x_3860_; 
lean_dec_ref(v___x_3776_);
lean_dec_ref(v_e_3531_);
v___x_3860_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(v_arg_3775_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3869_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3863_ = v___x_3860_;
v_isShared_3864_ = v_isSharedCheck_3869_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3860_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3869_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3865_; lean_object* v___x_3867_; 
v___x_3865_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3865_, 0, v_a_3861_);
if (v_isShared_3864_ == 0)
{
lean_ctor_set(v___x_3863_, 0, v___x_3865_);
v___x_3867_ = v___x_3863_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v___x_3865_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
v_a_3870_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3860_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3860_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
}
v___jp_3537_:
{
if (v___y_3542_ == 0)
{
lean_object* v___x_3543_; 
lean_dec_ref(v___y_3540_);
v___x_3543_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3541_, v___y_3539_, v___y_3538_);
lean_dec_ref(v___y_3541_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v___x_3544_; 
lean_dec_ref_known(v___x_3543_, 1);
v___x_3544_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
return v___x_3544_;
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
v_a_3545_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3543_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3543_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_dec_ref(v___y_3541_);
return v___y_3540_;
}
}
v___jp_3553_:
{
if (v___y_3558_ == 0)
{
lean_object* v___x_3559_; 
lean_dec_ref(v___y_3555_);
v___x_3559_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3557_, v___y_3556_, v___y_3554_);
lean_dec_ref(v___y_3557_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v___x_3560_; 
lean_dec_ref_known(v___x_3559_, 1);
v___x_3560_ = l_Lean_Meta_saveState___redArg(v___y_3556_, v___y_3554_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_3531_);
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3571_; 
lean_dec(v_a_3561_);
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3571_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3571_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; lean_object* v___x_3569_; 
v___x_3567_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3567_, 0, v_a_3563_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3567_);
v___x_3569_ = v___x_3565_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v___x_3567_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3581_; 
v_a_3572_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3574_ = v___x_3562_;
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3562_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
lean_inc(v_a_3572_);
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
uint8_t v___x_3578_; 
v___x_3578_ = l_Lean_Exception_isInterrupt(v_a_3572_);
if (v___x_3578_ == 0)
{
uint8_t v___x_3579_; 
v___x_3579_ = l_Lean_Exception_isRuntime(v_a_3572_);
v___y_3538_ = v___y_3554_;
v___y_3539_ = v___y_3556_;
v___y_3540_ = v___x_3577_;
v___y_3541_ = v_a_3561_;
v___y_3542_ = v___x_3579_;
goto v___jp_3537_;
}
else
{
lean_dec(v_a_3572_);
v___y_3538_ = v___y_3554_;
v___y_3539_ = v___y_3556_;
v___y_3540_ = v___x_3577_;
v___y_3541_ = v_a_3561_;
v___y_3542_ = v___x_3578_;
goto v___jp_3537_;
}
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref(v_e_3531_);
v_a_3582_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3560_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3560_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref(v_e_3531_);
v_a_3590_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3559_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3559_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
else
{
lean_dec_ref(v___y_3557_);
lean_dec_ref(v_e_3531_);
return v___y_3555_;
}
}
v___jp_3598_:
{
if (v___y_3603_ == 0)
{
lean_object* v___x_3604_; 
lean_dec_ref(v___y_3602_);
v___x_3604_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3600_, v___y_3601_, v___y_3599_);
lean_dec_ref(v___y_3600_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v___x_3605_; 
lean_dec_ref_known(v___x_3604_, 1);
v___x_3605_ = l_Lean_Meta_saveState___redArg(v___y_3601_, v___y_3599_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
lean_inc_ref(v_e_3531_);
v___x_3607_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_e_3531_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_a_3606_);
lean_dec_ref(v_e_3531_);
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3610_ = v___x_3607_;
v_isShared_3611_ = v_isSharedCheck_3616_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3616_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3612_, 0, v_a_3608_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3612_);
v___x_3614_ = v___x_3610_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3626_; 
v_a_3617_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3619_ = v___x_3607_;
v_isShared_3620_ = v_isSharedCheck_3626_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3607_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3626_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
lean_inc(v_a_3617_);
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
uint8_t v___x_3623_; 
v___x_3623_ = l_Lean_Exception_isInterrupt(v_a_3617_);
if (v___x_3623_ == 0)
{
uint8_t v___x_3624_; 
v___x_3624_ = l_Lean_Exception_isRuntime(v_a_3617_);
v___y_3554_ = v___y_3599_;
v___y_3555_ = v___x_3622_;
v___y_3556_ = v___y_3601_;
v___y_3557_ = v_a_3606_;
v___y_3558_ = v___x_3624_;
goto v___jp_3553_;
}
else
{
lean_dec(v_a_3617_);
v___y_3554_ = v___y_3599_;
v___y_3555_ = v___x_3622_;
v___y_3556_ = v___y_3601_;
v___y_3557_ = v_a_3606_;
v___y_3558_ = v___x_3623_;
goto v___jp_3553_;
}
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v_e_3531_);
v_a_3627_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3605_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3605_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v_e_3531_);
v_a_3635_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3604_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3604_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
else
{
lean_dec_ref(v___y_3600_);
lean_dec_ref(v_e_3531_);
return v___y_3602_;
}
}
v___jp_3643_:
{
if (v___y_3650_ == 0)
{
lean_object* v___x_3651_; 
lean_dec_ref(v___y_3645_);
v___x_3651_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3646_, v___y_3647_, v___y_3644_);
lean_dec_ref(v___y_3646_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v___x_3652_; 
lean_dec_ref_known(v___x_3651_, 1);
v___x_3652_ = l_Lean_Meta_saveState___redArg(v___y_3647_, v___y_3644_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3654_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
lean_inc_ref(v_e_3531_);
v___x_3654_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(v_e_3531_, v___y_3648_, v___y_3647_, v___y_3649_, v___y_3644_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_object* v_a_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v_a_3653_);
lean_dec_ref(v_e_3531_);
v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3657_ = v___x_3654_;
v_isShared_3658_ = v_isSharedCheck_3663_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_a_3655_);
lean_dec(v___x_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3663_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3659_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_3659_, 0, v_a_3655_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3659_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3673_; 
v_a_3664_ = lean_ctor_get(v___x_3654_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3654_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3666_ = v___x_3654_;
v_isShared_3667_ = v_isSharedCheck_3673_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3654_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3673_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
lean_inc(v_a_3664_);
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
uint8_t v___x_3670_; 
v___x_3670_ = l_Lean_Exception_isInterrupt(v_a_3664_);
if (v___x_3670_ == 0)
{
uint8_t v___x_3671_; 
v___x_3671_ = l_Lean_Exception_isRuntime(v_a_3664_);
v___y_3599_ = v___y_3644_;
v___y_3600_ = v_a_3653_;
v___y_3601_ = v___y_3647_;
v___y_3602_ = v___x_3669_;
v___y_3603_ = v___x_3671_;
goto v___jp_3598_;
}
else
{
lean_dec(v_a_3664_);
v___y_3599_ = v___y_3644_;
v___y_3600_ = v_a_3653_;
v___y_3601_ = v___y_3647_;
v___y_3602_ = v___x_3669_;
v___y_3603_ = v___x_3670_;
goto v___jp_3598_;
}
}
}
}
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref(v_e_3531_);
v_a_3674_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3652_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3652_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref(v_e_3531_);
v_a_3682_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3651_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3651_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
else
{
lean_dec_ref(v___y_3646_);
lean_dec_ref(v_e_3531_);
return v___y_3645_;
}
}
v___jp_3690_:
{
if (v___y_3697_ == 0)
{
lean_object* v___x_3698_; 
lean_dec_ref(v___y_3693_);
v___x_3698_ = l_Lean_Meta_SavedState_restore___redArg(v___y_3691_, v___y_3694_, v___y_3692_);
lean_dec_ref(v___y_3691_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v___x_3699_; 
lean_dec_ref_known(v___x_3698_, 1);
v___x_3699_ = l_Lean_Meta_saveState___redArg(v___y_3694_, v___y_3692_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3701_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
lean_dec_ref_known(v___x_3699_, 1);
lean_inc_ref(v_e_3531_);
v___x_3701_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_3531_);
if (lean_obj_tag(v___x_3701_) == 0)
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3710_; 
lean_dec(v_a_3700_);
lean_dec_ref(v_e_3531_);
v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3704_ = v___x_3701_;
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3706_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3706_, 0, v_a_3702_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3706_);
v___x_3708_ = v___x_3704_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3720_; 
v_a_3711_ = lean_ctor_get(v___x_3701_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3701_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3713_ = v___x_3701_;
v_isShared_3714_ = v_isSharedCheck_3720_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3701_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3720_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
lean_inc(v_a_3711_);
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
uint8_t v___x_3717_; 
v___x_3717_ = l_Lean_Exception_isInterrupt(v_a_3711_);
if (v___x_3717_ == 0)
{
uint8_t v___x_3718_; 
v___x_3718_ = l_Lean_Exception_isRuntime(v_a_3711_);
v___y_3644_ = v___y_3692_;
v___y_3645_ = v___x_3716_;
v___y_3646_ = v_a_3700_;
v___y_3647_ = v___y_3694_;
v___y_3648_ = v___y_3695_;
v___y_3649_ = v___y_3696_;
v___y_3650_ = v___x_3718_;
goto v___jp_3643_;
}
else
{
lean_dec(v_a_3711_);
v___y_3644_ = v___y_3692_;
v___y_3645_ = v___x_3716_;
v___y_3646_ = v_a_3700_;
v___y_3647_ = v___y_3694_;
v___y_3648_ = v___y_3695_;
v___y_3649_ = v___y_3696_;
v___y_3650_ = v___x_3717_;
goto v___jp_3643_;
}
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec_ref(v_e_3531_);
v_a_3721_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3699_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3699_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v_e_3531_);
v_a_3729_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3698_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3698_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_dec_ref(v___y_3691_);
lean_dec_ref(v_e_3531_);
return v___y_3693_;
}
}
v___jp_3737_:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_Meta_saveState___redArg(v___y_3739_, v___y_3741_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3744_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_a_3743_);
lean_dec_ref_known(v___x_3742_, 1);
lean_inc_ref(v_e_3531_);
v___x_3744_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(v_e_3531_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_a_3743_);
lean_dec_ref(v_e_3531_);
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3754_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3754_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; uint8_t v___x_3750_; lean_object* v___x_3752_; 
v___x_3749_ = lean_alloc_ctor(1, 0, 1);
v___x_3750_ = lean_unbox(v_a_3745_);
lean_dec(v_a_3745_);
lean_ctor_set_uint8(v___x_3749_, 0, v___x_3750_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3749_);
v___x_3752_ = v___x_3747_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3749_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3764_; 
v_a_3755_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3757_ = v___x_3744_;
v_isShared_3758_ = v_isSharedCheck_3764_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3744_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3764_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
lean_inc(v_a_3755_);
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
uint8_t v___x_3761_; 
v___x_3761_ = l_Lean_Exception_isInterrupt(v_a_3755_);
if (v___x_3761_ == 0)
{
uint8_t v___x_3762_; 
v___x_3762_ = l_Lean_Exception_isRuntime(v_a_3755_);
v___y_3691_ = v_a_3743_;
v___y_3692_ = v___y_3741_;
v___y_3693_ = v___x_3760_;
v___y_3694_ = v___y_3739_;
v___y_3695_ = v___y_3738_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___x_3762_;
goto v___jp_3690_;
}
else
{
lean_dec(v_a_3755_);
v___y_3691_ = v_a_3743_;
v___y_3692_ = v___y_3741_;
v___y_3693_ = v___x_3760_;
v___y_3694_ = v___y_3739_;
v___y_3695_ = v___y_3738_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___x_3761_;
goto v___jp_3690_;
}
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v_e_3531_);
v_a_3765_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3742_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3742_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed(lean_object* v_e_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(v_e_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
return v_res_3884_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1(void){
_start:
{
uint8_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = 0;
v___x_3887_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1));
v___x_3888_ = l_Lean_MessageData_ofConstName(v___x_3887_, v___x_3886_);
return v___x_3888_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3889_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1);
v___x_3890_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v___x_3889_);
return v___x_3891_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3892_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6, &l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6);
v___x_3893_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v___x_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(lean_object* v_e_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3901_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0));
v___x_3902_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3, &l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3);
v___x_3903_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(v___x_3901_, v_e_3895_, v___x_3902_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
return v___x_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed(lean_object* v_e_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(v_e_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
return v_res_3910_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1(void){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3912_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3);
v___x_3913_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0));
v___x_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
lean_ctor_set(v___x_3914_, 1, v___x_3912_);
return v___x_3914_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool(void){
_start:
{
lean_object* v___x_3915_; 
v___x_3915_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1);
return v___x_3915_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1(void){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3917_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3);
v___x_3918_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0));
v___x_3919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3918_);
lean_ctor_set(v___x_3919_, 1, v___x_3917_);
return v___x_3919_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat(void){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1);
return v___x_3920_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3922_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3);
v___x_3923_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0));
v___x_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v___x_3922_);
return v___x_3924_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt(void){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1);
return v___x_3925_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1(void){
_start:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3927_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3);
v___x_3928_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0));
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v___x_3927_);
return v___x_3929_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instString(void){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1);
return v___x_3930_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1(void){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3, &l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3);
v___x_3933_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0));
v___x_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
lean_ctor_set(v___x_3934_, 1, v___x_3932_);
return v___x_3934_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalExpr_instName(void){
_start:
{
lean_object* v___x_3935_; 
v___x_3935_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1, &l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1);
return v___x_3935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(lean_object* v_inst_3936_){
_start:
{
lean_object* v_evalExpr_3937_; lean_object* v_expectedType_x3f_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3959_; 
v_evalExpr_3937_ = lean_ctor_get(v_inst_3936_, 0);
v_expectedType_x3f_3938_ = lean_ctor_get(v_inst_3936_, 1);
v_isSharedCheck_3959_ = !lean_is_exclusive(v_inst_3936_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3940_ = v_inst_3936_;
v_isShared_3941_ = v_isSharedCheck_3959_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_expectedType_x3f_3938_);
lean_inc(v_evalExpr_3937_);
lean_dec(v_inst_3936_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3959_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; 
v___x_3942_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed), 8, 2);
lean_closure_set(v___x_3942_, 0, lean_box(0));
lean_closure_set(v___x_3942_, 1, v_evalExpr_3937_);
if (lean_obj_tag(v_expectedType_x3f_3938_) == 0)
{
lean_object* v___x_3944_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3942_);
v___x_3944_ = v___x_3940_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v_expectedType_x3f_3938_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
else
{
lean_object* v_val_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3958_; 
v_val_3946_ = lean_ctor_get(v_expectedType_x3f_3938_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v_expectedType_x3f_3938_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3948_ = v_expectedType_x3f_3938_;
v_isShared_3949_ = v_isSharedCheck_3958_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_val_3946_);
lean_dec(v_expectedType_x3f_3938_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3958_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3953_; 
v___x_3950_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2);
v___x_3951_ = l_Lean_Expr_app___override(v___x_3950_, v_val_3946_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3951_);
v___x_3953_ = v___x_3948_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v___x_3951_);
v___x_3953_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3952_;
}
v_reusejp_3952_:
{
lean_object* v___x_3955_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 1, v___x_3953_);
lean_ctor_set(v___x_3940_, 0, v___x_3942_);
v___x_3955_ = v___x_3940_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3956_, 1, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instOption(lean_object* v_00_u03b1_3960_, lean_object* v_inst_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(v_inst_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(lean_object* v_evalExpr_3963_, lean_object* v_e_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
uint8_t v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = 0;
v___x_3971_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(v_evalExpr_3963_, v_e_3964_, v___x_3970_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed(lean_object* v_evalExpr_3972_, lean_object* v_e_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(v_evalExpr_3972_, v_e_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(lean_object* v_inst_3980_){
_start:
{
lean_object* v_evalExpr_3981_; lean_object* v_expectedType_x3f_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4003_; 
v_evalExpr_3981_ = lean_ctor_get(v_inst_3980_, 0);
v_expectedType_x3f_3982_ = lean_ctor_get(v_inst_3980_, 1);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_inst_3980_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3984_ = v_inst_3980_;
v_isShared_3985_ = v_isSharedCheck_4003_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_expectedType_x3f_3982_);
lean_inc(v_evalExpr_3981_);
lean_dec(v_inst_3980_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4003_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___f_3986_; 
v___f_3986_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3986_, 0, v_evalExpr_3981_);
if (lean_obj_tag(v_expectedType_x3f_3982_) == 0)
{
lean_object* v___x_3988_; 
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___f_3986_);
v___x_3988_ = v___x_3984_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___f_3986_);
lean_ctor_set(v_reuseFailAlloc_3989_, 1, v_expectedType_x3f_3982_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
else
{
lean_object* v_val_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4002_; 
v_val_3990_ = lean_ctor_get(v_expectedType_x3f_3982_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_expectedType_x3f_3982_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3992_ = v_expectedType_x3f_3982_;
v_isShared_3993_ = v_isSharedCheck_4002_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_val_3990_);
lean_dec(v_expectedType_x3f_3982_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4002_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3994_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1, &l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1);
v___x_3995_ = l_Lean_Expr_app___override(v___x_3994_, v_val_3990_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_3995_);
v___x_3997_ = v___x_3992_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3999_; 
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 1, v___x_3997_);
lean_ctor_set(v___x_3984_, 0, v___f_3986_);
v___x_3999_ = v___x_3984_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___f_3986_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v___x_3997_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instList(lean_object* v_00_u03b1_4004_, lean_object* v_inst_4005_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v_inst_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(lean_object* v_inst_4007_){
_start:
{
lean_object* v_evalExpr_4008_; lean_object* v_expectedType_x3f_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4030_; 
v_evalExpr_4008_ = lean_ctor_get(v_inst_4007_, 0);
v_expectedType_x3f_4009_ = lean_ctor_get(v_inst_4007_, 1);
v_isSharedCheck_4030_ = !lean_is_exclusive(v_inst_4007_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4011_ = v_inst_4007_;
v_isShared_4012_ = v_isSharedCheck_4030_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_expectedType_x3f_4009_);
lean_inc(v_evalExpr_4008_);
lean_dec(v_inst_4007_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4030_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_alloc_closure((void*)(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed), 8, 2);
lean_closure_set(v___x_4013_, 0, lean_box(0));
lean_closure_set(v___x_4013_, 1, v_evalExpr_4008_);
if (lean_obj_tag(v_expectedType_x3f_4009_) == 0)
{
lean_object* v___x_4015_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v___x_4013_);
v___x_4015_ = v___x_4011_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4016_, 1, v_expectedType_x3f_4009_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
else
{
lean_object* v_val_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4029_; 
v_val_4017_ = lean_ctor_get(v_expectedType_x3f_4009_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v_expectedType_x3f_4009_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4019_ = v_expectedType_x3f_4009_;
v_isShared_4020_ = v_isSharedCheck_4029_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_val_4017_);
lean_dec(v_expectedType_x3f_4009_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4029_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4021_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2, &l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once, _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2);
v___x_4022_ = l_Lean_Expr_app___override(v___x_4021_, v_val_4017_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 0, v___x_4022_);
v___x_4024_ = v___x_4019_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
lean_object* v___x_4026_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 1, v___x_4024_);
lean_ctor_set(v___x_4011_, 0, v___x_4013_);
v___x_4026_ = v___x_4011_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4013_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v___x_4024_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instArray(lean_object* v_00_u03b1_4031_, lean_object* v_inst_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(v_inst_4032_);
return v___x_4033_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_ConfigEval_EvalTerm_instBool = _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instBool);
l_Lean_Elab_ConfigEval_EvalTerm_instNat = _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instNat);
l_Lean_Elab_ConfigEval_EvalTerm_instInt = _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instInt);
l_Lean_Elab_ConfigEval_EvalTerm_instString = _init_l_Lean_Elab_ConfigEval_EvalTerm_instString();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instString);
l_Lean_Elab_ConfigEval_EvalTerm_instName = _init_l_Lean_Elab_ConfigEval_EvalTerm_instName();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instName);
l_Lean_Elab_ConfigEval_EvalTerm_instDataValue = _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue);
l_Lean_Elab_ConfigEval_EvalExpr_instBool = _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instBool);
l_Lean_Elab_ConfigEval_EvalExpr_instNat = _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instNat);
l_Lean_Elab_ConfigEval_EvalExpr_instInt = _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instInt);
l_Lean_Elab_ConfigEval_EvalExpr_instString = _init_l_Lean_Elab_ConfigEval_EvalExpr_instString();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instString);
l_Lean_Elab_ConfigEval_EvalExpr_instName = _init_l_Lean_Elab_ConfigEval_EvalExpr_instName();
lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instName);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
