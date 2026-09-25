// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Cases
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.MGoal public import Std.Tactic.Do.Syntax import Lean.Elab.Tactic.Do.ProofMode.Pure import Lean.Elab.Tactic.Do.ProofMode.Focus import Lean.Elab.Tactic.Do.ProofMode.Basic
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_mul(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__0_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 187, 99, 122, 205, 56, 35, 106)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__3_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 222, 238, 124, 44, 25, 111, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__5_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__6_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__8_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__10_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__11_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__12_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 162, 5, 152, 35, 161, 128, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Cases"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__14_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 146, 40, 210, 100, 26, 188, 244)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__16_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(157, 47, 53, 92, 44, 87, 203, 83)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__17_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 242, 250, 200, 153, 102, 94, 106)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__18_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 189, 124, 77, 205, 184, 175, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__19_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 88, 5, 221, 161, 161, 158, 230)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__20_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 208, 140, 23, 157, 48, 219, 108)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__21_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 80, 168, 14, 14, 136, 83, 231)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__22_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__23_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 215, 139, 75, 201, 47, 183, 17)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__24_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__25_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 158, 105, 169, 239, 197, 90, 65)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__26_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 128, 16, 18, 221, 168, 137, 246)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__27_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 221, 139, 80, 206, 21, 33, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__28_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(227, 233, 100, 251, 113, 139, 68, 36)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__29_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 128, 35, 29, 109, 6, 117, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__30_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 128, 255, 187, 121, 29, 216, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__31_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 186, 110, 64, 107, 50, 144, 42)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__32_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(723085142) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 61, 101, 95, 10, 175, 53, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__33_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__34_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 238, 205, 38, 187, 61, 119, 254)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__35_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__36_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 34, 142, 28, 152, 50, 197, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__37_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(122, 150, 214, 160, 180, 105, 176, 72)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bientails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(201, 51, 221, 5, 242, 131, 169, 118)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 95, 37, 108, 69, 205, 235, 200)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "IsAnd"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(244, 83, 223, 78, 97, 64, 238, 46)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "to_and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(244, 83, 223, 78, 97, 64, 238, 46)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(151, 250, 181, 158, 145, 194, 213, 0)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "add_goal"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 144, 153, 201, 175, 133, 231, 95)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Internal error: Hypotheses not a conjunction "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exists"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 199, 194, 26, 176, 147, 16, 83)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Not an existential quantifier "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "and_1"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 17, 228, 163, 140, 254, 212, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "IsPure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(237, 27, 197, 114, 200, 2, 153, 253)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 195, 94, 67, 62, 251, 248, 42)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clear"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 45, 21, 8, 254, 99, 220, 141)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "and_2"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 129, 169, 148, 64, 164, 21, 218)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "and_3"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(192, 254, 223, 142, 199, 149, 90, 110)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(131, 147, 17, 85, 137, 95, 149, 65)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Neither a conjunction nor an existential quantifier "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "cannot further destruct a term after moving it to the Lean context"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(114, 97, 84, 180, 109, 220, 63, 60)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Not a disjunction "};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "and_or_elim_r"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(141, 175, 37, 92, 202, 198, 164, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value;
static const lean_ctor_object l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1 = (const lean_object*)&l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1_value;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mcases"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 192, 12, 149, 146, 251, 197, 23)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMCases"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__7_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__9_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__13_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 109, 55, 23, 237, 161, 174, 103)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_95_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__4_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_96_ = 0;
v___x_97_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__38_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_98_ = l_Lean_registerTraceClass(v___x_95_, v___x_96_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2____boxed(lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(lean_object* v_u_130_, lean_object* v_00_u03c3s_131_, lean_object* v_H_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___y_139_; uint8_t v___y_140_; lean_object* v_a_145_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Lean_Expr_consumeMData(v_H_132_);
v___x_149_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v___x_148_);
lean_dec_ref(v___x_148_);
if (lean_obj_tag(v___x_149_) == 1)
{
lean_object* v_val_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_189_; 
v_val_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_189_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_189_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_val_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_189_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v_snd_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_187_; 
v_snd_154_ = lean_ctor_get(v_val_150_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_val_150_);
if (v_isSharedCheck_187_ == 0)
{
lean_object* v_unused_188_; 
v_unused_188_ = lean_ctor_get(v_val_150_, 0);
lean_dec(v_unused_188_);
v___x_156_ = v_val_150_;
v_isShared_157_ = v_isSharedCheck_187_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_snd_154_);
lean_dec(v_val_150_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_187_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v_snd_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_185_; 
v_snd_158_ = lean_ctor_get(v_snd_154_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_snd_154_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; 
v_unused_186_ = lean_ctor_get(v_snd_154_, 0);
lean_dec(v_unused_186_);
v___x_160_ = v_snd_154_;
v_isShared_161_ = v_isSharedCheck_185_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_snd_158_);
lean_dec(v_snd_154_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_185_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_184_; 
v_fst_162_ = lean_ctor_get(v_snd_158_, 0);
v_snd_163_ = lean_ctor_get(v_snd_158_, 1);
v_isSharedCheck_184_ = !lean_is_exclusive(v_snd_158_);
if (v_isSharedCheck_184_ == 0)
{
v___x_165_ = v_snd_158_;
v_isShared_166_ = v_isSharedCheck_184_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_snd_163_);
lean_inc(v_fst_162_);
lean_dec(v_snd_158_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_184_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_167_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__4));
v___x_168_ = lean_box(0);
if (v_isShared_157_ == 0)
{
lean_ctor_set_tag(v___x_156_, 1);
lean_ctor_set(v___x_156_, 1, v___x_168_);
lean_ctor_set(v___x_156_, 0, v_u_130_);
v___x_170_ = v___x_156_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_u_130_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_183_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = l_Lean_mkConst(v___x_167_, v___x_170_);
v___x_172_ = l_Lean_mkAppB(v___x_171_, v_00_u03c3s_131_, v_H_132_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 1, v___x_172_);
lean_ctor_set(v___x_165_, 0, v_snd_163_);
v___x_174_ = v___x_165_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_snd_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_182_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_174_);
lean_ctor_set(v___x_160_, 0, v_fst_162_);
v___x_176_ = v___x_160_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_fst_162_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_181_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_176_);
v___x_178_ = v___x_152_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
return v___x_179_;
}
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
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v___x_149_);
v___x_190_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__5));
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v_u_130_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
lean_inc_ref(v___x_192_);
v___x_193_ = l_Lean_mkConst(v___x_190_, v___x_192_);
lean_inc_ref(v_00_u03c3s_131_);
v___x_194_ = l_Lean_Expr_app___override(v___x_193_, v_00_u03c3s_131_);
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
v___x_196_ = 0;
v___x_197_ = lean_box(0);
lean_inc_ref(v___x_195_);
v___x_198_ = l_Lean_Meta_mkFreshExprMVar(v___x_195_, v___x_196_, v___x_197_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref_known(v___x_198_, 1);
v___x_200_ = l_Lean_Meta_mkFreshExprMVar(v___x_195_, v___x_196_, v___x_197_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_227_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_227_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_227_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_227_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_205_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__7));
lean_inc_ref(v___x_192_);
v___x_206_ = l_Lean_mkConst(v___x_205_, v___x_192_);
lean_inc(v_a_201_);
lean_inc(v_a_199_);
lean_inc_ref(v_H_132_);
lean_inc_ref(v_00_u03c3s_131_);
v___x_207_ = l_Lean_mkApp4(v___x_206_, v_00_u03c3s_131_, v_H_132_, v_a_199_, v_a_201_);
v___x_208_ = lean_box(0);
v___x_209_ = l_Lean_Meta_synthInstance(v___x_207_, v___x_208_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_225_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_225_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_225_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_214_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__9));
v___x_215_ = l_Lean_mkConst(v___x_214_, v___x_192_);
lean_inc(v_a_201_);
lean_inc(v_a_199_);
v___x_216_ = l_Lean_mkApp5(v___x_215_, v_00_u03c3s_131_, v_H_132_, v_a_199_, v_a_201_, v_a_210_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_a_201_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v_a_199_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 1);
lean_ctor_set(v___x_203_, 0, v___x_218_);
v___x_220_ = v___x_203_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_224_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_222_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_220_);
v___x_222_ = v___x_212_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_226_; 
lean_del_object(v___x_203_);
lean_dec(v_a_201_);
lean_dec(v_a_199_);
lean_dec_ref_known(v___x_192_, 2);
lean_dec_ref(v_H_132_);
lean_dec_ref(v_00_u03c3s_131_);
v_a_226_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_209_, 1);
v_a_145_ = v_a_226_;
goto v___jp_144_;
}
}
}
else
{
lean_object* v_a_228_; 
lean_dec(v_a_199_);
lean_dec_ref_known(v___x_192_, 2);
lean_dec_ref(v_H_132_);
lean_dec_ref(v_00_u03c3s_131_);
v_a_228_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_200_, 1);
v_a_145_ = v_a_228_;
goto v___jp_144_;
}
}
else
{
lean_object* v_a_229_; 
lean_dec_ref_known(v___x_195_, 1);
lean_dec_ref_known(v___x_192_, 2);
lean_dec_ref(v_H_132_);
lean_dec_ref(v_00_u03c3s_131_);
v_a_229_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_198_, 1);
v_a_145_ = v_a_229_;
goto v___jp_144_;
}
}
v___jp_138_:
{
if (v___y_140_ == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec_ref(v___y_139_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v___y_139_);
return v___x_143_;
}
}
v___jp_144_:
{
uint8_t v___x_146_; 
v___x_146_ = l_Lean_Exception_isInterrupt(v_a_145_);
if (v___x_146_ == 0)
{
uint8_t v___x_147_; 
lean_inc_ref(v_a_145_);
v___x_147_ = l_Lean_Exception_isRuntime(v_a_145_);
v___y_139_ = v_a_145_;
v___y_140_ = v___x_147_;
goto v___jp_138_;
}
else
{
v___y_139_ = v_a_145_;
v___y_140_ = v___x_146_;
goto v___jp_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___boxed(lean_object* v_u_230_, lean_object* v_00_u03c3s_231_, lean_object* v_H_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_230_, v_00_u03c3s_231_, v_H_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(lean_object* v_u_247_, lean_object* v_goals_248_, lean_object* v_00_u03c3s_249_, lean_object* v_T_250_, lean_object* v_Q_251_, lean_object* v_H_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v___x_258_; lean_object* v_fst_259_; lean_object* v_snd_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_300_; 
lean_inc_ref(v_H_252_);
lean_inc_ref(v_Q_251_);
lean_inc_ref(v_00_u03c3s_249_);
lean_inc(v_u_247_);
v___x_258_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_247_, v_00_u03c3s_249_, v_Q_251_, v_H_252_);
v_fst_259_ = lean_ctor_get(v___x_258_, 0);
v_snd_260_ = lean_ctor_get(v___x_258_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_258_);
if (v_isSharedCheck_300_ == 0)
{
v___x_262_ = v___x_258_;
v_isShared_263_ = v_isSharedCheck_300_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_snd_260_);
lean_inc(v_fst_259_);
lean_dec(v___x_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_300_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_goal_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
lean_inc_ref(v_T_250_);
lean_inc(v_fst_259_);
lean_inc_ref(v_00_u03c3s_249_);
lean_inc(v_u_247_);
v_goal_264_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_goal_264_, 0, v_u_247_);
lean_ctor_set(v_goal_264_, 1, v_00_u03c3s_249_);
lean_ctor_set(v_goal_264_, 2, v_fst_259_);
lean_ctor_set(v_goal_264_, 3, v_T_250_);
v___x_265_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_264_);
v___x_266_ = lean_box(0);
v___x_267_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_265_, v___x_266_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_291_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_291_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_291_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_291_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_272_ = lean_st_ref_take(v_goals_248_);
v___x_273_ = l_Lean_Expr_mvarId_x21(v_a_268_);
v___x_274_ = lean_array_push(v___x_272_, v___x_273_);
v___x_275_ = lean_st_ref_put(v_goals_248_, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___closed__1));
v___x_277_ = lean_box(0);
lean_inc_n(v_u_247_, 2);
v___x_278_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_278_, 0, v_u_247_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_mkConst(v___x_276_, v___x_278_);
lean_inc_ref(v_T_250_);
lean_inc_ref(v_H_252_);
lean_inc_ref(v_Q_251_);
lean_inc_ref_n(v_00_u03c3s_249_, 2);
v___x_280_ = l_Lean_mkApp7(v___x_279_, v_00_u03c3s_249_, v_fst_259_, v_Q_251_, v_H_252_, v_T_250_, v_snd_260_, v_a_268_);
v___x_281_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_247_, v_00_u03c3s_249_, v_Q_251_, v_H_252_);
v___x_282_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_282_, 0, v_u_247_);
lean_ctor_set(v___x_282_, 1, v_00_u03c3s_249_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
lean_ctor_set(v___x_282_, 3, v_T_250_);
v___x_283_ = lean_box(0);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_280_);
lean_ctor_set(v___x_262_, 0, v___x_282_);
v___x_285_ = v___x_262_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_280_);
v___x_285_ = v_reuseFailAlloc_290_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_283_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_286_);
v___x_288_ = v___x_270_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_del_object(v___x_262_);
lean_dec(v_snd_260_);
lean_dec(v_fst_259_);
lean_dec_ref(v_H_252_);
lean_dec_ref(v_Q_251_);
lean_dec_ref(v_T_250_);
lean_dec_ref(v_00_u03c3s_249_);
lean_dec(v_u_247_);
v_a_292_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_267_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_267_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed(lean_object* v_u_301_, lean_object* v_goals_302_, lean_object* v_00_u03c3s_303_, lean_object* v_T_304_, lean_object* v_Q_305_, lean_object* v_H_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal(v_u_301_, v_goals_302_, v_00_u03c3s_303_, v_T_304_, v_Q_305_, v_H_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_goals_302_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(lean_object* v_msgData_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___x_319_; lean_object* v_env_320_; lean_object* v___x_321_; lean_object* v_toCold_322_; lean_object* v_mctx_323_; lean_object* v_lctx_324_; lean_object* v_options_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_319_ = lean_st_ref_get(v___y_317_);
v_env_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_env_320_);
lean_dec(v___x_319_);
v___x_321_ = lean_st_ref_get(v___y_315_);
v_toCold_322_ = lean_ctor_get(v___y_316_, 0);
v_mctx_323_ = lean_ctor_get(v___x_321_, 0);
lean_inc_ref(v_mctx_323_);
lean_dec(v___x_321_);
v_lctx_324_ = lean_ctor_get(v___y_314_, 2);
v_options_325_ = lean_ctor_get(v_toCold_322_, 2);
lean_inc_ref(v_options_325_);
lean_inc_ref(v_lctx_324_);
v___x_326_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_326_, 0, v_env_320_);
lean_ctor_set(v___x_326_, 1, v_mctx_323_);
lean_ctor_set(v___x_326_, 2, v_lctx_324_);
lean_ctor_set(v___x_326_, 3, v_options_325_);
v___x_327_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_msgData_313_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(lean_object* v_msgData_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msgData_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(lean_object* v_msg_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_ref_342_; lean_object* v___x_343_; lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_352_; 
v_ref_342_ = lean_ctor_get(v___y_339_, 2);
v___x_343_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_352_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_352_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_352_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v___x_350_; 
lean_inc(v_ref_342_);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v_ref_342_);
lean_ctor_set(v___x_348_, 1, v_a_344_);
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 1);
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg___boxed(lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_359_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(lean_object* v_goal_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_hyps_369_; lean_object* v___x_370_; 
v_hyps_369_ = lean_ctor_get(v_goal_363_, 2);
lean_inc_ref(v_hyps_369_);
lean_dec_ref(v_goal_363_);
v___x_370_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_369_);
if (lean_obj_tag(v___x_370_) == 1)
{
lean_object* v_val_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_380_; 
lean_dec_ref(v_hyps_369_);
v_val_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_380_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_380_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_val_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_380_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_snd_375_; lean_object* v_snd_376_; lean_object* v___x_378_; 
v_snd_375_ = lean_ctor_get(v_val_371_, 1);
lean_inc(v_snd_375_);
lean_dec(v_val_371_);
v_snd_376_ = lean_ctor_get(v_snd_375_, 1);
lean_inc(v_snd_376_);
lean_dec(v_snd_375_);
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 0);
lean_ctor_set(v___x_373_, 0, v_snd_376_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_snd_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
lean_dec(v___x_370_);
v___x_381_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1, &l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1);
v___x_382_ = l_Lean_MessageData_ofExpr(v_hyps_369_);
v___x_383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_381_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_383_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___boxed(lean_object* v_goal_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_goal_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(lean_object* v_00_u03b1_392_, lean_object* v_msg_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(lean_object* v_00_u03b1_400_, lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(v_00_u03b1_400_, v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(lean_object* v___x_408_, lean_object* v_snd_409_, lean_object* v_k_410_, uint8_t v___x_411_, lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v___x_416_, lean_object* v___x_417_, lean_object* v_H_418_, lean_object* v_x_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_lctx_425_; lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; 
v_lctx_425_ = lean_ctor_get(v___y_420_, 2);
lean_inc_ref(v___x_408_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_408_);
v___x_427_ = 0;
lean_inc_ref(v_x_419_);
lean_inc_ref(v_lctx_425_);
v___x_428_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_409_, v_lctx_425_, v_x_419_, v___x_426_, v___x_427_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v___x_429_; 
lean_dec_ref_known(v___x_428_, 1);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc(v___y_421_);
lean_inc_ref(v___y_420_);
lean_inc_ref(v_x_419_);
v___x_429_ = lean_apply_6(v_k_410_, v_x_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, lean_box(0));
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v_snd_431_; lean_object* v_fst_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_517_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v_snd_431_ = lean_ctor_get(v_a_430_, 1);
v_fst_432_ = lean_ctor_get(v_a_430_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_430_);
if (v_isSharedCheck_517_ == 0)
{
v___x_434_ = v_a_430_;
v_isShared_435_ = v_isSharedCheck_517_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_snd_431_);
lean_inc(v_fst_432_);
lean_dec(v_a_430_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_517_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_fst_436_; lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_516_; 
v_fst_436_ = lean_ctor_get(v_snd_431_, 0);
v_snd_437_ = lean_ctor_get(v_snd_431_, 1);
v_isSharedCheck_516_ = !lean_is_exclusive(v_snd_431_);
if (v_isSharedCheck_516_ == 0)
{
v___x_439_ = v_snd_431_;
v_isShared_440_ = v_isSharedCheck_516_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_inc(v_fst_436_);
lean_dec(v_snd_431_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_516_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; 
lean_inc(v_fst_436_);
v___x_441_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_436_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v_fst_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_506_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v_fst_443_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_a_442_, 1);
lean_dec(v_unused_507_);
v___x_445_ = v_a_442_;
v_isShared_446_ = v_isSharedCheck_506_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_fst_443_);
lean_dec(v_a_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_506_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; 
lean_inc_ref(v___x_408_);
v___x_447_ = l_Lean_Meta_getLevel(v___x_408_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_mk_empty_array_with_capacity(v___x_449_);
v___x_451_ = lean_array_push(v___x_450_, v_x_419_);
v___x_452_ = 1;
v___x_453_ = l_Lean_Meta_mkLambdaFVars(v___x_451_, v_snd_437_, v___x_427_, v___x_411_, v___x_427_, v___x_411_, v___x_452_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec_ref(v___x_451_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_489_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_489_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_489_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_489_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_u_458_; lean_object* v_00_u03c3s_459_; lean_object* v_target_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_487_; 
v_u_458_ = lean_ctor_get(v_fst_436_, 0);
v_00_u03c3s_459_ = lean_ctor_get(v_fst_436_, 1);
v_target_460_ = lean_ctor_get(v_fst_436_, 3);
v_isSharedCheck_487_ = !lean_is_exclusive(v_fst_436_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; 
v_unused_488_ = lean_ctor_get(v_fst_436_, 2);
lean_dec(v_unused_488_);
v___x_462_ = v_fst_436_;
v_isShared_463_ = v_isSharedCheck_487_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_target_460_);
lean_inc(v_00_u03c3s_459_);
lean_inc(v_u_458_);
lean_dec(v_fst_436_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_487_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_464_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_466_ = l_Lean_Name_mkStr6(v___x_412_, v___x_413_, v___x_414_, v___x_464_, v___x_465_, v___x_415_);
v___x_467_ = lean_box(0);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 1);
lean_ctor_set(v___x_434_, 1, v___x_467_);
lean_ctor_set(v___x_434_, 0, v_a_448_);
v___x_469_ = v___x_434_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_448_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_486_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
lean_inc_n(v_u_458_, 2);
v___x_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_470_, 0, v_u_458_);
lean_ctor_set(v___x_470_, 1, v___x_469_);
v___x_471_ = l_Lean_mkConst(v___x_466_, v___x_470_);
lean_inc_ref(v_target_460_);
lean_inc(v_fst_443_);
lean_inc_ref(v___x_416_);
v___x_472_ = l_Lean_mkApp6(v___x_471_, v___x_416_, v___x_408_, v_fst_443_, v___x_417_, v_target_460_, v_a_454_);
v___x_473_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_458_, v___x_416_, v_fst_443_, v_H_418_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 2, v___x_473_);
v___x_475_ = v___x_462_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_u_458_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_00_u03c3s_459_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_target_460_);
v___x_475_ = v_reuseFailAlloc_485_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_472_);
lean_ctor_set(v___x_445_, 0, v___x_475_);
v___x_477_ = v___x_445_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_472_);
v___x_477_ = v_reuseFailAlloc_484_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_479_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v___x_477_);
lean_ctor_set(v___x_439_, 0, v_fst_432_);
v___x_479_ = v___x_439_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_fst_432_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_483_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_479_);
v___x_481_ = v___x_456_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
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
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_a_448_);
lean_del_object(v___x_445_);
lean_dec(v_fst_443_);
lean_del_object(v___x_439_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_dec_ref(v_H_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_408_);
v_a_490_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_453_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_453_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_del_object(v___x_445_);
lean_dec(v_fst_443_);
lean_del_object(v___x_439_);
lean_dec(v_snd_437_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_dec_ref(v_x_419_);
lean_dec_ref(v_H_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_408_);
v_a_498_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_447_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_447_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_del_object(v___x_439_);
lean_dec(v_snd_437_);
lean_dec(v_fst_436_);
lean_del_object(v___x_434_);
lean_dec(v_fst_432_);
lean_dec_ref(v_x_419_);
lean_dec_ref(v_H_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_408_);
v_a_508_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_441_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_441_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_419_);
lean_dec_ref(v_H_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_408_);
return v___x_429_;
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_x_419_);
lean_dec_ref(v_H_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v_k_410_);
lean_dec_ref(v___x_408_);
v_a_518_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_428_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_428_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_526_ = _args[0];
lean_object* v_snd_527_ = _args[1];
lean_object* v_k_528_ = _args[2];
lean_object* v___x_529_ = _args[3];
lean_object* v___x_530_ = _args[4];
lean_object* v___x_531_ = _args[5];
lean_object* v___x_532_ = _args[6];
lean_object* v___x_533_ = _args[7];
lean_object* v___x_534_ = _args[8];
lean_object* v___x_535_ = _args[9];
lean_object* v_H_536_ = _args[10];
lean_object* v_x_537_ = _args[11];
lean_object* v___y_538_ = _args[12];
lean_object* v___y_539_ = _args[13];
lean_object* v___y_540_ = _args[14];
lean_object* v___y_541_ = _args[15];
lean_object* v___y_542_ = _args[16];
_start:
{
uint8_t v___x_2309__boxed_543_; lean_object* v_res_544_; 
v___x_2309__boxed_543_ = lean_unbox(v___x_529_);
v_res_544_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(v___x_526_, v_snd_527_, v_k_528_, v___x_2309__boxed_543_, v___x_530_, v___x_531_, v___x_532_, v___x_533_, v___x_534_, v___x_535_, v_H_536_, v_x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(lean_object* v_k_545_, lean_object* v_b_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v___x_552_; 
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
v___x_552_ = lean_apply_6(v_k_545_, v_b_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, lean_box(0));
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_553_, lean_object* v_b_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(v_k_553_, v_b_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(lean_object* v_name_561_, uint8_t v_bi_562_, lean_object* v_type_563_, lean_object* v_k_564_, uint8_t v_kind_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___f_571_; lean_object* v___x_572_; 
v___f_571_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_571_, 0, v_k_564_);
v___x_572_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_561_, v_bi_562_, v_type_563_, v___f_571_, v_kind_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_572_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_572_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___boxed(lean_object* v_name_589_, lean_object* v_bi_590_, lean_object* v_type_591_, lean_object* v_k_592_, lean_object* v_kind_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
uint8_t v_bi_boxed_599_; uint8_t v_kind_boxed_600_; lean_object* v_res_601_; 
v_bi_boxed_599_ = lean_unbox(v_bi_590_);
v_kind_boxed_600_ = lean_unbox(v_kind_593_);
v_res_601_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_589_, v_bi_boxed_599_, v_type_591_, v_k_592_, v_kind_boxed_600_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(lean_object* v_name_602_, lean_object* v_type_603_, lean_object* v_k_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
uint8_t v___x_610_; uint8_t v___x_611_; lean_object* v___x_612_; 
v___x_610_ = 0;
v___x_611_ = 0;
v___x_612_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_602_, v___x_610_, v_type_603_, v_k_604_, v___x_611_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(lean_object* v_name_613_, lean_object* v_type_614_, lean_object* v_k_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_613_, v_type_614_, v_k_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2));
v___x_630_ = l_Lean_stringToMessageData(v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(lean_object* v_H_631_, lean_object* v_name_632_, lean_object* v_k_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_639_ = l_Lean_Expr_consumeMData(v_H_631_);
v___x_640_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_643_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0));
v___x_644_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_645_ = lean_unsigned_to_nat(3u);
v___x_646_ = l_Lean_Expr_isAppOfArity(v___x_639_, v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
lean_dec_ref(v___x_639_);
lean_dec_ref(v_k_633_);
lean_dec(v_name_632_);
v___x_647_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3);
v___x_648_ = l_Lean_MessageData_ofExpr(v_H_631_);
v___x_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_649_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_650_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = l_Lean_Expr_appFn_x21(v___x_639_);
v___x_652_ = l_Lean_Expr_appFn_x21(v___x_651_);
v___x_653_ = l_Lean_Expr_appArg_x21(v___x_652_);
lean_dec_ref(v___x_652_);
v___x_654_ = l_Lean_Expr_appArg_x21(v___x_651_);
lean_dec_ref(v___x_651_);
v___x_655_ = l_Lean_Expr_appArg_x21(v___x_639_);
lean_dec_ref(v___x_639_);
v___x_656_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_632_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v_fst_658_; lean_object* v_snd_659_; lean_object* v___x_660_; lean_object* v___f_661_; lean_object* v___x_662_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v_fst_658_ = lean_ctor_get(v_a_657_, 0);
lean_inc(v_fst_658_);
v_snd_659_ = lean_ctor_get(v_a_657_, 1);
lean_inc(v_snd_659_);
lean_dec(v_a_657_);
v___x_660_ = lean_box(v___x_646_);
lean_inc_ref(v___x_653_);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed), 17, 11);
lean_closure_set(v___f_661_, 0, v___x_653_);
lean_closure_set(v___f_661_, 1, v_snd_659_);
lean_closure_set(v___f_661_, 2, v_k_633_);
lean_closure_set(v___f_661_, 3, v___x_660_);
lean_closure_set(v___f_661_, 4, v___x_640_);
lean_closure_set(v___f_661_, 5, v___x_641_);
lean_closure_set(v___f_661_, 6, v___x_642_);
lean_closure_set(v___f_661_, 7, v___x_643_);
lean_closure_set(v___f_661_, 8, v___x_654_);
lean_closure_set(v___f_661_, 9, v___x_655_);
lean_closure_set(v___f_661_, 10, v_H_631_);
v___x_662_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_658_, v___x_653_, v___f_661_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_662_;
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v___x_655_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v_k_633_);
lean_dec_ref(v_H_631_);
v_a_663_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_656_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_656_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___boxed(lean_object* v_H_671_, lean_object* v_name_672_, lean_object* v_k_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_671_, v_name_672_, v_k_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(lean_object* v_00_u03b1_680_, lean_object* v_H_681_, lean_object* v_name_682_, lean_object* v_k_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_681_, v_name_682_, v_k_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___boxed(lean_object* v_00_u03b1_690_, lean_object* v_H_691_, lean_object* v_name_692_, lean_object* v_k_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(v_00_u03b1_690_, v_H_691_, v_name_692_, v_k_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(lean_object* v_00_u03b1_700_, lean_object* v_name_701_, uint8_t v_bi_702_, lean_object* v_type_703_, lean_object* v_k_704_, uint8_t v_kind_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_701_, v_bi_702_, v_type_703_, v_k_704_, v_kind_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(lean_object* v_00_u03b1_712_, lean_object* v_name_713_, lean_object* v_bi_714_, lean_object* v_type_715_, lean_object* v_k_716_, lean_object* v_kind_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
uint8_t v_bi_boxed_723_; uint8_t v_kind_boxed_724_; lean_object* v_res_725_; 
v_bi_boxed_723_ = lean_unbox(v_bi_714_);
v_kind_boxed_724_ = lean_unbox(v_kind_717_);
v_res_725_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(v_00_u03b1_712_, v_name_713_, v_bi_boxed_723_, v_type_715_, v_k_716_, v_kind_boxed_724_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(lean_object* v_00_u03b1_726_, lean_object* v_name_727_, lean_object* v_type_728_, lean_object* v_k_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_727_, v_type_728_, v_k_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(lean_object* v_00_u03b1_736_, lean_object* v_name_737_, lean_object* v_type_738_, lean_object* v_k_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(v_00_u03b1_736_, v_name_737_, v_type_738_, v_k_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
return v_res_745_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_box(0);
v___x_747_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v___x_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg(){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(lean_object* v_00_u03b1_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(lean_object* v_00_u03b1_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(v_00_u03b1_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; lean_object* v_ngen_771_; lean_object* v_namePrefix_772_; lean_object* v_idx_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_803_; 
v___x_770_ = lean_st_ref_get(v___y_768_);
v_ngen_771_ = lean_ctor_get(v___x_770_, 2);
lean_inc_ref(v_ngen_771_);
lean_dec(v___x_770_);
v_namePrefix_772_ = lean_ctor_get(v_ngen_771_, 0);
v_idx_773_ = lean_ctor_get(v_ngen_771_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_ngen_771_);
if (v_isSharedCheck_803_ == 0)
{
v___x_775_ = v_ngen_771_;
v_isShared_776_ = v_isSharedCheck_803_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_idx_773_);
lean_inc(v_namePrefix_772_);
lean_dec(v_ngen_771_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_803_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_r_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
lean_inc(v_idx_773_);
lean_inc(v_namePrefix_772_);
v_r_777_ = l_Lean_Name_num___override(v_namePrefix_772_, v_idx_773_);
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = lean_nat_add(v_idx_773_, v___x_778_);
lean_dec(v_idx_773_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_779_);
v___x_781_ = v___x_775_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_namePrefix_772_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_802_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v_env_783_; lean_object* v_nextMacroScope_784_; lean_object* v_auxDeclNGen_785_; lean_object* v_traceState_786_; lean_object* v_cache_787_; lean_object* v_recordedDeps_788_; lean_object* v_messages_789_; lean_object* v_infoState_790_; lean_object* v_snapshotTasks_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_800_; 
v___x_782_ = lean_st_ref_take(v___y_768_);
v_env_783_ = lean_ctor_get(v___x_782_, 0);
v_nextMacroScope_784_ = lean_ctor_get(v___x_782_, 1);
v_auxDeclNGen_785_ = lean_ctor_get(v___x_782_, 3);
v_traceState_786_ = lean_ctor_get(v___x_782_, 4);
v_cache_787_ = lean_ctor_get(v___x_782_, 5);
v_recordedDeps_788_ = lean_ctor_get(v___x_782_, 6);
v_messages_789_ = lean_ctor_get(v___x_782_, 7);
v_infoState_790_ = lean_ctor_get(v___x_782_, 8);
v_snapshotTasks_791_ = lean_ctor_get(v___x_782_, 9);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_782_, 2);
lean_dec(v_unused_801_);
v___x_793_ = v___x_782_;
v_isShared_794_ = v_isSharedCheck_800_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_snapshotTasks_791_);
lean_inc(v_infoState_790_);
lean_inc(v_messages_789_);
lean_inc(v_recordedDeps_788_);
lean_inc(v_cache_787_);
lean_inc(v_traceState_786_);
lean_inc(v_auxDeclNGen_785_);
lean_inc(v_nextMacroScope_784_);
lean_inc(v_env_783_);
lean_dec(v___x_782_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_800_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 2, v___x_781_);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_env_783_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_nextMacroScope_784_);
lean_ctor_set(v_reuseFailAlloc_799_, 2, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_799_, 3, v_auxDeclNGen_785_);
lean_ctor_set(v_reuseFailAlloc_799_, 4, v_traceState_786_);
lean_ctor_set(v_reuseFailAlloc_799_, 5, v_cache_787_);
lean_ctor_set(v_reuseFailAlloc_799_, 6, v_recordedDeps_788_);
lean_ctor_set(v_reuseFailAlloc_799_, 7, v_messages_789_);
lean_ctor_set(v_reuseFailAlloc_799_, 8, v_infoState_790_);
lean_ctor_set(v_reuseFailAlloc_799_, 9, v_snapshotTasks_791_);
v___x_796_ = v_reuseFailAlloc_799_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_st_ref_put(v___y_768_, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v_r_777_);
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_804_);
lean_dec(v___y_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_810_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(lean_object* v_u_827_, lean_object* v_00_u03c3s_828_, lean_object* v_H_u2081_x27_829_, lean_object* v_k_830_, lean_object* v_H_u2082_x27_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v_fst_838_; lean_object* v_snd_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_917_; 
lean_inc_ref(v_H_u2082_x27_831_);
lean_inc_ref(v_H_u2081_x27_829_);
lean_inc_ref(v_00_u03c3s_828_);
lean_inc(v_u_827_);
v___x_837_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_827_, v_00_u03c3s_828_, v_H_u2081_x27_829_, v_H_u2082_x27_831_);
v_fst_838_ = lean_ctor_get(v___x_837_, 0);
v_snd_839_ = lean_ctor_get(v___x_837_, 1);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_917_ == 0)
{
v___x_841_ = v___x_837_;
v_isShared_842_ = v_isSharedCheck_917_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_snd_839_);
lean_inc(v_fst_838_);
lean_dec(v___x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_917_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; 
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc_ref(v___y_832_);
lean_inc(v_fst_838_);
v___x_843_ = lean_apply_6(v_k_830_, v_fst_838_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, lean_box(0));
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v_snd_845_; lean_object* v_fst_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_908_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v_snd_845_ = lean_ctor_get(v_a_844_, 1);
v_fst_846_ = lean_ctor_get(v_a_844_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_844_);
if (v_isSharedCheck_908_ == 0)
{
v___x_848_ = v_a_844_;
v_isShared_849_ = v_isSharedCheck_908_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_snd_845_);
lean_inc(v_fst_846_);
lean_dec(v_a_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_908_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_fst_850_; lean_object* v_snd_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_907_; 
v_fst_850_ = lean_ctor_get(v_snd_845_, 0);
v_snd_851_ = lean_ctor_get(v_snd_845_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_snd_845_);
if (v_isSharedCheck_907_ == 0)
{
v___x_853_ = v_snd_845_;
v_isShared_854_ = v_isSharedCheck_907_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snd_851_);
lean_inc(v_fst_850_);
lean_dec(v_snd_845_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_907_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; 
lean_inc(v_fst_850_);
v___x_855_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_850_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_898_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_898_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_898_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_898_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_fst_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_896_; 
v_fst_860_ = lean_ctor_get(v_a_856_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_a_856_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_a_856_, 1);
lean_dec(v_unused_897_);
v___x_862_ = v_a_856_;
v_isShared_863_ = v_isSharedCheck_896_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_fst_860_);
lean_dec(v_a_856_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_896_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_u_864_; lean_object* v_00_u03c3s_865_; lean_object* v_target_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_894_; 
v_u_864_ = lean_ctor_get(v_fst_850_, 0);
v_00_u03c3s_865_ = lean_ctor_get(v_fst_850_, 1);
v_target_866_ = lean_ctor_get(v_fst_850_, 3);
v_isSharedCheck_894_ = !lean_is_exclusive(v_fst_850_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_fst_850_, 2);
lean_dec(v_unused_895_);
v___x_868_ = v_fst_850_;
v_isShared_869_ = v_isSharedCheck_894_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_target_866_);
lean_inc(v_00_u03c3s_865_);
lean_inc(v_u_864_);
lean_dec(v_fst_850_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_894_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_870_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1));
v___x_871_ = lean_box(0);
lean_inc(v_u_827_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 1);
lean_ctor_set(v___x_841_, 1, v___x_871_);
lean_ctor_set(v___x_841_, 0, v_u_827_);
v___x_873_ = v___x_841_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_u_827_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_871_);
v___x_873_ = v_reuseFailAlloc_893_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_874_ = l_Lean_mkConst(v___x_870_, v___x_873_);
lean_inc_ref(v_target_866_);
lean_inc_ref(v_H_u2082_x27_831_);
lean_inc_ref(v_H_u2081_x27_829_);
lean_inc_n(v_fst_860_, 2);
lean_inc_ref_n(v_00_u03c3s_828_, 2);
v___x_875_ = l_Lean_mkApp8(v___x_874_, v_00_u03c3s_828_, v_fst_860_, v_H_u2081_x27_829_, v_H_u2082_x27_831_, v_fst_838_, v_target_866_, v_snd_839_, v_snd_851_);
lean_inc(v_u_827_);
v___x_876_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_827_, v_00_u03c3s_828_, v_fst_860_, v_H_u2081_x27_829_);
v___x_877_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_827_, v_00_u03c3s_828_, v___x_876_, v_H_u2082_x27_831_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 2, v___x_877_);
v___x_879_ = v___x_868_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_u_864_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_00_u03c3s_865_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_892_, 3, v_target_866_);
v___x_879_ = v_reuseFailAlloc_892_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v___x_881_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_fst_860_);
lean_ctor_set(v___x_862_, 0, v_fst_846_);
v___x_881_ = v___x_862_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_fst_846_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_fst_860_);
v___x_881_ = v_reuseFailAlloc_891_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_875_);
lean_ctor_set(v___x_853_, 0, v___x_879_);
v___x_883_ = v___x_853_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_875_);
v___x_883_ = v_reuseFailAlloc_890_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 1, v___x_883_);
lean_ctor_set(v___x_848_, 0, v___x_881_);
v___x_885_ = v___x_848_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_883_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_885_);
v___x_887_ = v___x_858_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
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
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_del_object(v___x_853_);
lean_dec(v_snd_851_);
lean_dec(v_fst_850_);
lean_del_object(v___x_848_);
lean_dec(v_fst_846_);
lean_del_object(v___x_841_);
lean_dec(v_snd_839_);
lean_dec(v_fst_838_);
lean_dec_ref(v_H_u2082_x27_831_);
lean_dec_ref(v_H_u2081_x27_829_);
lean_dec_ref(v_00_u03c3s_828_);
lean_dec(v_u_827_);
v_a_899_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_855_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_855_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_del_object(v___x_841_);
lean_dec(v_snd_839_);
lean_dec(v_fst_838_);
lean_dec_ref(v_H_u2082_x27_831_);
lean_dec_ref(v_H_u2081_x27_829_);
lean_dec_ref(v_00_u03c3s_828_);
lean_dec(v_u_827_);
v_a_909_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_843_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_843_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(lean_object* v_u_918_, lean_object* v_00_u03c3s_919_, lean_object* v_H_u2081_x27_920_, lean_object* v_k_921_, lean_object* v_H_u2082_x27_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(v_u_918_, v_00_u03c3s_919_, v_H_u2081_x27_920_, v_k_921_, v_H_u2082_x27_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(lean_object* v_a_931_, lean_object* v_snd_932_, lean_object* v_k_933_, lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v_00_u03c3s_939_, lean_object* v_hyp_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_h_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_lctx_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; 
v_lctx_949_ = lean_ctor_get(v___y_944_, 2);
lean_inc_ref(v_a_931_);
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v_a_931_);
v___x_951_ = 0;
lean_inc_ref(v_h_943_);
lean_inc_ref(v_lctx_949_);
v___x_952_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_932_, v_lctx_949_, v_h_943_, v___x_950_, v___x_951_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v___x_953_; 
lean_dec_ref_known(v___x_952_, 1);
lean_inc(v___y_947_);
lean_inc_ref(v___y_946_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
lean_inc_ref(v_h_943_);
lean_inc_ref(v_a_931_);
v___x_953_ = lean_apply_7(v_k_933_, v_a_931_, v_h_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, lean_box(0));
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v_snd_955_; lean_object* v_fst_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1011_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v_snd_955_ = lean_ctor_get(v_a_954_, 1);
v_fst_956_ = lean_ctor_get(v_a_954_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_954_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_958_ = v_a_954_;
v_isShared_959_ = v_isSharedCheck_1011_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_snd_955_);
lean_inc(v_fst_956_);
lean_dec(v_a_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1011_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1010_; 
v_fst_960_ = lean_ctor_get(v_snd_955_, 0);
v_snd_961_ = lean_ctor_get(v_snd_955_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_snd_955_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_963_ = v_snd_955_;
v_isShared_964_ = v_isSharedCheck_1010_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_snd_961_);
lean_inc(v_fst_960_);
lean_dec(v_snd_955_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1010_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = lean_mk_empty_array_with_capacity(v___x_965_);
v___x_967_ = lean_array_push(v___x_966_, v_h_943_);
v___x_968_ = 1;
v___x_969_ = 1;
v___x_970_ = l_Lean_Meta_mkLambdaFVars(v___x_967_, v_snd_961_, v___x_951_, v___x_968_, v___x_951_, v___x_968_, v___x_969_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec_ref(v___x_967_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_1001_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_1001_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_1001_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v_u_975_; lean_object* v_00_u03c3s_976_; lean_object* v_hyps_977_; lean_object* v_target_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1000_; 
v_u_975_ = lean_ctor_get(v_fst_960_, 0);
v_00_u03c3s_976_ = lean_ctor_get(v_fst_960_, 1);
v_hyps_977_ = lean_ctor_get(v_fst_960_, 2);
v_target_978_ = lean_ctor_get(v_fst_960_, 3);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_fst_960_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_980_ = v_fst_960_;
v_isShared_981_ = v_isSharedCheck_1000_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_target_978_);
lean_inc(v_hyps_977_);
lean_inc(v_00_u03c3s_976_);
lean_inc(v_u_975_);
lean_dec(v_fst_960_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1000_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_prf_986_; lean_object* v___x_987_; lean_object* v_goal_989_; 
v___x_982_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0));
v___x_983_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1));
v___x_984_ = l_Lean_Name_mkStr6(v___x_934_, v___x_935_, v___x_936_, v___x_937_, v___x_982_, v___x_983_);
v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_938_);
lean_inc_ref(v_target_978_);
lean_inc_ref(v_hyp_940_);
lean_inc_ref(v_hyps_977_);
lean_inc_ref(v_00_u03c3s_939_);
v_prf_986_ = l_Lean_mkApp7(v___x_985_, v_00_u03c3s_939_, v_hyps_977_, v_hyp_940_, v_target_978_, v_a_931_, v_a_941_, v_a_971_);
v___x_987_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_a_942_, v_00_u03c3s_939_, v_hyps_977_, v_hyp_940_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 2, v___x_987_);
v_goal_989_ = v___x_980_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_u_975_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_00_u03c3s_976_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_target_978_);
v_goal_989_ = v_reuseFailAlloc_999_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_991_; 
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v_prf_986_);
lean_ctor_set(v___x_963_, 0, v_goal_989_);
v___x_991_ = v___x_963_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_goal_989_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_prf_986_);
v___x_991_ = v_reuseFailAlloc_998_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___x_991_);
v___x_993_ = v___x_958_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_fst_956_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_993_);
v___x_995_ = v___x_973_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_del_object(v___x_963_);
lean_dec(v_fst_960_);
lean_del_object(v___x_958_);
lean_dec(v_fst_956_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec_ref(v_hyp_940_);
lean_dec_ref(v_00_u03c3s_939_);
lean_dec(v___x_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v_a_931_);
v_a_1002_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_970_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_970_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec_ref(v_hyp_940_);
lean_dec_ref(v_00_u03c3s_939_);
lean_dec(v___x_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v_a_931_);
return v___x_953_;
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_h_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec_ref(v_hyp_940_);
lean_dec_ref(v_00_u03c3s_939_);
lean_dec(v___x_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v_k_933_);
lean_dec_ref(v_a_931_);
v_a_1012_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_952_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_952_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_1020_ = _args[0];
lean_object* v_snd_1021_ = _args[1];
lean_object* v_k_1022_ = _args[2];
lean_object* v___x_1023_ = _args[3];
lean_object* v___x_1024_ = _args[4];
lean_object* v___x_1025_ = _args[5];
lean_object* v___x_1026_ = _args[6];
lean_object* v___x_1027_ = _args[7];
lean_object* v_00_u03c3s_1028_ = _args[8];
lean_object* v_hyp_1029_ = _args[9];
lean_object* v_a_1030_ = _args[10];
lean_object* v_a_1031_ = _args[11];
lean_object* v_h_1032_ = _args[12];
lean_object* v___y_1033_ = _args[13];
lean_object* v___y_1034_ = _args[14];
lean_object* v___y_1035_ = _args[15];
lean_object* v___y_1036_ = _args[16];
lean_object* v___y_1037_ = _args[17];
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_1020_, v_snd_1021_, v_k_1022_, v___x_1023_, v___x_1024_, v___x_1025_, v___x_1026_, v___x_1027_, v_00_u03c3s_1028_, v_hyp_1029_, v_a_1030_, v_a_1031_, v_h_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Lean_mkSort(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0);
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object* v_00_u03c3s_1050_, lean_object* v_hyp_1051_, lean_object* v_name_1052_, lean_object* v_k_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1062_ = 0;
v___x_1063_ = lean_box(0);
v___x_1064_ = l_Lean_Meta_mkFreshExprMVar(v___x_1061_, v___x_1062_, v___x_1063_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_n(v_a_1065_, 2);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_1067_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_1069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1071_ = lean_box(0);
lean_inc(v_a_1060_);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_a_1060_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
lean_inc_ref(v___x_1072_);
v___x_1073_ = l_Lean_mkConst(v___x_1070_, v___x_1072_);
lean_inc_ref(v_hyp_1051_);
lean_inc_ref(v_00_u03c3s_1050_);
v___x_1074_ = l_Lean_mkApp3(v___x_1073_, v_00_u03c3s_1050_, v_hyp_1051_, v_a_1065_);
v___x_1075_ = lean_box(0);
v___x_1076_ = l_Lean_Meta_synthInstance(v___x_1074_, v___x_1075_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_1052_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v_fst_1080_; lean_object* v_snd_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v_fst_1080_ = lean_ctor_get(v_a_1079_, 0);
lean_inc(v_fst_1080_);
v_snd_1081_ = lean_ctor_get(v_a_1079_, 1);
lean_inc(v_snd_1081_);
lean_dec(v_a_1079_);
lean_inc(v_a_1065_);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1082_, 0, v_a_1065_);
lean_closure_set(v___f_1082_, 1, v_snd_1081_);
lean_closure_set(v___f_1082_, 2, v_k_1053_);
lean_closure_set(v___f_1082_, 3, v___x_1066_);
lean_closure_set(v___f_1082_, 4, v___x_1067_);
lean_closure_set(v___f_1082_, 5, v___x_1068_);
lean_closure_set(v___f_1082_, 6, v___x_1069_);
lean_closure_set(v___f_1082_, 7, v___x_1072_);
lean_closure_set(v___f_1082_, 8, v_00_u03c3s_1050_);
lean_closure_set(v___f_1082_, 9, v_hyp_1051_);
lean_closure_set(v___f_1082_, 10, v_a_1077_);
lean_closure_set(v___f_1082_, 11, v_a_1060_);
v___x_1083_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_1080_, v_a_1065_, v___f_1082_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1083_;
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_a_1077_);
lean_dec_ref_known(v___x_1072_, 2);
lean_dec(v_a_1065_);
lean_dec(v_a_1060_);
lean_dec_ref(v_k_1053_);
lean_dec_ref(v_hyp_1051_);
lean_dec_ref(v_00_u03c3s_1050_);
v_a_1084_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1078_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1078_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
lean_dec_ref_known(v___x_1072_, 2);
lean_dec(v_a_1065_);
lean_dec(v_a_1060_);
lean_dec_ref(v_k_1053_);
lean_dec(v_name_1052_);
lean_dec_ref(v_hyp_1051_);
lean_dec_ref(v_00_u03c3s_1050_);
v_a_1092_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1076_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1076_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_a_1060_);
lean_dec_ref(v_k_1053_);
lean_dec(v_name_1052_);
lean_dec_ref(v_hyp_1051_);
lean_dec_ref(v_00_u03c3s_1050_);
v_a_1100_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1064_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1064_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_k_1053_);
lean_dec(v_name_1052_);
lean_dec_ref(v_hyp_1051_);
lean_dec_ref(v_00_u03c3s_1050_);
v_a_1108_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1059_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1059_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object* v_00_u03c3s_1116_, lean_object* v_hyp_1117_, lean_object* v_name_1118_, lean_object* v_k_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1116_, v_hyp_1117_, v_name_1118_, v_k_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object* v_u_1134_, lean_object* v_00_u03c3s_1135_, lean_object* v_k_1136_, lean_object* v_x_1137_, lean_object* v___h_u03c6_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_H_x27_1144_; lean_object* v___x_1145_; 
lean_inc_ref(v_00_u03c3s_1135_);
lean_inc(v_u_1134_);
v_H_x27_1144_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1134_, v_00_u03c3s_1135_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
v___x_1145_ = lean_apply_6(v_k_1136_, v_H_x27_1144_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, lean_box(0));
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v_snd_1147_; lean_object* v_fst_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1205_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v_snd_1147_ = lean_ctor_get(v_a_1146_, 1);
v_fst_1148_ = lean_ctor_get(v_a_1146_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_a_1146_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1150_ = v_a_1146_;
v_isShared_1151_ = v_isSharedCheck_1205_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_snd_1147_);
lean_inc(v_fst_1148_);
lean_dec(v_a_1146_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1205_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1204_; 
v_fst_1152_ = lean_ctor_get(v_snd_1147_, 0);
v_snd_1153_ = lean_ctor_get(v_snd_1147_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_snd_1147_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1155_ = v_snd_1147_;
v_isShared_1156_ = v_isSharedCheck_1204_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_snd_1153_);
lean_inc(v_fst_1152_);
lean_dec(v_snd_1147_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1204_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; 
lean_inc(v_fst_1152_);
v___x_1157_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1152_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1195_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1195_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1195_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_fst_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1193_; 
v_fst_1162_ = lean_ctor_get(v_a_1158_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_a_1158_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_a_1158_, 1);
lean_dec(v_unused_1194_);
v___x_1164_ = v_a_1158_;
v_isShared_1165_ = v_isSharedCheck_1193_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_fst_1162_);
lean_dec(v_a_1158_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1193_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_u_1166_; lean_object* v_00_u03c3s_1167_; lean_object* v_target_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1191_; 
v_u_1166_ = lean_ctor_get(v_fst_1152_, 0);
v_00_u03c3s_1167_ = lean_ctor_get(v_fst_1152_, 1);
v_target_1168_ = lean_ctor_get(v_fst_1152_, 3);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_fst_1152_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_fst_1152_, 2);
lean_dec(v_unused_1192_);
v___x_1170_ = v_fst_1152_;
v_isShared_1171_ = v_isSharedCheck_1191_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_target_1168_);
lean_inc(v_00_u03c3s_1167_);
lean_inc(v_u_1166_);
lean_dec(v_fst_1152_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1191_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1172_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1));
v___x_1173_ = lean_box(0);
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 1);
lean_ctor_set(v___x_1150_, 1, v___x_1173_);
lean_ctor_set(v___x_1150_, 0, v_u_1134_);
v___x_1175_ = v___x_1150_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_u_1134_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1173_);
v___x_1175_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1176_ = l_Lean_mkConst(v___x_1172_, v___x_1175_);
lean_inc_ref(v_target_1168_);
lean_inc(v_fst_1162_);
v___x_1177_ = l_Lean_mkApp4(v___x_1176_, v_00_u03c3s_1135_, v_fst_1162_, v_target_1168_, v_snd_1153_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 2, v_fst_1162_);
v___x_1179_ = v___x_1170_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_u_1166_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_00_u03c3s_1167_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_fst_1162_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_target_1168_);
v___x_1179_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1181_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 1, v___x_1177_);
lean_ctor_set(v___x_1164_, 0, v___x_1179_);
v___x_1181_ = v___x_1164_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v___x_1177_);
v___x_1181_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v___x_1181_);
lean_ctor_set(v___x_1155_, 0, v_fst_1148_);
v___x_1183_ = v___x_1155_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_fst_1148_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1183_);
v___x_1185_ = v___x_1160_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
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
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1155_);
lean_dec(v_snd_1153_);
lean_dec(v_fst_1152_);
lean_del_object(v___x_1150_);
lean_dec(v_fst_1148_);
lean_dec_ref(v_00_u03c3s_1135_);
lean_dec(v_u_1134_);
v_a_1196_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1157_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1157_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_00_u03c3s_1135_);
lean_dec(v_u_1134_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object* v_u_1206_, lean_object* v_00_u03c3s_1207_, lean_object* v_k_1208_, lean_object* v_x_1209_, lean_object* v___h_u03c6_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(v_u_1206_, v_00_u03c3s_1207_, v_k_1208_, v_x_1209_, v___h_u03c6_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec_ref(v___h_u03c6_1210_);
lean_dec_ref(v_x_1209_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object* v_u_1233_, lean_object* v_00_u03c3s_1234_, lean_object* v_k_1235_, lean_object* v_tail_1236_, lean_object* v_fst_1237_, lean_object* v_H_u2081_x27_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___f_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_inc_ref(v_H_u2081_x27_1238_);
lean_inc_ref_n(v_00_u03c3s_1234_, 2);
lean_inc_n(v_u_1233_, 2);
v___f_1244_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1244_, 0, v_u_1233_);
lean_closure_set(v___f_1244_, 1, v_00_u03c3s_1234_);
lean_closure_set(v___f_1244_, 2, v_H_u2081_x27_1238_);
lean_closure_set(v___f_1244_, 3, v_k_1235_);
v___x_1245_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1245_, 0, v_tail_1236_);
lean_inc_ref(v_fst_1237_);
v___x_1246_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1233_, v_00_u03c3s_1234_, v_fst_1237_, v___x_1245_, v___f_1244_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1292_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1292_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1292_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_fst_1251_; lean_object* v_snd_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1291_; 
v_fst_1251_ = lean_ctor_get(v_a_1247_, 0);
v_snd_1252_ = lean_ctor_get(v_a_1247_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_a_1247_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1254_ = v_a_1247_;
v_isShared_1255_ = v_isSharedCheck_1291_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_snd_1252_);
lean_inc(v_fst_1251_);
lean_dec(v_a_1247_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1291_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v_fst_1256_; lean_object* v_snd_1257_; lean_object* v_snd_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1289_; 
v_fst_1256_ = lean_ctor_get(v_snd_1252_, 0);
lean_inc(v_fst_1256_);
v_snd_1257_ = lean_ctor_get(v_fst_1251_, 1);
v_snd_1258_ = lean_ctor_get(v_snd_1252_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_snd_1252_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_snd_1252_, 0);
lean_dec(v_unused_1290_);
v___x_1260_ = v_snd_1252_;
v_isShared_1261_ = v_isSharedCheck_1289_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_snd_1258_);
lean_dec(v_snd_1252_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1289_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_u_1262_; lean_object* v_00_u03c3s_1263_; lean_object* v_target_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1287_; 
v_u_1262_ = lean_ctor_get(v_fst_1256_, 0);
v_00_u03c3s_1263_ = lean_ctor_get(v_fst_1256_, 1);
v_target_1264_ = lean_ctor_get(v_fst_1256_, 3);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_fst_1256_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v_fst_1256_, 2);
lean_dec(v_unused_1288_);
v___x_1266_ = v_fst_1256_;
v_isShared_1267_ = v_isSharedCheck_1287_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_target_1264_);
lean_inc(v_00_u03c3s_1263_);
lean_inc(v_u_1262_);
lean_dec(v_fst_1256_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1287_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1268_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1));
v___x_1269_ = lean_box(0);
lean_inc_n(v_u_1233_, 2);
v___x_1270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_u_1233_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = l_Lean_mkConst(v___x_1268_, v___x_1270_);
lean_inc_ref(v_target_1264_);
lean_inc_ref(v_fst_1237_);
lean_inc_ref(v_H_u2081_x27_1238_);
lean_inc_n(v_snd_1257_, 2);
lean_inc_ref_n(v_00_u03c3s_1234_, 2);
v___x_1272_ = l_Lean_mkApp6(v___x_1271_, v_00_u03c3s_1234_, v_snd_1257_, v_H_u2081_x27_1238_, v_fst_1237_, v_target_1264_, v_snd_1258_);
v___x_1273_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1233_, v_00_u03c3s_1234_, v_snd_1257_, v_fst_1237_);
v___x_1274_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1233_, v_00_u03c3s_1234_, v___x_1273_, v_H_u2081_x27_1238_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 2, v___x_1274_);
v___x_1276_ = v___x_1266_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_u_1262_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_00_u03c3s_1263_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_target_1264_);
v___x_1276_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v___x_1272_);
lean_ctor_set(v___x_1260_, 0, v___x_1276_);
v___x_1278_ = v___x_1260_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1272_);
v___x_1278_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v___x_1278_);
v___x_1280_ = v___x_1254_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_fst_1251_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1282_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1280_);
v___x_1282_ = v___x_1249_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
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
lean_dec_ref(v_H_u2081_x27_1238_);
lean_dec_ref(v_fst_1237_);
lean_dec_ref(v_00_u03c3s_1234_);
lean_dec(v_u_1233_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object* v_u_1293_, lean_object* v_00_u03c3s_1294_, lean_object* v_k_1295_, lean_object* v_tail_1296_, lean_object* v_fst_1297_, lean_object* v_H_u2081_x27_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(v_u_1293_, v_00_u03c3s_1294_, v_k_1295_, v_tail_1296_, v_fst_1297_, v_H_u2081_x27_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1304_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(lean_object* v___x_1316_, lean_object* v_tail_1317_, lean_object* v_u_1318_, lean_object* v___x_1319_, lean_object* v_k_1320_, lean_object* v_x_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(v___x_1316_, v_tail_1317_, v_u_1318_, v___x_1319_, v_k_1320_, v_x_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
return v_res_1327_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6));
v___x_1330_ = l_Lean_stringToMessageData(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10));
v___x_1339_ = l_Lean_stringToMessageData(v___x_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(lean_object* v_u_1346_, lean_object* v_00_u03c3s_1347_, lean_object* v_H_1348_, lean_object* v_pat_1349_, lean_object* v_k_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
switch(lean_obj_tag(v_pat_1349_))
{
case 0:
{
lean_object* v_name_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1403_; 
v_name_1356_ = lean_ctor_get(v_pat_1349_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_pat_1349_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1358_ = v_pat_1349_;
v_isShared_1359_ = v_isSharedCheck_1403_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_name_1356_);
lean_dec(v_pat_1349_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1403_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1368_; lean_object* v_a_1369_; lean_object* v___x_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1372_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1373_ = 0;
v___x_1374_ = lean_box(0);
v___x_1375_ = l_Lean_Meta_mkFreshExprMVar(v___x_1372_, v___x_1373_, v___x_1374_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1378_ = lean_box(0);
lean_inc(v_u_1346_);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_u_1346_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = l_Lean_mkConst(v___x_1377_, v___x_1379_);
lean_inc_ref(v_H_1348_);
lean_inc_ref(v_00_u03c3s_1347_);
v___x_1381_ = l_Lean_mkApp3(v___x_1380_, v_00_u03c3s_1347_, v_H_1348_, v_a_1376_);
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Lean_Meta_synthInstance(v___x_1381_, v___x_1382_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref_known(v___x_1383_, 1);
lean_inc(v_name_1356_);
v___x_1384_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1384_, 0, v_name_1356_);
lean_inc_ref(v_k_1350_);
lean_inc_ref(v_H_1348_);
lean_inc_ref(v_00_u03c3s_1347_);
lean_inc(v_u_1346_);
v___x_1385_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1346_, v_00_u03c3s_1347_, v_H_1348_, v___x_1384_, v_k_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_del_object(v___x_1358_);
lean_dec(v_name_1356_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
lean_dec(v_u_1346_);
return v___x_1385_;
}
else
{
lean_object* v_a_1386_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc(v_a_1386_);
v___y_1368_ = v___x_1385_;
v_a_1369_ = v_a_1386_;
goto v___jp_1367_;
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1383_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1383_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
lean_inc(v_a_1387_);
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
v___y_1368_ = v___x_1392_;
v_a_1369_ = v_a_1387_;
goto v___jp_1367_;
}
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
v_a_1395_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1375_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1375_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
lean_inc(v_a_1395_);
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
v___y_1368_ = v___x_1400_;
v_a_1369_ = v_a_1395_;
goto v___jp_1367_;
}
}
}
v___jp_1360_:
{
if (v___y_1362_ == 0)
{
lean_object* v___x_1364_; 
lean_dec_ref(v___y_1361_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set_tag(v___x_1358_, 5);
v___x_1364_ = v___x_1358_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_name_1356_);
v___x_1364_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
v_pat_1349_ = v___x_1364_;
goto _start;
}
}
else
{
lean_del_object(v___x_1358_);
lean_dec(v_name_1356_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
lean_dec(v_u_1346_);
return v___y_1361_;
}
}
v___jp_1367_:
{
uint8_t v___x_1370_; 
v___x_1370_ = l_Lean_Exception_isInterrupt(v_a_1369_);
if (v___x_1370_ == 0)
{
uint8_t v___x_1371_; 
v___x_1371_ = l_Lean_Exception_isRuntime(v_a_1369_);
v___y_1361_ = v___y_1368_;
v___y_1362_ = v___x_1371_;
goto v___jp_1360_;
}
else
{
lean_dec_ref(v_a_1369_);
v___y_1361_ = v___y_1368_;
v___y_1362_ = v___x_1370_;
goto v___jp_1360_;
}
}
}
}
case 1:
{
lean_object* v_H_x27_1404_; lean_object* v___x_1405_; 
lean_inc_ref(v_00_u03c3s_1347_);
lean_inc(v_u_1346_);
v_H_x27_1404_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1346_, v_00_u03c3s_1347_);
lean_inc(v_a_1354_);
lean_inc_ref(v_a_1353_);
lean_inc(v_a_1352_);
lean_inc_ref(v_a_1351_);
v___x_1405_ = lean_apply_6(v_k_1350_, v_H_x27_1404_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, lean_box(0));
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v_snd_1407_; lean_object* v_fst_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1466_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v_snd_1407_ = lean_ctor_get(v_a_1406_, 1);
v_fst_1408_ = lean_ctor_get(v_a_1406_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_a_1406_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1410_ = v_a_1406_;
v_isShared_1411_ = v_isSharedCheck_1466_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_snd_1407_);
lean_inc(v_fst_1408_);
lean_dec(v_a_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1466_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_fst_1412_; lean_object* v_snd_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1465_; 
v_fst_1412_ = lean_ctor_get(v_snd_1407_, 0);
v_snd_1413_ = lean_ctor_get(v_snd_1407_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_snd_1407_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1415_ = v_snd_1407_;
v_isShared_1416_ = v_isSharedCheck_1465_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_snd_1413_);
lean_inc(v_fst_1412_);
lean_dec(v_snd_1407_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1465_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1417_; 
lean_inc(v_fst_1412_);
v___x_1417_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1412_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1456_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1456_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1456_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_fst_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1454_; 
v_fst_1422_ = lean_ctor_get(v_a_1418_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_a_1418_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v_a_1418_, 1);
lean_dec(v_unused_1455_);
v___x_1424_ = v_a_1418_;
v_isShared_1425_ = v_isSharedCheck_1454_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_fst_1422_);
lean_dec(v_a_1418_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1454_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_u_1426_; lean_object* v_00_u03c3s_1427_; lean_object* v_target_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1452_; 
v_u_1426_ = lean_ctor_get(v_fst_1412_, 0);
v_00_u03c3s_1427_ = lean_ctor_get(v_fst_1412_, 1);
v_target_1428_ = lean_ctor_get(v_fst_1412_, 3);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_fst_1412_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_fst_1412_, 2);
lean_dec(v_unused_1453_);
v___x_1430_ = v_fst_1412_;
v_isShared_1431_ = v_isSharedCheck_1452_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_target_1428_);
lean_inc(v_00_u03c3s_1427_);
lean_inc(v_u_1426_);
lean_dec(v_fst_1412_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1452_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1));
v___x_1433_ = lean_box(0);
lean_inc(v_u_1346_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 1);
lean_ctor_set(v___x_1410_, 1, v___x_1433_);
lean_ctor_set(v___x_1410_, 0, v_u_1346_);
v___x_1435_ = v___x_1410_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_u_1346_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1436_ = l_Lean_mkConst(v___x_1432_, v___x_1435_);
lean_inc_ref(v_target_1428_);
lean_inc_ref(v_H_1348_);
lean_inc(v_fst_1422_);
lean_inc_ref(v_00_u03c3s_1347_);
v___x_1437_ = l_Lean_mkApp5(v___x_1436_, v_00_u03c3s_1347_, v_fst_1422_, v_H_1348_, v_target_1428_, v_snd_1413_);
v___x_1438_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1346_, v_00_u03c3s_1347_, v_fst_1422_, v_H_1348_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 2, v___x_1438_);
v___x_1440_ = v___x_1430_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_u_1426_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_00_u03c3s_1427_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_target_1428_);
v___x_1440_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 1, v___x_1437_);
lean_ctor_set(v___x_1424_, 0, v___x_1440_);
v___x_1442_ = v___x_1424_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1437_);
v___x_1442_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 1, v___x_1442_);
lean_ctor_set(v___x_1415_, 0, v_fst_1408_);
v___x_1444_ = v___x_1415_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_fst_1408_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1444_);
v___x_1446_ = v___x_1420_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
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
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_del_object(v___x_1415_);
lean_dec(v_snd_1413_);
lean_dec(v_fst_1412_);
lean_del_object(v___x_1410_);
lean_dec(v_fst_1408_);
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
lean_dec(v_u_1346_);
v_a_1457_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1417_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1417_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
lean_dec(v_u_1346_);
return v___x_1405_;
}
}
case 2:
{
lean_object* v_args_1467_; 
v_args_1467_ = lean_ctor_get(v_pat_1349_, 0);
lean_inc(v_args_1467_);
lean_dec_ref_known(v_pat_1349_, 1);
if (lean_obj_tag(v_args_1467_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_box(1);
v_pat_1349_ = v___x_1468_;
goto _start;
}
else
{
lean_object* v_tail_1470_; 
v_tail_1470_ = lean_ctor_get(v_args_1467_, 1);
if (lean_obj_tag(v_tail_1470_) == 0)
{
lean_object* v_head_1471_; 
v_head_1471_ = lean_ctor_get(v_args_1467_, 0);
lean_inc(v_head_1471_);
lean_dec_ref_known(v_args_1467_, 2);
v_pat_1349_ = v_head_1471_;
goto _start;
}
else
{
lean_object* v_head_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1566_; 
lean_inc(v_tail_1470_);
v_head_1473_ = lean_ctor_get(v_args_1467_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_args_1467_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v_args_1467_, 1);
lean_dec(v_unused_1567_);
v___x_1475_ = v_args_1467_;
v_isShared_1476_ = v_isSharedCheck_1566_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_head_1473_);
lean_dec(v_args_1467_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1566_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; 
lean_inc_ref(v_H_1348_);
lean_inc_ref(v_00_u03c3s_1347_);
lean_inc(v_u_1346_);
v___x_1477_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_1346_, v_00_u03c3s_1347_, v_H_1348_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
if (lean_obj_tag(v_a_1478_) == 1)
{
lean_object* v_val_1479_; lean_object* v_snd_1480_; lean_object* v_fst_1481_; lean_object* v_fst_1482_; lean_object* v_snd_1483_; lean_object* v___f_1484_; lean_object* v___x_1485_; 
v_val_1479_ = lean_ctor_get(v_a_1478_, 0);
lean_inc(v_val_1479_);
lean_dec_ref_known(v_a_1478_, 1);
v_snd_1480_ = lean_ctor_get(v_val_1479_, 1);
lean_inc(v_snd_1480_);
v_fst_1481_ = lean_ctor_get(v_val_1479_, 0);
lean_inc_n(v_fst_1481_, 2);
lean_dec(v_val_1479_);
v_fst_1482_ = lean_ctor_get(v_snd_1480_, 0);
lean_inc_n(v_fst_1482_, 2);
v_snd_1483_ = lean_ctor_get(v_snd_1480_, 1);
lean_inc(v_snd_1483_);
lean_dec(v_snd_1480_);
lean_inc_ref_n(v_00_u03c3s_1347_, 2);
lean_inc_n(v_u_1346_, 2);
v___f_1484_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed), 11, 5);
lean_closure_set(v___f_1484_, 0, v_u_1346_);
lean_closure_set(v___f_1484_, 1, v_00_u03c3s_1347_);
lean_closure_set(v___f_1484_, 2, v_k_1350_);
lean_closure_set(v___f_1484_, 3, v_tail_1470_);
lean_closure_set(v___f_1484_, 4, v_fst_1482_);
v___x_1485_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1346_, v_00_u03c3s_1347_, v_fst_1481_, v_head_1473_, v___f_1484_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1533_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1533_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1533_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v_fst_1492_; lean_object* v_fst_1493_; lean_object* v_snd_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1532_; 
v_fst_1490_ = lean_ctor_get(v_a_1486_, 0);
lean_inc(v_fst_1490_);
v_snd_1491_ = lean_ctor_get(v_a_1486_, 1);
lean_inc(v_snd_1491_);
lean_dec(v_a_1486_);
v_fst_1492_ = lean_ctor_get(v_snd_1491_, 0);
lean_inc(v_fst_1492_);
v_fst_1493_ = lean_ctor_get(v_fst_1490_, 0);
v_snd_1494_ = lean_ctor_get(v_fst_1490_, 1);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_fst_1490_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1496_ = v_fst_1490_;
v_isShared_1497_ = v_isSharedCheck_1532_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_snd_1494_);
lean_inc(v_fst_1493_);
lean_dec(v_fst_1490_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1532_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1530_; 
v_snd_1498_ = lean_ctor_get(v_snd_1491_, 1);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_snd_1491_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_snd_1491_, 0);
lean_dec(v_unused_1531_);
v___x_1500_ = v_snd_1491_;
v_isShared_1501_ = v_isSharedCheck_1530_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_dec(v_snd_1491_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1530_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_u_1502_; lean_object* v_00_u03c3s_1503_; lean_object* v_target_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1528_; 
v_u_1502_ = lean_ctor_get(v_fst_1492_, 0);
v_00_u03c3s_1503_ = lean_ctor_get(v_fst_1492_, 1);
v_target_1504_ = lean_ctor_get(v_fst_1492_, 3);
v_isSharedCheck_1528_ = !lean_is_exclusive(v_fst_1492_);
if (v_isSharedCheck_1528_ == 0)
{
lean_object* v_unused_1529_; 
v_unused_1529_ = lean_ctor_get(v_fst_1492_, 2);
lean_dec(v_unused_1529_);
v___x_1506_ = v_fst_1492_;
v_isShared_1507_ = v_isSharedCheck_1528_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_target_1504_);
lean_inc(v_00_u03c3s_1503_);
lean_inc(v_u_1502_);
lean_dec(v_fst_1492_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1528_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1508_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3));
v___x_1509_ = lean_box(0);
lean_inc(v_u_1346_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1509_);
lean_ctor_set(v___x_1475_, 0, v_u_1346_);
v___x_1511_ = v___x_1475_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_u_1346_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1512_ = l_Lean_mkConst(v___x_1508_, v___x_1511_);
lean_inc_ref(v_target_1504_);
lean_inc_ref(v_H_1348_);
lean_inc(v_snd_1494_);
lean_inc_ref(v_00_u03c3s_1347_);
v___x_1513_ = l_Lean_mkApp8(v___x_1512_, v_00_u03c3s_1347_, v_snd_1494_, v_fst_1481_, v_fst_1482_, v_H_1348_, v_target_1504_, v_snd_1483_, v_snd_1498_);
v___x_1514_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1346_, v_00_u03c3s_1347_, v_snd_1494_, v_H_1348_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 2, v___x_1514_);
v___x_1516_ = v___x_1506_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_u_1502_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_00_u03c3s_1503_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_target_1504_);
v___x_1516_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v___x_1518_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1513_);
lean_ctor_set(v___x_1500_, 0, v___x_1516_);
v___x_1518_ = v___x_1500_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1513_);
v___x_1518_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 1, v___x_1518_);
v___x_1520_ = v___x_1496_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_fst_1493_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1520_);
v___x_1522_ = v___x_1488_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
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
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
lean_dec(v_snd_1483_);
lean_dec(v_fst_1482_);
lean_dec(v_fst_1481_);
lean_del_object(v___x_1475_);
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
lean_dec(v_u_1346_);
v_a_1534_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1485_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1485_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
lean_dec(v_a_1478_);
lean_del_object(v___x_1475_);
lean_dec_ref(v_00_u03c3s_1347_);
v___x_1542_ = l_Lean_Expr_consumeMData(v_H_1348_);
v___x_1543_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_1544_ = lean_unsigned_to_nat(3u);
v___x_1545_ = l_Lean_Expr_isAppOfArity(v___x_1542_, v___x_1543_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref(v___x_1542_);
lean_dec(v_head_1473_);
lean_dec(v_tail_1470_);
lean_dec_ref(v_k_1350_);
lean_dec(v_u_1346_);
v___x_1546_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5);
v___x_1547_ = l_Lean_MessageData_ofExpr(v_H_1348_);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1548_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1549_;
}
else
{
if (lean_obj_tag(v_head_1473_) == 0)
{
lean_object* v_name_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___f_1554_; lean_object* v___x_1555_; 
v_name_1550_ = lean_ctor_get(v_head_1473_, 0);
lean_inc(v_name_1550_);
lean_dec_ref_known(v_head_1473_, 1);
v___x_1551_ = l_Lean_Expr_appFn_x21(v___x_1542_);
v___x_1552_ = l_Lean_Expr_appArg_x21(v___x_1551_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = l_Lean_Expr_appArg_x21(v___x_1542_);
lean_dec_ref(v___x_1542_);
v___f_1554_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1554_, 0, v___x_1553_);
lean_closure_set(v___f_1554_, 1, v_tail_1470_);
lean_closure_set(v___f_1554_, 2, v_u_1346_);
lean_closure_set(v___f_1554_, 3, v___x_1552_);
lean_closure_set(v___f_1554_, 4, v_k_1350_);
v___x_1555_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_1348_, v_name_1550_, v___f_1554_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec_ref(v___x_1542_);
lean_dec(v_head_1473_);
lean_dec(v_tail_1470_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_H_1348_);
lean_dec(v_u_1346_);
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7);
v___x_1557_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1556_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1475_);
lean_dec(v_head_1473_);
lean_dec(v_tail_1470_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
lean_dec(v_u_1346_);
v_a_1558_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1477_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1477_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_args_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1663_; 
v_args_1568_ = lean_ctor_get(v_pat_1349_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_pat_1349_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1570_ = v_pat_1349_;
v_isShared_1571_ = v_isSharedCheck_1663_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_args_1568_);
lean_dec(v_pat_1349_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1663_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
if (lean_obj_tag(v_args_1568_) == 0)
{
lean_object* v___x_1572_; 
lean_del_object(v___x_1570_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
lean_dec(v_u_1346_);
v___x_1572_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_1572_;
}
else
{
lean_object* v_tail_1573_; 
v_tail_1573_ = lean_ctor_get(v_args_1568_, 1);
if (lean_obj_tag(v_tail_1573_) == 0)
{
lean_object* v_head_1574_; 
lean_del_object(v___x_1570_);
v_head_1574_ = lean_ctor_get(v_args_1568_, 0);
lean_inc(v_head_1574_);
lean_dec_ref_known(v_args_1568_, 2);
v_pat_1349_ = v_head_1574_;
goto _start;
}
else
{
lean_object* v_head_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1661_; 
lean_inc(v_tail_1573_);
lean_dec_ref(v_00_u03c3s_1347_);
v_head_1576_ = lean_ctor_get(v_args_1568_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_args_1568_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v_args_1568_, 1);
lean_dec(v_unused_1662_);
v___x_1578_ = v_args_1568_;
v_isShared_1579_ = v_isSharedCheck_1661_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_head_1576_);
lean_dec(v_args_1568_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1661_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1580_ = l_Lean_Expr_consumeMData(v_H_1348_);
v___x_1581_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9));
v___x_1582_ = lean_unsigned_to_nat(3u);
v___x_1583_ = l_Lean_Expr_isAppOfArity(v___x_1580_, v___x_1581_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec_ref(v___x_1580_);
lean_del_object(v___x_1578_);
lean_dec(v_head_1576_);
lean_dec(v_tail_1573_);
lean_del_object(v___x_1570_);
lean_dec_ref(v_k_1350_);
lean_dec(v_u_1346_);
v___x_1584_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11);
v___x_1585_ = l_Lean_MessageData_ofExpr(v_H_1348_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1586_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1587_;
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
lean_dec_ref(v_H_1348_);
v___x_1588_ = l_Lean_Expr_appFn_x21(v___x_1580_);
v___x_1589_ = l_Lean_Expr_appFn_x21(v___x_1588_);
v___x_1590_ = l_Lean_Expr_appArg_x21(v___x_1589_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = l_Lean_Expr_appArg_x21(v___x_1588_);
lean_dec_ref(v___x_1588_);
v___x_1592_ = l_Lean_Expr_appArg_x21(v___x_1580_);
lean_dec_ref(v___x_1580_);
lean_inc_ref(v_k_1350_);
lean_inc_ref(v___x_1591_);
lean_inc_ref(v___x_1590_);
lean_inc(v_u_1346_);
v___x_1593_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1346_, v___x_1590_, v___x_1591_, v_head_1576_, v_k_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v_snd_1595_; lean_object* v_fst_1596_; lean_object* v_snd_1597_; lean_object* v___x_1599_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v_snd_1595_ = lean_ctor_get(v_a_1594_, 1);
lean_inc(v_snd_1595_);
lean_dec(v_a_1594_);
v_fst_1596_ = lean_ctor_get(v_snd_1595_, 0);
lean_inc(v_fst_1596_);
v_snd_1597_ = lean_ctor_get(v_snd_1595_, 1);
lean_inc(v_snd_1597_);
lean_dec(v_snd_1595_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v_tail_1573_);
v___x_1599_ = v___x_1570_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_tail_1573_);
v___x_1599_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; 
lean_inc_ref(v___x_1592_);
lean_inc_ref(v___x_1590_);
lean_inc(v_u_1346_);
v___x_1600_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1346_, v___x_1590_, v___x_1592_, v___x_1599_, v_k_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v_snd_1602_; lean_object* v_fst_1603_; lean_object* v_snd_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1658_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v_snd_1602_ = lean_ctor_get(v_a_1601_, 1);
lean_inc(v_snd_1602_);
v_fst_1603_ = lean_ctor_get(v_a_1601_, 0);
lean_inc(v_fst_1603_);
lean_dec(v_a_1601_);
v_snd_1604_ = lean_ctor_get(v_snd_1602_, 1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_snd_1602_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_snd_1602_, 0);
lean_dec(v_unused_1659_);
v___x_1606_ = v_snd_1602_;
v_isShared_1607_ = v_isSharedCheck_1658_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_snd_1604_);
lean_dec(v_snd_1602_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1658_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; 
lean_inc(v_fst_1596_);
v___x_1608_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1596_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1649_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1649_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1649_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v_fst_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1647_; 
v_fst_1613_ = lean_ctor_get(v_a_1609_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_a_1609_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_a_1609_, 1);
lean_dec(v_unused_1648_);
v___x_1615_ = v_a_1609_;
v_isShared_1616_ = v_isSharedCheck_1647_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_fst_1613_);
lean_dec(v_a_1609_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1647_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_u_1617_; lean_object* v_00_u03c3s_1618_; lean_object* v_target_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1645_; 
v_u_1617_ = lean_ctor_get(v_fst_1596_, 0);
v_00_u03c3s_1618_ = lean_ctor_get(v_fst_1596_, 1);
v_target_1619_ = lean_ctor_get(v_fst_1596_, 3);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_fst_1596_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v_fst_1596_, 2);
lean_dec(v_unused_1646_);
v___x_1621_ = v_fst_1596_;
v_isShared_1622_ = v_isSharedCheck_1645_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_target_1619_);
lean_inc(v_00_u03c3s_1618_);
lean_inc(v_u_1617_);
lean_dec(v_fst_1596_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1645_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = lean_box(0);
lean_inc(v_u_1346_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 1, v___x_1623_);
lean_ctor_set(v___x_1578_, 0, v_u_1346_);
v___x_1625_ = v___x_1578_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_u_1346_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_inc_ref(v___x_1625_);
v___x_1626_ = l_Lean_mkConst(v___x_1581_, v___x_1625_);
lean_inc_ref(v___x_1592_);
lean_inc_ref(v___x_1591_);
lean_inc_ref_n(v___x_1590_, 2);
v___x_1627_ = l_Lean_mkApp3(v___x_1626_, v___x_1590_, v___x_1591_, v___x_1592_);
lean_inc(v_fst_1613_);
v___x_1628_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1346_, v___x_1590_, v_fst_1613_, v___x_1627_);
lean_inc_ref(v_target_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 2, v___x_1628_);
v___x_1630_ = v___x_1621_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_u_1617_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_00_u03c3s_1618_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_target_1619_);
v___x_1630_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1631_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13));
v___x_1632_ = l_Lean_mkConst(v___x_1631_, v___x_1625_);
v___x_1633_ = l_Lean_mkApp7(v___x_1632_, v___x_1590_, v_fst_1613_, v___x_1591_, v___x_1592_, v_target_1619_, v_snd_1597_, v_snd_1604_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 1, v___x_1633_);
lean_ctor_set(v___x_1615_, 0, v___x_1630_);
v___x_1635_ = v___x_1615_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 1, v___x_1635_);
lean_ctor_set(v___x_1606_, 0, v_fst_1603_);
v___x_1637_ = v___x_1606_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_fst_1603_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1637_);
v___x_1639_ = v___x_1611_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
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
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_del_object(v___x_1606_);
lean_dec(v_snd_1604_);
lean_dec(v_fst_1603_);
lean_dec(v_snd_1597_);
lean_dec(v_fst_1596_);
lean_dec_ref(v___x_1592_);
lean_dec_ref(v___x_1591_);
lean_dec_ref(v___x_1590_);
lean_del_object(v___x_1578_);
lean_dec(v_u_1346_);
v_a_1650_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1608_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1608_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
else
{
lean_dec(v_snd_1597_);
lean_dec(v_fst_1596_);
lean_dec_ref(v___x_1592_);
lean_dec_ref(v___x_1591_);
lean_dec_ref(v___x_1590_);
lean_del_object(v___x_1578_);
lean_dec(v_u_1346_);
return v___x_1600_;
}
}
}
else
{
lean_dec_ref(v___x_1592_);
lean_dec_ref(v___x_1591_);
lean_dec_ref(v___x_1590_);
lean_del_object(v___x_1578_);
lean_dec(v_tail_1573_);
lean_del_object(v___x_1570_);
lean_dec_ref(v_k_1350_);
lean_dec(v_u_1346_);
return v___x_1593_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_h_1664_; lean_object* v___f_1665_; lean_object* v___x_1666_; 
v_h_1664_ = lean_ctor_get(v_pat_1349_, 0);
lean_inc(v_h_1664_);
lean_dec_ref_known(v_pat_1349_, 1);
lean_inc_ref(v_00_u03c3s_1347_);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1665_, 0, v_u_1346_);
lean_closure_set(v___f_1665_, 1, v_00_u03c3s_1347_);
lean_closure_set(v___f_1665_, 2, v_k_1350_);
v___x_1666_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1347_, v_H_1348_, v_h_1664_, v___f_1665_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1666_;
}
default: 
{
lean_object* v_h_1667_; lean_object* v___x_1668_; 
lean_dec(v_u_1346_);
v_h_1667_ = lean_ctor_get(v_pat_1349_, 0);
lean_inc(v_h_1667_);
lean_dec_ref_known(v_pat_1349_, 1);
v___x_1668_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_h_1667_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v_fst_1670_; lean_object* v_snd_1671_; lean_object* v___x_1672_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1668_, 1);
v_fst_1670_ = lean_ctor_get(v_a_1669_, 0);
lean_inc(v_fst_1670_);
v_snd_1671_ = lean_ctor_get(v_a_1669_, 1);
lean_inc(v_snd_1671_);
lean_dec(v_a_1669_);
v___x_1672_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v_a_1354_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
v___x_1674_ = l_Lean_Expr_consumeMData(v_H_1348_);
lean_dec_ref(v_H_1348_);
v___x_1675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1675_, 0, v_fst_1670_);
lean_ctor_set(v___x_1675_, 1, v_a_1673_);
lean_ctor_set(v___x_1675_, 2, v___x_1674_);
v___x_1676_ = 1;
lean_inc_ref(v___x_1675_);
v___x_1677_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1671_, v_00_u03c3s_1347_, v___x_1675_, v___x_1676_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
lean_dec_ref_known(v___x_1677_, 1);
v___x_1678_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1675_);
lean_inc(v_a_1354_);
lean_inc_ref(v_a_1353_);
lean_inc(v_a_1352_);
lean_inc_ref(v_a_1351_);
v___x_1679_ = lean_apply_6(v_k_1350_, v___x_1678_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, lean_box(0));
return v___x_1679_;
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref_known(v___x_1675_, 3);
lean_dec_ref(v_k_1350_);
v_a_1680_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1677_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1677_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec(v_snd_1671_);
lean_dec(v_fst_1670_);
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
v_a_1688_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1672_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1672_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec_ref(v_k_1350_);
lean_dec_ref(v_H_1348_);
lean_dec_ref(v_00_u03c3s_1347_);
v_a_1696_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1668_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1668_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(lean_object* v___x_1704_, lean_object* v_tail_1705_, lean_object* v_u_1706_, lean_object* v___x_1707_, lean_object* v_k_1708_, lean_object* v_x_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1715_ = lean_unsigned_to_nat(1u);
v___x_1716_ = lean_mk_empty_array_with_capacity(v___x_1715_);
v___x_1717_ = lean_array_push(v___x_1716_, v_x_1709_);
v___x_1718_ = 0;
v___x_1719_ = l_Lean_Expr_betaRev(v___x_1704_, v___x_1717_, v___x_1718_, v___x_1718_);
lean_dec_ref(v___x_1717_);
v___x_1720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_tail_1705_);
v___x_1721_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1706_, v___x_1707_, v___x_1719_, v___x_1720_, v_k_1708_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(lean_object* v_u_1722_, lean_object* v_00_u03c3s_1723_, lean_object* v_H_1724_, lean_object* v_pat_1725_, lean_object* v_k_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1722_, v_00_u03c3s_1723_, v_H_1724_, v_pat_1725_, v_k_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_object* v_00_u03b1_1733_, lean_object* v_u_1734_, lean_object* v_00_u03c3s_1735_, lean_object* v_H_1736_, lean_object* v_pat_1737_, lean_object* v_k_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1734_, v_00_u03c3s_1735_, v_H_1736_, v_pat_1737_, v_k_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_u_1746_, lean_object* v_00_u03c3s_1747_, lean_object* v_H_1748_, lean_object* v_pat_1749_, lean_object* v_k_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(v_00_u03b1_1745_, v_u_1746_, v_00_u03c3s_1747_, v_H_1748_, v_pat_1749_, v_k_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
lean_dec(v_a_1752_);
lean_dec_ref(v_a_1751_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_object* v_00_u03b1_1757_, lean_object* v_00_u03c3s_1758_, lean_object* v_hyp_1759_, lean_object* v_name_1760_, lean_object* v_k_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1758_, v_hyp_1759_, v_name_1760_, v_k_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(lean_object* v_00_u03b1_1768_, lean_object* v_00_u03c3s_1769_, lean_object* v_hyp_1770_, lean_object* v_name_1771_, lean_object* v_k_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(v_00_u03b1_1768_, v_00_u03c3s_1769_, v_hyp_1770_, v_name_1771_, v_k_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg(){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_object* v_00_u03b1_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(lean_object* v_00_u03b1_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(v_00_u03b1_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(lean_object* v_x_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
lean_inc(v___y_1808_);
lean_inc_ref(v___y_1807_);
v___x_1816_ = lean_apply_9(v_x_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, lean_box(0));
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(lean_object* v_x_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(lean_object* v_mvarId_1828_, lean_object* v_x_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___f_1839_; lean_object* v___x_1840_; 
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
lean_inc(v___y_1831_);
lean_inc_ref(v___y_1830_);
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1839_, 0, v_x_1829_);
lean_closure_set(v___f_1839_, 1, v___y_1830_);
lean_closure_set(v___f_1839_, 2, v___y_1831_);
lean_closure_set(v___f_1839_, 3, v___y_1832_);
lean_closure_set(v___f_1839_, 4, v___y_1833_);
v___x_1840_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1828_, v___f_1839_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1840_) == 0)
{
return v___x_1840_;
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(lean_object* v_mvarId_1849_, lean_object* v_x_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1849_, v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_object* v_00_u03b1_1861_, lean_object* v_mvarId_1862_, lean_object* v_x_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1862_, v_x_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_mvarId_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(v_00_u03b1_1874_, v_mvarId_1875_, v_x_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
lean_object* v_ks_1891_; lean_object* v_vs_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1916_; 
v_ks_1891_ = lean_ctor_get(v_x_1887_, 0);
v_vs_1892_ = lean_ctor_get(v_x_1887_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1894_ = v_x_1887_;
v_isShared_1895_ = v_isSharedCheck_1916_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_vs_1892_);
lean_inc(v_ks_1891_);
lean_dec(v_x_1887_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1916_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1896_ = lean_array_get_size(v_ks_1891_);
v___x_1897_ = lean_nat_dec_lt(v_x_1888_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_dec(v_x_1888_);
v___x_1898_ = lean_array_push(v_ks_1891_, v_x_1889_);
v___x_1899_ = lean_array_push(v_vs_1892_, v_x_1890_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1899_);
lean_ctor_set(v___x_1894_, 0, v___x_1898_);
v___x_1901_ = v___x_1894_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
else
{
lean_object* v_k_x27_1903_; uint8_t v___x_1904_; 
v_k_x27_1903_ = lean_array_fget_borrowed(v_ks_1891_, v_x_1888_);
v___x_1904_ = l_Lean_instBEqMVarId_beq(v_x_1889_, v_k_x27_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1906_; 
if (v_isShared_1895_ == 0)
{
v___x_1906_ = v___x_1894_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_ks_1891_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_vs_1892_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = lean_nat_add(v_x_1888_, v___x_1907_);
lean_dec(v_x_1888_);
v_x_1887_ = v___x_1906_;
v_x_1888_ = v___x_1908_;
goto _start;
}
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1911_ = lean_array_fset(v_ks_1891_, v_x_1888_, v_x_1889_);
v___x_1912_ = lean_array_fset(v_vs_1892_, v_x_1888_, v_x_1890_);
lean_dec(v_x_1888_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 1, v___x_1912_);
lean_ctor_set(v___x_1894_, 0, v___x_1911_);
v___x_1914_ = v___x_1894_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(lean_object* v_n_1917_, lean_object* v_k_1918_, lean_object* v_v_1919_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1921_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_n_1917_, v___x_1920_, v_k_1918_, v_v_1919_);
return v___x_1921_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(lean_object* v_x_1923_, size_t v_x_1924_, size_t v_x_1925_, lean_object* v_x_1926_, lean_object* v_x_1927_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
lean_object* v_es_1928_; size_t v___x_1929_; size_t v___x_1930_; lean_object* v_j_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_es_1928_ = lean_ctor_get(v_x_1923_, 0);
v___x_1929_ = ((size_t)31ULL);
v___x_1930_ = lean_usize_land(v_x_1924_, v___x_1929_);
v_j_1931_ = lean_usize_to_nat(v___x_1930_);
v___x_1932_ = lean_array_get_size(v_es_1928_);
v___x_1933_ = lean_nat_dec_lt(v_j_1931_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_dec(v_j_1931_);
lean_dec(v_x_1927_);
lean_dec(v_x_1926_);
return v_x_1923_;
}
else
{
lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1972_; 
lean_inc_ref(v_es_1928_);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1923_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_x_1923_, 0);
lean_dec(v_unused_1973_);
v___x_1935_ = v_x_1923_;
v_isShared_1936_ = v_isSharedCheck_1972_;
goto v_resetjp_1934_;
}
else
{
lean_dec(v_x_1923_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1972_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_v_1937_; lean_object* v___x_1938_; lean_object* v_xs_x27_1939_; lean_object* v___y_1941_; 
v_v_1937_ = lean_array_fget(v_es_1928_, v_j_1931_);
v___x_1938_ = lean_box(0);
v_xs_x27_1939_ = lean_array_fset(v_es_1928_, v_j_1931_, v___x_1938_);
switch(lean_obj_tag(v_v_1937_))
{
case 0:
{
lean_object* v_key_1946_; lean_object* v_val_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1957_; 
v_key_1946_ = lean_ctor_get(v_v_1937_, 0);
v_val_1947_ = lean_ctor_get(v_v_1937_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_v_1937_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1949_ = v_v_1937_;
v_isShared_1950_ = v_isSharedCheck_1957_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_val_1947_);
lean_inc(v_key_1946_);
lean_dec(v_v_1937_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1957_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
uint8_t v___x_1951_; 
v___x_1951_ = l_Lean_instBEqMVarId_beq(v_x_1926_, v_key_1946_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_del_object(v___x_1949_);
v___x_1952_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1946_, v_val_1947_, v_x_1926_, v_x_1927_);
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
v___y_1941_ = v___x_1953_;
goto v___jp_1940_;
}
else
{
lean_object* v___x_1955_; 
lean_dec(v_val_1947_);
lean_dec(v_key_1946_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v_x_1927_);
lean_ctor_set(v___x_1949_, 0, v_x_1926_);
v___x_1955_ = v___x_1949_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_x_1926_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_x_1927_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
v___y_1941_ = v___x_1955_;
goto v___jp_1940_;
}
}
}
}
case 1:
{
lean_object* v_node_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1970_; 
v_node_1958_ = lean_ctor_get(v_v_1937_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_v_1937_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1960_ = v_v_1937_;
v_isShared_1961_ = v_isSharedCheck_1970_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_node_1958_);
lean_dec(v_v_1937_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1970_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
size_t v___x_1962_; size_t v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1962_ = ((size_t)5ULL);
v___x_1963_ = lean_usize_shift_right(v_x_1924_, v___x_1962_);
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_x_1925_, v___x_1964_);
v___x_1966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_node_1958_, v___x_1963_, v___x_1965_, v_x_1926_, v_x_1927_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1966_);
v___x_1968_ = v___x_1960_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
v___y_1941_ = v___x_1968_;
goto v___jp_1940_;
}
}
}
default: 
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_x_1926_);
lean_ctor_set(v___x_1971_, 1, v_x_1927_);
v___y_1941_ = v___x_1971_;
goto v___jp_1940_;
}
}
v___jp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_array_fset(v_xs_x27_1939_, v_j_1931_, v___y_1941_);
lean_dec(v_j_1931_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1942_);
v___x_1944_ = v___x_1935_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
else
{
lean_object* v_ks_1974_; lean_object* v_vs_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1993_; 
v_ks_1974_ = lean_ctor_get(v_x_1923_, 0);
v_vs_1975_ = lean_ctor_get(v_x_1923_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_x_1923_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1977_ = v_x_1923_;
v_isShared_1978_ = v_isSharedCheck_1993_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_vs_1975_);
lean_inc(v_ks_1974_);
lean_dec(v_x_1923_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1993_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_ks_1974_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_vs_1975_);
v___x_1980_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v_newNode_1981_; size_t v___x_1982_; uint8_t v___x_1983_; 
v_newNode_1981_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v___x_1980_, v_x_1926_, v_x_1927_);
v___x_1982_ = ((size_t)7ULL);
v___x_1983_ = lean_usize_dec_le(v___x_1982_, v_x_1925_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1984_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1981_);
v___x_1985_ = lean_unsigned_to_nat(4u);
v___x_1986_ = lean_nat_dec_lt(v___x_1984_, v___x_1985_);
lean_dec(v___x_1984_);
if (v___x_1986_ == 0)
{
lean_object* v_ks_1987_; lean_object* v_vs_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_ks_1987_ = lean_ctor_get(v_newNode_1981_, 0);
lean_inc_ref(v_ks_1987_);
v_vs_1988_ = lean_ctor_get(v_newNode_1981_, 1);
lean_inc_ref(v_vs_1988_);
lean_dec_ref(v_newNode_1981_);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0);
v___x_1991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_x_1925_, v_ks_1987_, v_vs_1988_, v___x_1989_, v___x_1990_);
lean_dec_ref(v_vs_1988_);
lean_dec_ref(v_ks_1987_);
return v___x_1991_;
}
else
{
return v_newNode_1981_;
}
}
else
{
return v_newNode_1981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(size_t v_depth_1994_, lean_object* v_keys_1995_, lean_object* v_vals_1996_, lean_object* v_i_1997_, lean_object* v_entries_1998_){
_start:
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = lean_array_get_size(v_keys_1995_);
v___x_2000_ = lean_nat_dec_lt(v_i_1997_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec(v_i_1997_);
return v_entries_1998_;
}
else
{
lean_object* v_k_2001_; lean_object* v_v_2002_; uint64_t v___x_2003_; size_t v_h_2004_; size_t v___x_2005_; lean_object* v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; size_t v___x_2009_; size_t v_h_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_k_2001_ = lean_array_fget_borrowed(v_keys_1995_, v_i_1997_);
v_v_2002_ = lean_array_fget_borrowed(v_vals_1996_, v_i_1997_);
v___x_2003_ = l_Lean_instHashableMVarId_hash(v_k_2001_);
v_h_2004_ = lean_uint64_to_usize(v___x_2003_);
v___x_2005_ = ((size_t)5ULL);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = ((size_t)1ULL);
v___x_2008_ = lean_usize_sub(v_depth_1994_, v___x_2007_);
v___x_2009_ = lean_usize_mul(v___x_2005_, v___x_2008_);
v_h_2010_ = lean_usize_shift_right(v_h_2004_, v___x_2009_);
v___x_2011_ = lean_nat_add(v_i_1997_, v___x_2006_);
lean_dec(v_i_1997_);
lean_inc(v_v_2002_);
lean_inc(v_k_2001_);
v___x_2012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_entries_1998_, v_h_2010_, v_depth_1994_, v_k_2001_, v_v_2002_);
v_i_1997_ = v___x_2011_;
v_entries_1998_ = v___x_2012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg___boxed(lean_object* v_depth_2014_, lean_object* v_keys_2015_, lean_object* v_vals_2016_, lean_object* v_i_2017_, lean_object* v_entries_2018_){
_start:
{
size_t v_depth_boxed_2019_; lean_object* v_res_2020_; 
v_depth_boxed_2019_ = lean_unbox_usize(v_depth_2014_);
lean_dec(v_depth_2014_);
v_res_2020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_boxed_2019_, v_keys_2015_, v_vals_2016_, v_i_2017_, v_entries_2018_);
lean_dec_ref(v_vals_2016_);
lean_dec_ref(v_keys_2015_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
size_t v_x_19624__boxed_2026_; size_t v_x_19625__boxed_2027_; lean_object* v_res_2028_; 
v_x_19624__boxed_2026_ = lean_unbox_usize(v_x_2022_);
lean_dec(v_x_2022_);
v_x_19625__boxed_2027_ = lean_unbox_usize(v_x_2023_);
lean_dec(v_x_2023_);
v_res_2028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2021_, v_x_19624__boxed_2026_, v_x_19625__boxed_2027_, v_x_2024_, v_x_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_){
_start:
{
uint64_t v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; lean_object* v___x_2035_; 
v___x_2032_ = l_Lean_instHashableMVarId_hash(v_x_2030_);
v___x_2033_ = lean_uint64_to_usize(v___x_2032_);
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2029_, v___x_2033_, v___x_2034_, v_x_2030_, v_x_2031_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object* v_mvarId_2036_, lean_object* v_val_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; lean_object* v_mctx_2041_; lean_object* v_cache_2042_; lean_object* v_zetaDeltaFVarIds_2043_; lean_object* v_postponed_2044_; lean_object* v_diag_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2074_; 
v___x_2040_ = lean_st_ref_take(v___y_2038_);
v_mctx_2041_ = lean_ctor_get(v___x_2040_, 0);
v_cache_2042_ = lean_ctor_get(v___x_2040_, 1);
v_zetaDeltaFVarIds_2043_ = lean_ctor_get(v___x_2040_, 2);
v_postponed_2044_ = lean_ctor_get(v___x_2040_, 3);
v_diag_2045_ = lean_ctor_get(v___x_2040_, 4);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2047_ = v___x_2040_;
v_isShared_2048_ = v_isSharedCheck_2074_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_diag_2045_);
lean_inc(v_postponed_2044_);
lean_inc(v_zetaDeltaFVarIds_2043_);
lean_inc(v_cache_2042_);
lean_inc(v_mctx_2041_);
lean_dec(v___x_2040_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2074_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_depth_2049_; lean_object* v_levelAssignDepth_2050_; lean_object* v_lmvarCounter_2051_; lean_object* v_mvarCounter_2052_; lean_object* v_lDecls_2053_; lean_object* v_decls_2054_; lean_object* v_userNames_2055_; lean_object* v_lAssignment_2056_; lean_object* v_eAssignment_2057_; lean_object* v_dAssignment_2058_; lean_object* v_instanceTypedMVars_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2073_; 
v_depth_2049_ = lean_ctor_get(v_mctx_2041_, 0);
v_levelAssignDepth_2050_ = lean_ctor_get(v_mctx_2041_, 1);
v_lmvarCounter_2051_ = lean_ctor_get(v_mctx_2041_, 2);
v_mvarCounter_2052_ = lean_ctor_get(v_mctx_2041_, 3);
v_lDecls_2053_ = lean_ctor_get(v_mctx_2041_, 4);
v_decls_2054_ = lean_ctor_get(v_mctx_2041_, 5);
v_userNames_2055_ = lean_ctor_get(v_mctx_2041_, 6);
v_lAssignment_2056_ = lean_ctor_get(v_mctx_2041_, 7);
v_eAssignment_2057_ = lean_ctor_get(v_mctx_2041_, 8);
v_dAssignment_2058_ = lean_ctor_get(v_mctx_2041_, 9);
v_instanceTypedMVars_2059_ = lean_ctor_get(v_mctx_2041_, 10);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_mctx_2041_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2061_ = v_mctx_2041_;
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_instanceTypedMVars_2059_);
lean_inc(v_dAssignment_2058_);
lean_inc(v_eAssignment_2057_);
lean_inc(v_lAssignment_2056_);
lean_inc(v_userNames_2055_);
lean_inc(v_decls_2054_);
lean_inc(v_lDecls_2053_);
lean_inc(v_mvarCounter_2052_);
lean_inc(v_lmvarCounter_2051_);
lean_inc(v_levelAssignDepth_2050_);
lean_inc(v_depth_2049_);
lean_dec(v_mctx_2041_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2073_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2063_ = lean_box(0);
v___x_2064_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_eAssignment_2057_, v_mvarId_2036_, v_val_2037_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 8, v___x_2064_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_depth_2049_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_levelAssignDepth_2050_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_lmvarCounter_2051_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v_mvarCounter_2052_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v_lDecls_2053_);
lean_ctor_set(v_reuseFailAlloc_2072_, 5, v_decls_2054_);
lean_ctor_set(v_reuseFailAlloc_2072_, 6, v_userNames_2055_);
lean_ctor_set(v_reuseFailAlloc_2072_, 7, v_lAssignment_2056_);
lean_ctor_set(v_reuseFailAlloc_2072_, 8, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2072_, 9, v_dAssignment_2058_);
lean_ctor_set(v_reuseFailAlloc_2072_, 10, v_instanceTypedMVars_2059_);
v___x_2066_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2066_);
v___x_2068_ = v___x_2047_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_cache_2042_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_zetaDeltaFVarIds_2043_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_postponed_2044_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_diag_2045_);
v___x_2068_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_st_ref_put(v___y_2038_, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2063_);
return v___x_2070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object* v_mvarId_2075_, lean_object* v_val_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_2075_, v_val_2076_, v___y_2077_);
lean_dec(v___y_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object* v_snd_2082_, lean_object* v_hyp_2083_, lean_object* v_a_2084_, lean_object* v_fst_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; 
lean_inc_ref(v_snd_2082_);
v___x_2095_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_snd_2082_, v_hyp_2083_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v_focusHyp_2097_; lean_object* v_restHyps_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v_u_2101_; lean_object* v_00_u03c3s_2102_; lean_object* v_target_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v_focusHyp_2097_ = lean_ctor_get(v_a_2096_, 0);
v_restHyps_2098_ = lean_ctor_get(v_a_2096_, 1);
v___x_2099_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0));
v___x_2100_ = lean_st_mk_ref(v___x_2099_);
v_u_2101_ = lean_ctor_get(v_snd_2082_, 0);
v_00_u03c3s_2102_ = lean_ctor_get(v_snd_2082_, 1);
v_target_2103_ = lean_ctor_get(v_snd_2082_, 3);
lean_inc_ref(v_restHyps_2098_);
lean_inc_ref(v_target_2103_);
lean_inc_ref_n(v_00_u03c3s_2102_, 2);
lean_inc(v___x_2100_);
lean_inc_n(v_u_2101_, 2);
v___x_2104_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed), 11, 5);
lean_closure_set(v___x_2104_, 0, v_u_2101_);
lean_closure_set(v___x_2104_, 1, v___x_2100_);
lean_closure_set(v___x_2104_, 2, v_00_u03c3s_2102_);
lean_closure_set(v___x_2104_, 3, v_target_2103_);
lean_closure_set(v___x_2104_, 4, v_restHyps_2098_);
lean_inc_ref(v_focusHyp_2097_);
v___x_2105_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_2101_, v_00_u03c3s_2102_, v_focusHyp_2097_, v_a_2084_, v___x_2104_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v_snd_2107_; lean_object* v_snd_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v_snd_2107_ = lean_ctor_get(v_a_2106_, 1);
lean_inc(v_snd_2107_);
lean_dec(v_a_2106_);
v_snd_2108_ = lean_ctor_get(v_snd_2107_, 1);
lean_inc(v_snd_2108_);
lean_dec(v_snd_2107_);
v___x_2109_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(v_a_2096_, v_snd_2082_, v_snd_2108_);
v___x_2110_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_fst_2085_, v___x_2109_, v___y_2091_);
lean_dec_ref(v___x_2110_);
v___x_2111_ = lean_st_ref_get(v___x_2100_);
lean_dec(v___x_2100_);
v___x_2112_ = lean_array_to_list(v___x_2111_);
v___x_2113_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2112_, v___y_2087_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
return v___x_2113_;
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_dec(v___x_2100_);
lean_dec(v_a_2096_);
lean_dec(v_fst_2085_);
lean_dec_ref(v_snd_2082_);
v_a_2114_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2105_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2105_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_fst_2085_);
lean_dec(v_a_2084_);
lean_dec_ref(v_snd_2082_);
v_a_2122_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2095_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2095_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object* v_snd_2130_, lean_object* v_hyp_2131_, lean_object* v_a_2132_, lean_object* v_fst_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(v_snd_2130_, v_hyp_2131_, v_a_2132_, v_fst_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
return v_res_2143_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2144_; double v___x_2145_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_float_of_nat(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object* v_cls_2149_, lean_object* v_msg_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_ref_2156_; lean_object* v___x_2157_; lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2203_; 
v_ref_2156_ = lean_ctor_get(v___y_2153_, 2);
v___x_2157_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2203_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2203_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v_traceState_2163_; lean_object* v_env_2164_; lean_object* v_nextMacroScope_2165_; lean_object* v_ngen_2166_; lean_object* v_auxDeclNGen_2167_; lean_object* v_cache_2168_; lean_object* v_recordedDeps_2169_; lean_object* v_messages_2170_; lean_object* v_infoState_2171_; lean_object* v_snapshotTasks_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2202_; 
v___x_2162_ = lean_st_ref_take(v___y_2154_);
v_traceState_2163_ = lean_ctor_get(v___x_2162_, 4);
v_env_2164_ = lean_ctor_get(v___x_2162_, 0);
v_nextMacroScope_2165_ = lean_ctor_get(v___x_2162_, 1);
v_ngen_2166_ = lean_ctor_get(v___x_2162_, 2);
v_auxDeclNGen_2167_ = lean_ctor_get(v___x_2162_, 3);
v_cache_2168_ = lean_ctor_get(v___x_2162_, 5);
v_recordedDeps_2169_ = lean_ctor_get(v___x_2162_, 6);
v_messages_2170_ = lean_ctor_get(v___x_2162_, 7);
v_infoState_2171_ = lean_ctor_get(v___x_2162_, 8);
v_snapshotTasks_2172_ = lean_ctor_get(v___x_2162_, 9);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2174_ = v___x_2162_;
v_isShared_2175_ = v_isSharedCheck_2202_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snapshotTasks_2172_);
lean_inc(v_infoState_2171_);
lean_inc(v_messages_2170_);
lean_inc(v_recordedDeps_2169_);
lean_inc(v_cache_2168_);
lean_inc(v_traceState_2163_);
lean_inc(v_auxDeclNGen_2167_);
lean_inc(v_ngen_2166_);
lean_inc(v_nextMacroScope_2165_);
lean_inc(v_env_2164_);
lean_dec(v___x_2162_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2202_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
uint64_t v_tid_2176_; lean_object* v_traces_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2201_; 
v_tid_2176_ = lean_ctor_get_uint64(v_traceState_2163_, sizeof(void*)*1);
v_traces_2177_ = lean_ctor_get(v_traceState_2163_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_traceState_2163_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2179_ = v_traceState_2163_;
v_isShared_2180_ = v_isSharedCheck_2201_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_traces_2177_);
lean_dec(v_traceState_2163_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2201_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; double v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0);
v___x_2184_ = 0;
v___x_2185_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2186_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2186_, 0, v_cls_2149_);
lean_ctor_set(v___x_2186_, 1, v___x_2182_);
lean_ctor_set(v___x_2186_, 2, v___x_2185_);
lean_ctor_set_float(v___x_2186_, sizeof(void*)*3, v___x_2183_);
lean_ctor_set_float(v___x_2186_, sizeof(void*)*3 + 8, v___x_2183_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*3 + 16, v___x_2184_);
v___x_2187_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2));
v___x_2188_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v_a_2158_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
lean_inc(v_ref_2156_);
v___x_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2189_, 0, v_ref_2156_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_PersistentArray_push___redArg(v_traces_2177_, v___x_2189_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2190_);
v___x_2192_ = v___x_2179_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2190_);
lean_ctor_set_uint64(v_reuseFailAlloc_2200_, sizeof(void*)*1, v_tid_2176_);
v___x_2192_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 4, v___x_2192_);
v___x_2194_ = v___x_2174_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_env_2164_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_nextMacroScope_2165_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_ngen_2166_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_auxDeclNGen_2167_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2199_, 5, v_cache_2168_);
lean_ctor_set(v_reuseFailAlloc_2199_, 6, v_recordedDeps_2169_);
lean_ctor_set(v_reuseFailAlloc_2199_, 7, v_messages_2170_);
lean_ctor_set(v_reuseFailAlloc_2199_, 8, v_infoState_2171_);
lean_ctor_set(v_reuseFailAlloc_2199_, 9, v_snapshotTasks_2172_);
v___x_2194_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_st_ref_put(v___y_2154_, v___x_2194_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2181_);
v___x_2197_ = v___x_2160_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2181_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2204_, lean_object* v_msg_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2204_, v_msg_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object* v_as_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
if (lean_obj_tag(v_as_2215_) == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_box(0);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
else
{
lean_object* v_toCold_2227_; lean_object* v_options_2228_; uint8_t v_hasTrace_2229_; 
v_toCold_2227_ = lean_ctor_get(v___y_2222_, 0);
v_options_2228_ = lean_ctor_get(v_toCold_2227_, 2);
v_hasTrace_2229_ = lean_ctor_get_uint8(v_options_2228_, sizeof(void*)*1);
if (v_hasTrace_2229_ == 0)
{
lean_object* v_tail_2230_; 
v_tail_2230_ = lean_ctor_get(v_as_2215_, 1);
lean_inc(v_tail_2230_);
lean_dec_ref_known(v_as_2215_, 2);
v_as_2215_ = v_tail_2230_;
goto _start;
}
else
{
lean_object* v_head_2232_; lean_object* v_tail_2233_; lean_object* v_fst_2234_; lean_object* v_snd_2235_; lean_object* v_inheritedTraceOptions_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_head_2232_ = lean_ctor_get(v_as_2215_, 0);
lean_inc(v_head_2232_);
v_tail_2233_ = lean_ctor_get(v_as_2215_, 1);
lean_inc(v_tail_2233_);
lean_dec_ref_known(v_as_2215_, 2);
v_fst_2234_ = lean_ctor_get(v_head_2232_, 0);
lean_inc_n(v_fst_2234_, 2);
v_snd_2235_ = lean_ctor_get(v_head_2232_, 1);
lean_inc(v_snd_2235_);
lean_dec(v_head_2232_);
v_inheritedTraceOptions_2236_ = lean_ctor_get(v_toCold_2227_, 11);
v___x_2237_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2238_ = l_Lean_Name_append(v___x_2237_, v_fst_2234_);
v___x_2239_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2236_, v_options_2228_, v___x_2238_);
lean_dec(v___x_2238_);
if (v___x_2239_ == 0)
{
lean_dec(v_snd_2235_);
lean_dec(v_fst_2234_);
v_as_2215_ = v_tail_2233_;
goto _start;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2241_, 0, v_snd_2235_);
v___x_2242_ = l_Lean_MessageData_ofFormat(v___x_2241_);
v___x_2243_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_fst_2234_, v___x_2242_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_dec_ref_known(v___x_2243_, 1);
v_as_2215_ = v_tail_2233_;
goto _start;
}
else
{
lean_dec(v_tail_2233_);
return v___x_2243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object* v_as_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object* v_env_2256_, lean_object* v_declName_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
uint8_t v___x_2260_; lean_object* v_env_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; uint8_t v___x_2264_; 
v___x_2260_ = 0;
v_env_2261_ = l_Lean_Environment_setExporting(v_env_2256_, v___x_2260_);
lean_inc(v_declName_2257_);
v___x_2262_ = l_Lean_mkPrivateName(v_env_2261_, v_declName_2257_);
v___x_2263_ = 1;
lean_inc_ref(v_env_2261_);
v___x_2264_ = l_Lean_Environment_contains(v_env_2261_, v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2265_ = l_Lean_privateToUserName(v_declName_2257_);
v___x_2266_ = l_Lean_Environment_contains(v_env_2261_, v___x_2265_, v___x_2263_);
v___x_2267_ = lean_box(v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v___y_2259_);
return v___x_2268_;
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v_env_2261_);
lean_dec(v_declName_2257_);
v___x_2269_ = lean_box(v___x_2264_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v___y_2259_);
return v___x_2270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object* v_env_2271_, lean_object* v_declName_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(v_env_2271_, v_declName_2272_, v___y_2273_, v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object* v_msg_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_ref_2282_; lean_object* v___x_2283_; lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2292_; 
v_ref_2282_ = lean_ctor_get(v___y_2279_, 2);
v___x_2283_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2290_; 
lean_inc(v_ref_2282_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v_ref_2282_);
lean_ctor_set(v___x_2288_, 1, v_a_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 1);
lean_ctor_set(v___x_2286_, 0, v___x_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_msg_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object* v_ref_2300_, lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_toCold_2311_; lean_object* v_currRecDepth_2312_; lean_object* v_ref_2313_; uint16_t v_optionFlags_2314_; uint8_t v_suppressElabErrors_2315_; uint8_t v_isRecordingDeps_2316_; lean_object* v_ref_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_toCold_2311_ = lean_ctor_get(v___y_2308_, 0);
v_currRecDepth_2312_ = lean_ctor_get(v___y_2308_, 1);
v_ref_2313_ = lean_ctor_get(v___y_2308_, 2);
v_optionFlags_2314_ = lean_ctor_get_uint16(v___y_2308_, sizeof(void*)*3);
v_suppressElabErrors_2315_ = lean_ctor_get_uint8(v___y_2308_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2316_ = lean_ctor_get_uint8(v___y_2308_, sizeof(void*)*3 + 3);
v_ref_2317_ = l_Lean_replaceRef(v_ref_2300_, v_ref_2313_);
lean_inc(v_currRecDepth_2312_);
lean_inc_ref(v_toCold_2311_);
v___x_2318_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2318_, 0, v_toCold_2311_);
lean_ctor_set(v___x_2318_, 1, v_currRecDepth_2312_);
lean_ctor_set(v___x_2318_, 2, v_ref_2317_);
lean_ctor_set_uint16(v___x_2318_, sizeof(void*)*3, v_optionFlags_2314_);
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*3 + 2, v_suppressElabErrors_2315_);
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*3 + 3, v_isRecordingDeps_2316_);
v___x_2319_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2301_, v___y_2306_, v___y_2307_, v___x_2318_, v___y_2309_);
lean_dec_ref_known(v___x_2318_, 3);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2320_, lean_object* v_msg_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_2320_, v_msg_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v_ref_2320_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object* v_env_2332_, lean_object* v_currNamespace_2333_, lean_object* v_openDecls_2334_, lean_object* v_n_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = l_Lean_ResolveName_resolveNamespace(v_env_2332_, v_currNamespace_2333_, v_openDecls_2334_, v_n_2335_);
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_ctor_set(v___x_2339_, 1, v___y_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object* v_env_2340_, lean_object* v_currNamespace_2341_, lean_object* v_openDecls_2342_, lean_object* v_n_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(v_env_2340_, v_currNamespace_2341_, v_openDecls_2342_, v_n_2343_, v___y_2344_, v___y_2345_);
lean_dec_ref(v___y_2344_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object* v_env_2347_, lean_object* v___x_2348_, lean_object* v_currNamespace_2349_, lean_object* v_openDecls_2350_, lean_object* v_n_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = l_Lean_ResolveName_resolveGlobalName(v_env_2347_, v___x_2348_, v_currNamespace_2349_, v_openDecls_2350_, v_n_2351_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object* v_env_2356_, lean_object* v___x_2357_, lean_object* v_currNamespace_2358_, lean_object* v_openDecls_2359_, lean_object* v_n_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(v_env_2356_, v___x_2357_, v_currNamespace_2358_, v_openDecls_2359_, v_n_2360_, v___y_2361_, v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec_ref(v___x_2357_);
return v_res_2363_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = l_Lean_maxRecDepthErrorMessage;
v___x_2370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3);
v___x_2372_ = l_Lean_MessageData_ofFormat(v___x_2371_);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4);
v___x_2374_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2));
v___x_2375_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v___x_2373_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object* v_ref_2376_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v_ref_2376_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object* v_currNamespace_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_currNamespace_2384_);
lean_ctor_set(v___x_2387_, 1, v___y_2386_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(v_currNamespace_2388_, v___y_2389_, v___y_2390_);
lean_dec_ref(v___y_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object* v_keys_2392_, lean_object* v_i_2393_, lean_object* v_k_2394_){
_start:
{
lean_object* v___x_2395_; uint8_t v___x_2396_; 
v___x_2395_ = lean_array_get_size(v_keys_2392_);
v___x_2396_ = lean_nat_dec_lt(v_i_2393_, v___x_2395_);
if (v___x_2396_ == 0)
{
lean_dec(v_i_2393_);
return v___x_2396_;
}
else
{
lean_object* v_k_x27_2397_; uint8_t v___x_2398_; 
v_k_x27_2397_ = lean_array_fget_borrowed(v_keys_2392_, v_i_2393_);
v___x_2398_ = l_Lean_instBEqExtraModUse_beq(v_k_2394_, v_k_x27_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = lean_unsigned_to_nat(1u);
v___x_2400_ = lean_nat_add(v_i_2393_, v___x_2399_);
lean_dec(v_i_2393_);
v_i_2393_ = v___x_2400_;
goto _start;
}
else
{
lean_dec(v_i_2393_);
return v___x_2396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object* v_keys_2402_, lean_object* v_i_2403_, lean_object* v_k_2404_){
_start:
{
uint8_t v_res_2405_; lean_object* v_r_2406_; 
v_res_2405_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_2402_, v_i_2403_, v_k_2404_);
lean_dec_ref(v_k_2404_);
lean_dec_ref(v_keys_2402_);
v_r_2406_ = lean_box(v_res_2405_);
return v_r_2406_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object* v_x_2407_, size_t v_x_2408_, lean_object* v_x_2409_){
_start:
{
if (lean_obj_tag(v_x_2407_) == 0)
{
lean_object* v_es_2410_; lean_object* v___x_2411_; size_t v___x_2412_; size_t v___x_2413_; lean_object* v_j_2414_; lean_object* v___x_2415_; 
v_es_2410_ = lean_ctor_get(v_x_2407_, 0);
v___x_2411_ = lean_box(2);
v___x_2412_ = ((size_t)31ULL);
v___x_2413_ = lean_usize_land(v_x_2408_, v___x_2412_);
v_j_2414_ = lean_usize_to_nat(v___x_2413_);
v___x_2415_ = lean_array_get_borrowed(v___x_2411_, v_es_2410_, v_j_2414_);
lean_dec(v_j_2414_);
switch(lean_obj_tag(v___x_2415_))
{
case 0:
{
lean_object* v_key_2416_; uint8_t v___x_2417_; 
v_key_2416_ = lean_ctor_get(v___x_2415_, 0);
v___x_2417_ = l_Lean_instBEqExtraModUse_beq(v_x_2409_, v_key_2416_);
return v___x_2417_;
}
case 1:
{
lean_object* v_node_2418_; size_t v___x_2419_; size_t v___x_2420_; 
v_node_2418_ = lean_ctor_get(v___x_2415_, 0);
v___x_2419_ = ((size_t)5ULL);
v___x_2420_ = lean_usize_shift_right(v_x_2408_, v___x_2419_);
v_x_2407_ = v_node_2418_;
v_x_2408_ = v___x_2420_;
goto _start;
}
default: 
{
uint8_t v___x_2422_; 
v___x_2422_ = 0;
return v___x_2422_;
}
}
}
else
{
lean_object* v_ks_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; 
v_ks_2423_ = lean_ctor_get(v_x_2407_, 0);
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_ks_2423_, v___x_2424_, v_x_2409_);
return v___x_2425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_x_2426_, lean_object* v_x_2427_, lean_object* v_x_2428_){
_start:
{
size_t v_x_20291__boxed_2429_; uint8_t v_res_2430_; lean_object* v_r_2431_; 
v_x_20291__boxed_2429_ = lean_unbox_usize(v_x_2427_);
lean_dec(v_x_2427_);
v_res_2430_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2426_, v_x_20291__boxed_2429_, v_x_2428_);
lean_dec_ref(v_x_2428_);
lean_dec_ref(v_x_2426_);
v_r_2431_ = lean_box(v_res_2430_);
return v_r_2431_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object* v_x_2432_, lean_object* v_x_2433_){
_start:
{
uint64_t v___x_2434_; size_t v___x_2435_; uint8_t v___x_2436_; 
v___x_2434_ = l_Lean_instHashableExtraModUse_hash(v_x_2433_);
v___x_2435_ = lean_uint64_to_usize(v___x_2434_);
v___x_2436_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2432_, v___x_2435_, v_x_2433_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_2437_, lean_object* v_x_2438_){
_start:
{
uint8_t v_res_2439_; lean_object* v_r_2440_; 
v_res_2439_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_2437_, v_x_2438_);
lean_dec_ref(v_x_2438_);
lean_dec_ref(v_x_2437_);
v_r_2440_ = lean_box(v_res_2439_);
return v_r_2440_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2442_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2);
v___x_2448_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
lean_ctor_set(v___x_2448_, 2, v___x_2447_);
lean_ctor_set(v___x_2448_, 3, v___x_2447_);
lean_ctor_set(v___x_2448_, 4, v___x_2447_);
lean_ctor_set(v___x_2448_, 5, v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7));
v___x_2454_ = l_Lean_stringToMessageData(v___x_2453_);
return v___x_2454_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9));
v___x_2457_ = l_Lean_stringToMessageData(v___x_2456_);
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2459_ = l_Lean_stringToMessageData(v___x_2458_);
return v___x_2459_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v_cls_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_cls_2460_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6));
v___x_2461_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2462_ = l_Lean_Name_append(v___x_2461_, v_cls_2460_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13));
v___x_2465_ = l_Lean_stringToMessageData(v___x_2464_);
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15));
v___x_2468_ = l_Lean_stringToMessageData(v___x_2467_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object* v_mod_2473_, uint8_t v_isMeta_2474_, lean_object* v_hint_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v_env_2487_; uint8_t v_isExporting_2488_; lean_object* v_entry_2489_; lean_object* v___x_2490_; lean_object* v_env_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2485_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0);
v___x_2486_ = lean_st_ref_get(v___y_2483_);
v_env_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc_ref(v_env_2487_);
lean_dec(v___x_2486_);
v_isExporting_2488_ = lean_ctor_get_uint8(v_env_2487_, sizeof(void*)*8);
lean_dec_ref(v_env_2487_);
lean_inc(v_mod_2473_);
v_entry_2489_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2489_, 0, v_mod_2473_);
lean_ctor_set_uint8(v_entry_2489_, sizeof(void*)*1, v_isExporting_2488_);
lean_ctor_set_uint8(v_entry_2489_, sizeof(void*)*1 + 1, v_isMeta_2474_);
v___x_2490_ = lean_st_ref_get(v___y_2483_);
v_env_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc_ref(v_env_2491_);
lean_dec(v___x_2490_);
v___x_2492_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2493_ = lean_box(1);
v___x_2494_ = lean_box(0);
v___x_2538_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2485_, v___x_2492_, v_env_2491_, v___x_2493_, v___x_2494_);
v___x_2539_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v___x_2538_, v_entry_2489_);
lean_dec(v___x_2538_);
if (v___x_2539_ == 0)
{
lean_object* v_toCold_2540_; lean_object* v_options_2541_; uint8_t v_hasTrace_2542_; 
v_toCold_2540_ = lean_ctor_get(v___y_2482_, 0);
v_options_2541_ = lean_ctor_get(v_toCold_2540_, 2);
v_hasTrace_2542_ = lean_ctor_get_uint8(v_options_2541_, sizeof(void*)*1);
if (v_hasTrace_2542_ == 0)
{
lean_dec(v_hint_2475_);
lean_dec(v_mod_2473_);
v___y_2496_ = v___y_2481_;
v___y_2497_ = v___y_2483_;
goto v___jp_2495_;
}
else
{
lean_object* v_inheritedTraceOptions_2543_; lean_object* v_cls_2544_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_inheritedTraceOptions_2543_ = lean_ctor_get(v_toCold_2540_, 11);
v_cls_2544_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6));
v___x_2564_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12);
v___x_2565_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2543_, v_options_2541_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_dec(v_hint_2475_);
lean_dec(v_mod_2473_);
v___y_2496_ = v___y_2481_;
v___y_2497_ = v___y_2483_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2566_; lean_object* v___y_2568_; 
v___x_2566_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14);
if (v_isExporting_2488_ == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19));
v___y_2568_ = v___x_2575_;
goto v___jp_2567_;
}
else
{
lean_object* v___x_2576_; 
v___x_2576_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20));
v___y_2568_ = v___x_2576_;
goto v___jp_2567_;
}
v___jp_2567_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_inc_ref(v___y_2568_);
v___x_2569_ = l_Lean_stringToMessageData(v___y_2568_);
v___x_2570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2566_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16);
v___x_2572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2570_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
if (v_isMeta_2474_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17));
v___y_2551_ = v___x_2572_;
v___y_2552_ = v___x_2573_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18));
v___y_2551_ = v___x_2572_;
v___y_2552_ = v___x_2574_;
goto v___jp_2550_;
}
}
}
v___jp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___y_2546_);
lean_ctor_set(v___x_2548_, 1, v___y_2547_);
v___x_2549_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2544_, v___x_2548_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_dec_ref_known(v___x_2549_, 1);
v___y_2496_ = v___y_2481_;
v___y_2497_ = v___y_2483_;
goto v___jp_2495_;
}
else
{
lean_dec_ref_known(v_entry_2489_, 1);
return v___x_2549_;
}
}
v___jp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
lean_inc_ref(v___y_2552_);
v___x_2553_ = l_Lean_stringToMessageData(v___y_2552_);
v___x_2554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___y_2551_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8);
v___x_2556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2554_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = l_Lean_MessageData_ofName(v_mod_2473_);
v___x_2558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2556_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l_Lean_Name_isAnonymous(v_hint_2475_);
if (v___x_2559_ == 0)
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10);
v___x_2561_ = l_Lean_MessageData_ofName(v_hint_2475_);
v___x_2562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2560_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___y_2546_ = v___x_2558_;
v___y_2547_ = v___x_2562_;
goto v___jp_2545_;
}
else
{
lean_object* v___x_2563_; 
lean_dec(v_hint_2475_);
v___x_2563_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11);
v___y_2546_ = v___x_2558_;
v___y_2547_ = v___x_2563_;
goto v___jp_2545_;
}
}
}
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec_ref_known(v_entry_2489_, 1);
lean_dec(v_hint_2475_);
lean_dec(v_mod_2473_);
v___x_2577_ = lean_box(0);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
v___jp_2495_:
{
lean_object* v___x_2498_; lean_object* v_toEnvExtension_2499_; lean_object* v_env_2500_; lean_object* v_nextMacroScope_2501_; lean_object* v_ngen_2502_; lean_object* v_auxDeclNGen_2503_; lean_object* v_traceState_2504_; lean_object* v_recordedDeps_2505_; lean_object* v_messages_2506_; lean_object* v_infoState_2507_; lean_object* v_snapshotTasks_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2536_; 
v___x_2498_ = lean_st_ref_take(v___y_2497_);
v_toEnvExtension_2499_ = lean_ctor_get(v___x_2492_, 0);
v_env_2500_ = lean_ctor_get(v___x_2498_, 0);
v_nextMacroScope_2501_ = lean_ctor_get(v___x_2498_, 1);
v_ngen_2502_ = lean_ctor_get(v___x_2498_, 2);
v_auxDeclNGen_2503_ = lean_ctor_get(v___x_2498_, 3);
v_traceState_2504_ = lean_ctor_get(v___x_2498_, 4);
v_recordedDeps_2505_ = lean_ctor_get(v___x_2498_, 6);
v_messages_2506_ = lean_ctor_get(v___x_2498_, 7);
v_infoState_2507_ = lean_ctor_get(v___x_2498_, 8);
v_snapshotTasks_2508_ = lean_ctor_get(v___x_2498_, 9);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2536_ == 0)
{
lean_object* v_unused_2537_; 
v_unused_2537_ = lean_ctor_get(v___x_2498_, 5);
lean_dec(v_unused_2537_);
v___x_2510_ = v___x_2498_;
v_isShared_2511_ = v_isSharedCheck_2536_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_snapshotTasks_2508_);
lean_inc(v_infoState_2507_);
lean_inc(v_messages_2506_);
lean_inc(v_recordedDeps_2505_);
lean_inc(v_traceState_2504_);
lean_inc(v_auxDeclNGen_2503_);
lean_inc(v_ngen_2502_);
lean_inc(v_nextMacroScope_2501_);
lean_inc(v_env_2500_);
lean_dec(v___x_2498_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2536_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v_asyncMode_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2516_; 
v_asyncMode_2512_ = lean_ctor_get(v_toEnvExtension_2499_, 2);
v___x_2513_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2492_, v_env_2500_, v_entry_2489_, v_asyncMode_2512_, v___x_2494_);
v___x_2514_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 5, v___x_2514_);
lean_ctor_set(v___x_2510_, 0, v___x_2513_);
v___x_2516_ = v___x_2510_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2513_);
lean_ctor_set(v_reuseFailAlloc_2535_, 1, v_nextMacroScope_2501_);
lean_ctor_set(v_reuseFailAlloc_2535_, 2, v_ngen_2502_);
lean_ctor_set(v_reuseFailAlloc_2535_, 3, v_auxDeclNGen_2503_);
lean_ctor_set(v_reuseFailAlloc_2535_, 4, v_traceState_2504_);
lean_ctor_set(v_reuseFailAlloc_2535_, 5, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2535_, 6, v_recordedDeps_2505_);
lean_ctor_set(v_reuseFailAlloc_2535_, 7, v_messages_2506_);
lean_ctor_set(v_reuseFailAlloc_2535_, 8, v_infoState_2507_);
lean_ctor_set(v_reuseFailAlloc_2535_, 9, v_snapshotTasks_2508_);
v___x_2516_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_mctx_2519_; lean_object* v_zetaDeltaFVarIds_2520_; lean_object* v_postponed_2521_; lean_object* v_diag_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2533_; 
v___x_2517_ = lean_st_ref_put(v___y_2497_, v___x_2516_);
v___x_2518_ = lean_st_ref_take(v___y_2496_);
v_mctx_2519_ = lean_ctor_get(v___x_2518_, 0);
v_zetaDeltaFVarIds_2520_ = lean_ctor_get(v___x_2518_, 2);
v_postponed_2521_ = lean_ctor_get(v___x_2518_, 3);
v_diag_2522_ = lean_ctor_get(v___x_2518_, 4);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v___x_2518_, 1);
lean_dec(v_unused_2534_);
v___x_2524_ = v___x_2518_;
v_isShared_2525_ = v_isSharedCheck_2533_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_diag_2522_);
lean_inc(v_postponed_2521_);
lean_inc(v_zetaDeltaFVarIds_2520_);
lean_inc(v_mctx_2519_);
lean_dec(v___x_2518_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2533_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2529_; 
v___x_2526_ = lean_box(0);
v___x_2527_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 1, v___x_2527_);
v___x_2529_ = v___x_2524_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_mctx_2519_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2527_);
lean_ctor_set(v_reuseFailAlloc_2532_, 2, v_zetaDeltaFVarIds_2520_);
lean_ctor_set(v_reuseFailAlloc_2532_, 3, v_postponed_2521_);
lean_ctor_set(v_reuseFailAlloc_2532_, 4, v_diag_2522_);
v___x_2529_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_st_ref_put(v___y_2496_, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2526_);
return v___x_2531_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2579_, lean_object* v_isMeta_2580_, lean_object* v_hint_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
uint8_t v_isMeta_boxed_2591_; lean_object* v_res_2592_; 
v_isMeta_boxed_2591_ = lean_unbox(v_isMeta_2580_);
v_res_2592_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_mod_2579_, v_isMeta_boxed_2591_, v_hint_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2593_, lean_object* v_x_2594_){
_start:
{
if (lean_obj_tag(v_x_2594_) == 0)
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_box(0);
return v___x_2595_;
}
else
{
lean_object* v_key_2596_; lean_object* v_value_2597_; lean_object* v_tail_2598_; uint8_t v___x_2599_; 
v_key_2596_ = lean_ctor_get(v_x_2594_, 0);
v_value_2597_ = lean_ctor_get(v_x_2594_, 1);
v_tail_2598_ = lean_ctor_get(v_x_2594_, 2);
v___x_2599_ = lean_name_eq(v_key_2596_, v_a_2593_);
if (v___x_2599_ == 0)
{
v_x_2594_ = v_tail_2598_;
goto _start;
}
else
{
lean_object* v___x_2601_; 
lean_inc(v_value_2597_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v_value_2597_);
return v___x_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_2602_, lean_object* v_x_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2602_, v_x_2603_);
lean_dec(v_x_2603_);
lean_dec(v_a_2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_buckets_2607_; lean_object* v___x_2608_; uint64_t v___y_2610_; 
v_buckets_2607_ = lean_ctor_get(v_m_2605_, 1);
v___x_2608_ = lean_array_get_size(v_buckets_2607_);
if (lean_obj_tag(v_a_2606_) == 0)
{
uint64_t v___x_2624_; 
v___x_2624_ = 1723ULL;
v___y_2610_ = v___x_2624_;
goto v___jp_2609_;
}
else
{
uint64_t v_hash_2625_; 
v_hash_2625_ = lean_ctor_get_uint64(v_a_2606_, sizeof(void*)*2);
v___y_2610_ = v_hash_2625_;
goto v___jp_2609_;
}
v___jp_2609_:
{
uint64_t v___x_2611_; uint64_t v___x_2612_; uint64_t v_fold_2613_; uint64_t v___x_2614_; uint64_t v___x_2615_; uint64_t v___x_2616_; size_t v___x_2617_; size_t v___x_2618_; size_t v___x_2619_; size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2611_ = 32ULL;
v___x_2612_ = lean_uint64_shift_right(v___y_2610_, v___x_2611_);
v_fold_2613_ = lean_uint64_xor(v___y_2610_, v___x_2612_);
v___x_2614_ = 16ULL;
v___x_2615_ = lean_uint64_shift_right(v_fold_2613_, v___x_2614_);
v___x_2616_ = lean_uint64_xor(v_fold_2613_, v___x_2615_);
v___x_2617_ = lean_uint64_to_usize(v___x_2616_);
v___x_2618_ = lean_usize_of_nat(v___x_2608_);
v___x_2619_ = ((size_t)1ULL);
v___x_2620_ = lean_usize_sub(v___x_2618_, v___x_2619_);
v___x_2621_ = lean_usize_land(v___x_2617_, v___x_2620_);
v___x_2622_ = lean_array_uget_borrowed(v_buckets_2607_, v___x_2621_);
v___x_2623_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2606_, v___x_2622_);
return v___x_2623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2626_, lean_object* v_a_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_2626_, v_a_2627_);
lean_dec(v_a_2627_);
lean_dec_ref(v_m_2626_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object* v___x_2629_, lean_object* v_declName_2630_, lean_object* v_as_2631_, size_t v_sz_2632_, size_t v_i_2633_, lean_object* v_b_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
uint8_t v___x_2644_; 
v___x_2644_ = lean_usize_dec_lt(v_i_2633_, v_sz_2632_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; 
lean_dec(v_declName_2630_);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v_b_2634_);
return v___x_2645_;
}
else
{
lean_object* v___x_2646_; lean_object* v_modules_2647_; lean_object* v___x_2648_; lean_object* v_a_2649_; lean_object* v___x_2650_; lean_object* v_toImport_2651_; lean_object* v_module_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; lean_object* v___x_2655_; 
v___x_2646_ = l_Lean_Environment_header(v___x_2629_);
v_modules_2647_ = lean_ctor_get(v___x_2646_, 3);
lean_inc_ref(v_modules_2647_);
lean_dec_ref(v___x_2646_);
v___x_2648_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2649_ = lean_array_uget_borrowed(v_as_2631_, v_i_2633_);
v___x_2650_ = lean_array_get(v___x_2648_, v_modules_2647_, v_a_2649_);
lean_dec_ref(v_modules_2647_);
v_toImport_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc_ref(v_toImport_2651_);
lean_dec(v___x_2650_);
v_module_2652_ = lean_ctor_get(v_toImport_2651_, 0);
lean_inc(v_module_2652_);
lean_dec_ref(v_toImport_2651_);
v___x_2653_ = lean_box(0);
v___x_2654_ = 0;
lean_inc(v_declName_2630_);
v___x_2655_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2652_, v___x_2654_, v_declName_2630_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
if (lean_obj_tag(v___x_2655_) == 0)
{
size_t v___x_2656_; size_t v___x_2657_; 
lean_dec_ref_known(v___x_2655_, 1);
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_add(v_i_2633_, v___x_2656_);
v_i_2633_ = v___x_2657_;
v_b_2634_ = v___x_2653_;
goto _start;
}
else
{
lean_dec(v_declName_2630_);
return v___x_2655_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2659_, lean_object* v_declName_2660_, lean_object* v_as_2661_, lean_object* v_sz_2662_, lean_object* v_i_2663_, lean_object* v_b_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
size_t v_sz_boxed_2674_; size_t v_i_boxed_2675_; lean_object* v_res_2676_; 
v_sz_boxed_2674_ = lean_unbox_usize(v_sz_2662_);
lean_dec(v_sz_2662_);
v_i_boxed_2675_ = lean_unbox_usize(v_i_2663_);
lean_dec(v_i_2663_);
v_res_2676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v___x_2659_, v_declName_2660_, v_as_2661_, v_sz_boxed_2674_, v_i_boxed_2675_, v_b_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec_ref(v_as_2661_);
lean_dec_ref(v___x_2659_);
return v_res_2676_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object* v_declName_2680_, uint8_t v_isMeta_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v_env_2696_; lean_object* v___y_2698_; lean_object* v___x_2711_; 
v___x_2691_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0);
v___x_2692_ = lean_st_ref_get(v___y_2689_);
v_env_2696_ = lean_ctor_get(v___x_2692_, 0);
lean_inc_ref(v_env_2696_);
lean_dec(v___x_2692_);
v___x_2711_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2696_, v_declName_2680_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_dec_ref(v_env_2696_);
lean_dec(v_declName_2680_);
goto v___jp_2693_;
}
else
{
lean_object* v_val_2712_; lean_object* v___x_2713_; lean_object* v_modules_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_val_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = l_Lean_Environment_header(v_env_2696_);
v_modules_2714_ = lean_ctor_get(v___x_2713_, 3);
lean_inc_ref(v_modules_2714_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = lean_array_get_size(v_modules_2714_);
v___x_2716_ = lean_nat_dec_lt(v_val_2712_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_dec_ref(v_modules_2714_);
lean_dec(v_val_2712_);
lean_dec_ref(v_env_2696_);
lean_dec(v_declName_2680_);
goto v___jp_2693_;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___y_2720_; 
v___x_2717_ = lean_array_fget(v_modules_2714_, v_val_2712_);
lean_dec(v_val_2712_);
lean_dec_ref(v_modules_2714_);
v___x_2718_ = lean_st_ref_get(v___y_2689_);
if (v_isMeta_2681_ == 0)
{
lean_dec(v___x_2718_);
v___y_2720_ = v_isMeta_2681_;
goto v___jp_2719_;
}
else
{
lean_object* v_env_2731_; uint8_t v___x_2732_; 
v_env_2731_ = lean_ctor_get(v___x_2718_, 0);
lean_inc_ref(v_env_2731_);
lean_dec(v___x_2718_);
lean_inc(v_declName_2680_);
v___x_2732_ = l_Lean_isMarkedMeta(v_env_2731_, v_declName_2680_);
if (v___x_2732_ == 0)
{
v___y_2720_ = v_isMeta_2681_;
goto v___jp_2719_;
}
else
{
uint8_t v___x_2733_; 
v___x_2733_ = 0;
v___y_2720_ = v___x_2733_;
goto v___jp_2719_;
}
}
v___jp_2719_:
{
lean_object* v_toImport_2721_; lean_object* v_module_2722_; lean_object* v___x_2723_; 
v_toImport_2721_ = lean_ctor_get(v___x_2717_, 0);
lean_inc_ref(v_toImport_2721_);
lean_dec(v___x_2717_);
v_module_2722_ = lean_ctor_get(v_toImport_2721_, 0);
lean_inc(v_module_2722_);
lean_dec_ref(v_toImport_2721_);
lean_inc(v_declName_2680_);
v___x_2723_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2722_, v___y_2720_, v_declName_2680_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec_ref_known(v___x_2723_, 1);
v___x_2724_ = l_Lean_indirectModUseExt;
v___x_2725_ = lean_box(1);
v___x_2726_ = lean_box(0);
lean_inc_ref(v_env_2696_);
v___x_2727_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2691_, v___x_2724_, v_env_2696_, v___x_2725_, v___x_2726_);
v___x_2728_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v___x_2727_, v_declName_2680_);
lean_dec(v___x_2727_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v___x_2729_; 
v___x_2729_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1));
v___y_2698_ = v___x_2729_;
goto v___jp_2697_;
}
else
{
lean_object* v_val_2730_; 
v_val_2730_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_val_2730_);
lean_dec_ref_known(v___x_2728_, 1);
v___y_2698_ = v_val_2730_;
goto v___jp_2697_;
}
}
else
{
lean_dec_ref(v_env_2696_);
lean_dec(v_declName_2680_);
return v___x_2723_;
}
}
}
}
v___jp_2693_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
return v___x_2695_;
}
v___jp_2697_:
{
lean_object* v___x_2699_; size_t v_sz_2700_; size_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2699_ = lean_box(0);
v_sz_2700_ = lean_array_size(v___y_2698_);
v___x_2701_ = ((size_t)0ULL);
v___x_2702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v_env_2696_, v_declName_2680_, v___y_2698_, v_sz_2700_, v___x_2701_, v___x_2699_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec_ref(v___y_2698_);
lean_dec_ref(v_env_2696_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; 
v_unused_2710_ = lean_ctor_get(v___x_2702_, 0);
lean_dec(v_unused_2710_);
v___x_2704_ = v___x_2702_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_dec(v___x_2702_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 0, v___x_2699_);
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2699_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
else
{
return v___x_2702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object* v_declName_2734_, lean_object* v_isMeta_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
uint8_t v_isMeta_boxed_2745_; lean_object* v_res_2746_; 
v_isMeta_boxed_2745_ = lean_unbox(v_isMeta_2735_);
v_res_2746_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_declName_2734_, v_isMeta_boxed_2745_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object* v_as_x27_2747_, lean_object* v_b_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
if (lean_obj_tag(v_as_x27_2747_) == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_b_2748_);
return v___x_2758_;
}
else
{
lean_object* v_head_2759_; lean_object* v_tail_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; lean_object* v___x_2763_; 
v_head_2759_ = lean_ctor_get(v_as_x27_2747_, 0);
v_tail_2760_ = lean_ctor_get(v_as_x27_2747_, 1);
v___x_2761_ = lean_box(0);
v___x_2762_ = 1;
lean_inc(v_head_2759_);
v___x_2763_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_head_2759_, v___x_2762_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_dec_ref_known(v___x_2763_, 1);
v_as_x27_2747_ = v_tail_2760_;
v_b_2748_ = v___x_2761_;
goto _start;
}
else
{
return v___x_2763_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2765_, lean_object* v_b_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_2765_, v_b_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v_as_x27_2765_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object* v_x_2777_, lean_object* v___y_2778_){
_start:
{
if (lean_obj_tag(v_x_2777_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; 
v_a_2779_ = lean_ctor_get(v_x_2777_, 0);
lean_inc(v_a_2779_);
v___x_2780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2780_, 0, v_a_2779_);
lean_ctor_set(v___x_2780_, 1, v___y_2778_);
return v___x_2780_;
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2782_; 
v_a_2781_ = lean_ctor_get(v_x_2777_, 0);
lean_inc(v_a_2781_);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_a_2781_);
lean_ctor_set(v___x_2782_, 1, v___y_2778_);
return v___x_2782_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object* v_x_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_2783_, v___y_2784_);
lean_dec_ref(v_x_2783_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(lean_object* v_env_2786_, lean_object* v_stx_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2786_, v_stx_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
if (lean_obj_tag(v_a_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2800_; 
v_a_2792_ = lean_ctor_get(v___x_2790_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v___x_2790_, 0);
lean_dec(v_unused_2801_);
v___x_2794_ = v___x_2790_;
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2790_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2796_ = lean_box(0);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 0, v___x_2796_);
v___x_2798_ = v___x_2794_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_a_2792_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
else
{
lean_object* v_val_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2830_; 
v_val_2802_ = lean_ctor_get(v_a_2791_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_a_2791_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2804_ = v_a_2791_;
v_isShared_2805_ = v_isSharedCheck_2830_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_val_2802_);
lean_dec(v_a_2791_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2830_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v_snd_2806_; 
v_snd_2806_ = lean_ctor_get(v_val_2802_, 1);
lean_inc(v_snd_2806_);
lean_dec(v_val_2802_);
if (lean_obj_tag(v_snd_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2816_; 
lean_del_object(v___x_2804_);
v_a_2807_ = lean_ctor_get(v___x_2790_, 1);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2790_, 2);
v_a_2808_ = lean_ctor_get(v_snd_2806_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_snd_2806_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2810_ = v_snd_2806_;
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v_snd_2806_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2813_, v_a_2807_);
lean_dec_ref(v___x_2813_);
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2829_; 
v_a_2817_ = lean_ctor_get(v___x_2790_, 1);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2790_, 2);
v_a_2818_ = lean_ctor_get(v_snd_2806_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_snd_2806_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2820_ = v_snd_2806_;
v_isShared_2821_ = v_isSharedCheck_2829_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v_snd_2806_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2829_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v_a_2818_);
v___x_2823_ = v___x_2804_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2823_);
v___x_2825_ = v___x_2820_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; 
v___x_2826_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2825_, v_a_2817_);
lean_dec_ref(v___x_2825_);
return v___x_2826_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2831_; lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_a_2831_ = lean_ctor_get(v___x_2790_, 0);
v_a_2832_ = lean_ctor_get(v___x_2790_, 1);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2790_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_inc(v_a_2831_);
lean_dec(v___x_2790_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2831_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(lean_object* v_env_2840_, lean_object* v_stx_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(v_env_2840_, v_stx_2841_, v___y_2842_, v___y_2843_);
lean_dec_ref(v___y_2842_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(lean_object* v_x_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; lean_object* v_toCold_2857_; lean_object* v_env_2858_; lean_object* v_currRecDepth_2859_; lean_object* v_ref_2860_; lean_object* v_maxRecDepth_2861_; lean_object* v_currNamespace_2862_; lean_object* v_openDecls_2863_; lean_object* v_quotContext_2864_; lean_object* v_currMacroScope_2865_; lean_object* v___f_2866_; lean_object* v___f_2867_; lean_object* v___x_2868_; lean_object* v___f_2869_; lean_object* v___f_2870_; lean_object* v___f_2871_; lean_object* v_methods_2872_; lean_object* v___x_2873_; lean_object* v_nextMacroScope_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2856_ = lean_st_ref_get(v___y_2854_);
v_toCold_2857_ = lean_ctor_get(v___y_2853_, 0);
v_env_2858_ = lean_ctor_get(v___x_2856_, 0);
lean_inc_ref_n(v_env_2858_, 4);
lean_dec(v___x_2856_);
v_currRecDepth_2859_ = lean_ctor_get(v___y_2853_, 1);
v_ref_2860_ = lean_ctor_get(v___y_2853_, 2);
v_maxRecDepth_2861_ = lean_ctor_get(v_toCold_2857_, 3);
v_currNamespace_2862_ = lean_ctor_get(v_toCold_2857_, 4);
v_openDecls_2863_ = lean_ctor_get(v_toCold_2857_, 5);
v_quotContext_2864_ = lean_ctor_get(v_toCold_2857_, 8);
v_currMacroScope_2865_ = lean_ctor_get(v_toCold_2857_, 9);
v___f_2866_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2866_, 0, v_env_2858_);
v___f_2867_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2867_, 0, v_env_2858_);
v___x_2868_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2853_);
lean_inc_n(v_currNamespace_2862_, 3);
v___f_2869_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2869_, 0, v_currNamespace_2862_);
lean_inc_n(v_openDecls_2863_, 2);
v___f_2870_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_2870_, 0, v_env_2858_);
lean_closure_set(v___f_2870_, 1, v___x_2868_);
lean_closure_set(v___f_2870_, 2, v_currNamespace_2862_);
lean_closure_set(v___f_2870_, 3, v_openDecls_2863_);
v___f_2871_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2871_, 0, v_env_2858_);
lean_closure_set(v___f_2871_, 1, v_currNamespace_2862_);
lean_closure_set(v___f_2871_, 2, v_openDecls_2863_);
v_methods_2872_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2872_, 0, v___f_2867_);
lean_ctor_set(v_methods_2872_, 1, v___f_2869_);
lean_ctor_set(v_methods_2872_, 2, v___f_2866_);
lean_ctor_set(v_methods_2872_, 3, v___f_2871_);
lean_ctor_set(v_methods_2872_, 4, v___f_2870_);
v___x_2873_ = lean_st_ref_get(v___y_2854_);
v_nextMacroScope_2874_ = lean_ctor_get(v___x_2873_, 1);
lean_inc(v_nextMacroScope_2874_);
lean_dec(v___x_2873_);
lean_inc(v_ref_2860_);
lean_inc(v_maxRecDepth_2861_);
lean_inc(v_currRecDepth_2859_);
lean_inc(v_currMacroScope_2865_);
lean_inc(v_quotContext_2864_);
v___x_2875_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2875_, 0, v_methods_2872_);
lean_ctor_set(v___x_2875_, 1, v_quotContext_2864_);
lean_ctor_set(v___x_2875_, 2, v_currMacroScope_2865_);
lean_ctor_set(v___x_2875_, 3, v_currRecDepth_2859_);
lean_ctor_set(v___x_2875_, 4, v_maxRecDepth_2861_);
lean_ctor_set(v___x_2875_, 5, v_ref_2860_);
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2877_, 0, v_nextMacroScope_2874_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
lean_ctor_set(v___x_2877_, 2, v___x_2876_);
v___x_2878_ = lean_apply_2(v_x_2846_, v___x_2875_, v___x_2877_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v_a_2880_; lean_object* v_macroScope_2881_; lean_object* v_traceMsgs_2882_; lean_object* v_expandedMacroDecls_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 1);
lean_inc(v_a_2879_);
v_a_2880_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2878_, 2);
v_macroScope_2881_ = lean_ctor_get(v_a_2879_, 0);
lean_inc(v_macroScope_2881_);
v_traceMsgs_2882_ = lean_ctor_get(v_a_2879_, 1);
lean_inc(v_traceMsgs_2882_);
v_expandedMacroDecls_2883_ = lean_ctor_get(v_a_2879_, 2);
lean_inc(v_expandedMacroDecls_2883_);
lean_dec(v_a_2879_);
v___x_2884_ = lean_box(0);
v___x_2885_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_expandedMacroDecls_2883_, v___x_2884_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v_expandedMacroDecls_2883_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v___x_2886_; lean_object* v_env_2887_; lean_object* v_ngen_2888_; lean_object* v_auxDeclNGen_2889_; lean_object* v_traceState_2890_; lean_object* v_cache_2891_; lean_object* v_recordedDeps_2892_; lean_object* v_messages_2893_; lean_object* v_infoState_2894_; lean_object* v_snapshotTasks_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref_known(v___x_2885_, 1);
v___x_2886_ = lean_st_ref_take(v___y_2854_);
v_env_2887_ = lean_ctor_get(v___x_2886_, 0);
v_ngen_2888_ = lean_ctor_get(v___x_2886_, 2);
v_auxDeclNGen_2889_ = lean_ctor_get(v___x_2886_, 3);
v_traceState_2890_ = lean_ctor_get(v___x_2886_, 4);
v_cache_2891_ = lean_ctor_get(v___x_2886_, 5);
v_recordedDeps_2892_ = lean_ctor_get(v___x_2886_, 6);
v_messages_2893_ = lean_ctor_get(v___x_2886_, 7);
v_infoState_2894_ = lean_ctor_get(v___x_2886_, 8);
v_snapshotTasks_2895_ = lean_ctor_get(v___x_2886_, 9);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2921_ == 0)
{
lean_object* v_unused_2922_; 
v_unused_2922_ = lean_ctor_get(v___x_2886_, 1);
lean_dec(v_unused_2922_);
v___x_2897_ = v___x_2886_;
v_isShared_2898_ = v_isSharedCheck_2921_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_snapshotTasks_2895_);
lean_inc(v_infoState_2894_);
lean_inc(v_messages_2893_);
lean_inc(v_recordedDeps_2892_);
lean_inc(v_cache_2891_);
lean_inc(v_traceState_2890_);
lean_inc(v_auxDeclNGen_2889_);
lean_inc(v_ngen_2888_);
lean_inc(v_env_2887_);
lean_dec(v___x_2886_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2921_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 1, v_macroScope_2881_);
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_env_2887_);
lean_ctor_set(v_reuseFailAlloc_2920_, 1, v_macroScope_2881_);
lean_ctor_set(v_reuseFailAlloc_2920_, 2, v_ngen_2888_);
lean_ctor_set(v_reuseFailAlloc_2920_, 3, v_auxDeclNGen_2889_);
lean_ctor_set(v_reuseFailAlloc_2920_, 4, v_traceState_2890_);
lean_ctor_set(v_reuseFailAlloc_2920_, 5, v_cache_2891_);
lean_ctor_set(v_reuseFailAlloc_2920_, 6, v_recordedDeps_2892_);
lean_ctor_set(v_reuseFailAlloc_2920_, 7, v_messages_2893_);
lean_ctor_set(v_reuseFailAlloc_2920_, 8, v_infoState_2894_);
lean_ctor_set(v_reuseFailAlloc_2920_, 9, v_snapshotTasks_2895_);
v___x_2900_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = lean_st_ref_put(v___y_2854_, v___x_2900_);
v___x_2902_ = l_List_reverse___redArg(v_traceMsgs_2882_);
v___x_2903_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v___x_2902_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v___x_2903_, 0);
lean_dec(v_unused_2911_);
v___x_2905_ = v___x_2903_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_dec(v___x_2903_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v_a_2880_);
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2880_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2880_);
v_a_2912_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2903_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2903_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_traceMsgs_2882_);
lean_dec(v_macroScope_2881_);
lean_dec(v_a_2880_);
v_a_2923_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2885_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2885_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
else
{
lean_object* v_a_2931_; 
v_a_2931_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2931_);
lean_dec_ref_known(v___x_2878_, 2);
if (lean_obj_tag(v_a_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v_a_2933_; lean_object* v___x_2934_; uint8_t v___x_2935_; 
v_a_2932_ = lean_ctor_get(v_a_2931_, 0);
lean_inc(v_a_2932_);
v_a_2933_ = lean_ctor_get(v_a_2931_, 1);
lean_inc_ref(v_a_2933_);
lean_dec_ref_known(v_a_2931_, 2);
v___x_2934_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0));
v___x_2935_ = lean_string_dec_eq(v_a_2933_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_a_2933_);
v___x_2937_ = l_Lean_MessageData_ofFormat(v___x_2936_);
v___x_2938_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_a_2932_, v___x_2937_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v_a_2932_);
return v___x_2938_;
}
else
{
lean_object* v___x_2939_; 
lean_dec_ref(v_a_2933_);
v___x_2939_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_a_2932_);
return v___x_2939_;
}
}
else
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(lean_object* v_x_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object* v_x_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_){
_start:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
lean_inc(v_x_2962_);
v___x_2973_ = l_Lean_Syntax_isOfKind(v_x_2962_, v___x_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; 
lean_dec(v_x_2962_);
v___x_2974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2974_;
}
else
{
lean_object* v___x_2975_; lean_object* v_hyp_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2975_ = lean_unsigned_to_nat(1u);
v_hyp_2976_ = l_Lean_Syntax_getArg(v_x_2962_, v___x_2975_);
v___x_2977_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4));
lean_inc(v_hyp_2976_);
v___x_2978_ = l_Lean_Syntax_isOfKind(v_hyp_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_dec(v_hyp_2976_);
lean_dec(v_x_2962_);
v___x_2979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2979_;
}
else
{
lean_object* v___x_2980_; lean_object* v_pat_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2980_ = lean_unsigned_to_nat(3u);
v_pat_2981_ = l_Lean_Syntax_getArg(v_x_2962_, v___x_2980_);
lean_dec(v_x_2962_);
v___x_2982_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MCasesPat_parse___boxed), 3, 1);
lean_closure_set(v___x_2982_, 0, v_pat_2981_);
v___x_2983_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v___x_2982_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2964_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v_fst_2987_; lean_object* v_snd_2988_; lean_object* v___f_2989_; lean_object* v___x_2990_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v_fst_2987_ = lean_ctor_get(v_a_2986_, 0);
lean_inc_n(v_fst_2987_, 2);
v_snd_2988_ = lean_ctor_get(v_a_2986_, 1);
lean_inc(v_snd_2988_);
lean_dec(v_a_2986_);
v___f_2989_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2989_, 0, v_snd_2988_);
lean_closure_set(v___f_2989_, 1, v_hyp_2976_);
lean_closure_set(v___f_2989_, 2, v_a_2984_);
lean_closure_set(v___f_2989_, 3, v_fst_2987_);
v___x_2990_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_fst_2987_, v___f_2989_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_);
return v___x_2990_;
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec(v_a_2984_);
lean_dec(v_hyp_2976_);
v_a_2991_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2985_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2985_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec(v_hyp_2976_);
v_a_2999_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2983_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2983_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object* v_x_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v_res_3017_; 
v_res_3017_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(v_x_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_);
lean_dec(v_a_3015_);
lean_dec_ref(v_a_3014_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object* v_00_u03b1_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_3019_, v___y_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3023_, lean_object* v_x_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(v_00_u03b1_3023_, v_x_3024_, v___y_3025_, v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v_x_3024_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object* v_00_u03b1_3028_, lean_object* v_ref_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_3029_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_ref_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(v_00_u03b1_3040_, v_ref_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object* v_00_u03b1_3052_, lean_object* v_x_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object* v_00_u03b1_3064_, lean_object* v_x_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(v_00_u03b1_3064_, v_x_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3070_);
lean_dec(v___y_3069_);
lean_dec_ref(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec_ref(v___y_3066_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object* v_mvarId_3076_, lean_object* v_val_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_3076_, v_val_3077_, v___y_3083_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object* v_mvarId_3088_, lean_object* v_val_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(v_mvarId_3088_, v_val_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec_ref(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object* v_cls_3100_, lean_object* v_msg_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_3100_, v_msg_3101_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object* v_cls_3112_, lean_object* v_msg_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_3112_, v_msg_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object* v_as_3124_, lean_object* v_as_x27_3125_, lean_object* v_b_3126_, lean_object* v_a_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_3125_, v_b_3126_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object* v_as_3138_, lean_object* v_as_x27_3139_, lean_object* v_b_3140_, lean_object* v_a_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_as_3138_, v_as_x27_3139_, v_b_3140_, v_a_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v_as_x27_3139_);
lean_dec(v_as_3138_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object* v_00_u03b1_3152_, lean_object* v_ref_3153_, lean_object* v_msg_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_3153_, v_msg_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3165_, lean_object* v_ref_3166_, lean_object* v_msg_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v_00_u03b1_3165_, v_ref_3166_, v_msg_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v_ref_3166_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(lean_object* v_00_u03b2_3178_, lean_object* v_x_3179_, lean_object* v_x_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_x_3179_, v_x_3180_, v_x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3183_, lean_object* v_m_3184_, lean_object* v_a_3185_){
_start:
{
lean_object* v___x_3186_; 
v___x_3186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_3184_, v_a_3185_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3187_, lean_object* v_m_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(v_00_u03b2_3187_, v_m_3188_, v_a_3189_);
lean_dec(v_a_3189_);
lean_dec_ref(v_m_3188_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_3191_, lean_object* v_msg_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v___x_3202_; 
v___x_3202_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_3192_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_3203_, lean_object* v_msg_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(v_00_u03b1_3203_, v_msg_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(lean_object* v_00_u03b2_3215_, lean_object* v_x_3216_, size_t v_x_3217_, size_t v_x_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_3216_, v_x_3217_, v_x_3218_, v_x_3219_, v_x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(lean_object* v_00_u03b2_3222_, lean_object* v_x_3223_, lean_object* v_x_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
size_t v_x_21497__boxed_3228_; size_t v_x_21498__boxed_3229_; lean_object* v_res_3230_; 
v_x_21497__boxed_3228_ = lean_unbox_usize(v_x_3224_);
lean_dec(v_x_3224_);
v_x_21498__boxed_3229_ = lean_unbox_usize(v_x_3225_);
lean_dec(v_x_3225_);
v_res_3230_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(v_00_u03b2_3222_, v_x_3223_, v_x_21497__boxed_3228_, v_x_21498__boxed_3229_, v_x_3226_, v_x_3227_);
return v_res_3230_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_){
_start:
{
uint8_t v___x_3234_; 
v___x_3234_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_3232_, v_x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3235_, lean_object* v_x_3236_, lean_object* v_x_3237_){
_start:
{
uint8_t v_res_3238_; lean_object* v_r_3239_; 
v_res_3238_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(v_00_u03b2_3235_, v_x_3236_, v_x_3237_);
lean_dec_ref(v_x_3237_);
lean_dec_ref(v_x_3236_);
v_r_3239_ = lean_box(v_res_3238_);
return v_r_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3240_, lean_object* v_a_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_3241_, v_x_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3244_, lean_object* v_a_3245_, lean_object* v_x_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(v_00_u03b2_3244_, v_a_3245_, v_x_3246_);
lean_dec(v_x_3246_);
lean_dec(v_a_3245_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_3248_, lean_object* v_n_3249_, lean_object* v_k_3250_, lean_object* v_v_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v_n_3249_, v_k_3250_, v_v_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_3253_, size_t v_depth_3254_, lean_object* v_keys_3255_, lean_object* v_vals_3256_, lean_object* v_heq_3257_, lean_object* v_i_3258_, lean_object* v_entries_3259_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_3254_, v_keys_3255_, v_vals_3256_, v_i_3258_, v_entries_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3261_, lean_object* v_depth_3262_, lean_object* v_keys_3263_, lean_object* v_vals_3264_, lean_object* v_heq_3265_, lean_object* v_i_3266_, lean_object* v_entries_3267_){
_start:
{
size_t v_depth_boxed_3268_; lean_object* v_res_3269_; 
v_depth_boxed_3268_ = lean_unbox_usize(v_depth_3262_);
lean_dec(v_depth_3262_);
v_res_3269_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(v_00_u03b2_3261_, v_depth_boxed_3268_, v_keys_3263_, v_vals_3264_, v_heq_3265_, v_i_3266_, v_entries_3267_);
lean_dec_ref(v_vals_3264_);
lean_dec_ref(v_keys_3263_);
return v_res_3269_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_3270_, lean_object* v_x_3271_, size_t v_x_3272_, lean_object* v_x_3273_){
_start:
{
uint8_t v___x_3274_; 
v___x_3274_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_3271_, v_x_3272_, v_x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(lean_object* v_00_u03b2_3275_, lean_object* v_x_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_){
_start:
{
size_t v_x_21531__boxed_3279_; uint8_t v_res_3280_; lean_object* v_r_3281_; 
v_x_21531__boxed_3279_ = lean_unbox_usize(v_x_3277_);
lean_dec(v_x_3277_);
v_res_3280_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(v_00_u03b2_3275_, v_x_3276_, v_x_21531__boxed_3279_, v_x_3278_);
lean_dec_ref(v_x_3278_);
lean_dec_ref(v_x_3276_);
v_r_3281_ = lean_box(v_res_3280_);
return v_r_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(lean_object* v_00_u03b2_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_x_3283_, v_x_3284_, v_x_3285_, v_x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object* v_00_u03b2_3288_, lean_object* v_keys_3289_, lean_object* v_vals_3290_, lean_object* v_heq_3291_, lean_object* v_i_3292_, lean_object* v_k_3293_){
_start:
{
uint8_t v___x_3294_; 
v___x_3294_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_3289_, v_i_3292_, v_k_3293_);
return v___x_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3295_, lean_object* v_keys_3296_, lean_object* v_vals_3297_, lean_object* v_heq_3298_, lean_object* v_i_3299_, lean_object* v_k_3300_){
_start:
{
uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_res_3301_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(v_00_u03b2_3295_, v_keys_3296_, v_vals_3297_, v_heq_3298_, v_i_3299_, v_k_3300_);
lean_dec_ref(v_k_3300_);
lean_dec_ref(v_vals_3297_);
lean_dec_ref(v_keys_3296_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1(){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3312_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3313_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1));
v___x_3315_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed), 10, 0);
v___x_3316_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3312_, v___x_3313_, v___x_3314_, v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
return v_res_3318_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Pure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Cases(builtin);
}
#ifdef __cplusplus
}
#endif
