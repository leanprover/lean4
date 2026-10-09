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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___redArg();
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___lam__0(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_319_; lean_object* v_env_320_; uint8_t v___x_321_; lean_object* v_env_322_; lean_object* v___x_323_; lean_object* v_toCold_324_; lean_object* v_mctx_325_; lean_object* v_lctx_326_; lean_object* v_options_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_319_ = lean_st_ref_get(v___y_317_);
v_env_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_env_320_);
lean_dec(v___x_319_);
v___x_321_ = 0;
v_env_322_ = l_Lean_Environment_setRecordingDeps(v_env_320_, v___x_321_);
v___x_323_ = lean_st_ref_get(v___y_315_);
v_toCold_324_ = lean_ctor_get(v___y_316_, 0);
v_mctx_325_ = lean_ctor_get(v___x_323_, 0);
lean_inc_ref(v_mctx_325_);
lean_dec(v___x_323_);
v_lctx_326_ = lean_ctor_get(v___y_314_, 2);
v_options_327_ = lean_ctor_get(v_toCold_324_, 2);
lean_inc_ref(v_options_327_);
lean_inc_ref(v_lctx_326_);
v___x_328_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_328_, 0, v_env_322_);
lean_ctor_set(v___x_328_, 1, v_mctx_325_);
lean_ctor_set(v___x_328_, 2, v_lctx_326_);
lean_ctor_set(v___x_328_, 3, v_options_327_);
v___x_329_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_msgData_313_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0___boxed(lean_object* v_msgData_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msgData_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(lean_object* v_msg_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_ref_344_; lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_354_; 
v_ref_344_ = lean_ctor_get(v___y_341_, 2);
v___x_345_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_354_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_354_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_352_; 
lean_inc(v_ref_344_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v_ref_344_);
lean_ctor_set(v___x_350_, 1, v_a_346_);
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 1);
lean_ctor_set(v___x_348_, 0, v___x_350_);
v___x_352_ = v___x_348_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg___boxed(lean_object* v_msg_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_361_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__0));
v___x_364_ = l_Lean_stringToMessageData(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(lean_object* v_goal_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_hyps_371_; lean_object* v___x_372_; 
v_hyps_371_ = lean_ctor_get(v_goal_365_, 2);
lean_inc_ref(v_hyps_371_);
lean_dec_ref(v_goal_365_);
v___x_372_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_hyps_371_);
if (lean_obj_tag(v___x_372_) == 1)
{
lean_object* v_val_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_382_; 
lean_dec_ref(v_hyps_371_);
v_val_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_382_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_val_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v_snd_377_; lean_object* v_snd_378_; lean_object* v___x_380_; 
v_snd_377_ = lean_ctor_get(v_val_373_, 1);
lean_inc(v_snd_377_);
lean_dec(v_val_373_);
v_snd_378_ = lean_ctor_get(v_snd_377_, 1);
lean_inc(v_snd_378_);
lean_dec(v_snd_377_);
if (v_isShared_376_ == 0)
{
lean_ctor_set_tag(v___x_375_, 0);
lean_ctor_set(v___x_375_, 0, v_snd_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_snd_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_dec(v___x_372_);
v___x_383_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1, &l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___closed__1);
v___x_384_ = l_Lean_MessageData_ofExpr(v_hyps_371_);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_385_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH___boxed(lean_object* v_goal_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_goal_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(lean_object* v_00_u03b1_394_, lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___boxed(lean_object* v_00_u03b1_402_, lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0(v_00_u03b1_402_, v_msg_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(lean_object* v___x_410_, lean_object* v_snd_411_, lean_object* v_k_412_, uint8_t v___x_413_, lean_object* v___x_414_, lean_object* v___x_415_, lean_object* v___x_416_, lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_H_420_, lean_object* v_x_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_lctx_427_; lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; 
v_lctx_427_ = lean_ctor_get(v___y_422_, 2);
lean_inc_ref(v___x_410_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_410_);
v___x_429_ = 0;
lean_inc_ref(v_x_421_);
lean_inc_ref(v_lctx_427_);
v___x_430_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_411_, v_lctx_427_, v_x_421_, v___x_428_, v___x_429_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_431_; 
lean_dec_ref_known(v___x_430_, 1);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc_ref(v_x_421_);
v___x_431_ = lean_apply_6(v_k_412_, v_x_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, lean_box(0));
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v_snd_433_; lean_object* v_fst_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_519_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v___x_431_, 1);
v_snd_433_ = lean_ctor_get(v_a_432_, 1);
v_fst_434_ = lean_ctor_get(v_a_432_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v_a_432_);
if (v_isSharedCheck_519_ == 0)
{
v___x_436_ = v_a_432_;
v_isShared_437_ = v_isSharedCheck_519_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snd_433_);
lean_inc(v_fst_434_);
lean_dec(v_a_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_519_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_518_; 
v_fst_438_ = lean_ctor_get(v_snd_433_, 0);
v_snd_439_ = lean_ctor_get(v_snd_433_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_snd_433_);
if (v_isSharedCheck_518_ == 0)
{
v___x_441_ = v_snd_433_;
v_isShared_442_ = v_isSharedCheck_518_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_inc(v_fst_438_);
lean_dec(v_snd_433_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_518_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; 
lean_inc(v_fst_438_);
v___x_443_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_438_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v_fst_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_508_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v_fst_445_ = lean_ctor_get(v_a_444_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v_a_444_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v_a_444_, 1);
lean_dec(v_unused_509_);
v___x_447_ = v_a_444_;
v_isShared_448_ = v_isSharedCheck_508_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_fst_445_);
lean_dec(v_a_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_508_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; 
lean_inc_ref(v___x_410_);
v___x_449_ = l_Lean_Meta_getLevel(v___x_410_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; lean_object* v___x_455_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_mk_empty_array_with_capacity(v___x_451_);
v___x_453_ = lean_array_push(v___x_452_, v_x_421_);
v___x_454_ = 1;
v___x_455_ = l_Lean_Meta_mkLambdaFVars(v___x_453_, v_snd_439_, v___x_429_, v___x_413_, v___x_429_, v___x_413_, v___x_454_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec_ref(v___x_453_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_491_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_491_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_491_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_491_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_u_460_; lean_object* v_00_u03c3s_461_; lean_object* v_target_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_489_; 
v_u_460_ = lean_ctor_get(v_fst_438_, 0);
v_00_u03c3s_461_ = lean_ctor_get(v_fst_438_, 1);
v_target_462_ = lean_ctor_get(v_fst_438_, 3);
v_isSharedCheck_489_ = !lean_is_exclusive(v_fst_438_);
if (v_isSharedCheck_489_ == 0)
{
lean_object* v_unused_490_; 
v_unused_490_ = lean_ctor_get(v_fst_438_, 2);
lean_dec(v_unused_490_);
v___x_464_ = v_fst_438_;
v_isShared_465_ = v_isSharedCheck_489_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_target_462_);
lean_inc(v_00_u03c3s_461_);
lean_inc(v_u_460_);
lean_dec(v_fst_438_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_489_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_466_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_467_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__15_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_468_ = l_Lean_Name_mkStr6(v___x_414_, v___x_415_, v___x_416_, v___x_466_, v___x_467_, v___x_417_);
v___x_469_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 1);
lean_ctor_set(v___x_436_, 1, v___x_469_);
lean_ctor_set(v___x_436_, 0, v_a_450_);
v___x_471_ = v___x_436_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_450_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_488_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
lean_inc_n(v_u_460_, 2);
v___x_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_472_, 0, v_u_460_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_mkConst(v___x_468_, v___x_472_);
lean_inc_ref(v_target_462_);
lean_inc(v_fst_445_);
lean_inc_ref(v___x_418_);
v___x_474_ = l_Lean_mkApp6(v___x_473_, v___x_418_, v___x_410_, v_fst_445_, v___x_419_, v_target_462_, v_a_456_);
v___x_475_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_460_, v___x_418_, v_fst_445_, v_H_420_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 2, v___x_475_);
v___x_477_ = v___x_464_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_u_460_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_00_u03c3s_461_);
lean_ctor_set(v_reuseFailAlloc_487_, 2, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_487_, 3, v_target_462_);
v___x_477_ = v_reuseFailAlloc_487_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_479_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 1, v___x_474_);
lean_ctor_set(v___x_447_, 0, v___x_477_);
v___x_479_ = v___x_447_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_474_);
v___x_479_ = v_reuseFailAlloc_486_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_481_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_479_);
lean_ctor_set(v___x_441_, 0, v_fst_434_);
v___x_481_ = v___x_441_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_fst_434_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_479_);
v___x_481_ = v_reuseFailAlloc_485_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
lean_object* v___x_483_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_481_);
v___x_483_ = v___x_458_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
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
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_a_450_);
lean_del_object(v___x_447_);
lean_dec(v_fst_445_);
lean_del_object(v___x_441_);
lean_dec(v_fst_438_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_dec_ref(v_H_420_);
lean_dec_ref(v___x_419_);
lean_dec_ref(v___x_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_410_);
v_a_492_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_455_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_455_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
lean_del_object(v___x_447_);
lean_dec(v_fst_445_);
lean_del_object(v___x_441_);
lean_dec(v_snd_439_);
lean_dec(v_fst_438_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_dec_ref(v_x_421_);
lean_dec_ref(v_H_420_);
lean_dec_ref(v___x_419_);
lean_dec_ref(v___x_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_410_);
v_a_500_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_449_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_449_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_del_object(v___x_441_);
lean_dec(v_snd_439_);
lean_dec(v_fst_438_);
lean_del_object(v___x_436_);
lean_dec(v_fst_434_);
lean_dec_ref(v_x_421_);
lean_dec_ref(v_H_420_);
lean_dec_ref(v___x_419_);
lean_dec_ref(v___x_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_410_);
v_a_510_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_443_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_443_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_x_421_);
lean_dec_ref(v_H_420_);
lean_dec_ref(v___x_419_);
lean_dec_ref(v___x_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v___x_410_);
return v___x_431_;
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_x_421_);
lean_dec_ref(v_H_420_);
lean_dec_ref(v___x_419_);
lean_dec_ref(v___x_418_);
lean_dec_ref(v___x_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v___x_415_);
lean_dec_ref(v___x_414_);
lean_dec_ref(v_k_412_);
lean_dec_ref(v___x_410_);
v_a_520_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_430_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_430_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_528_ = _args[0];
lean_object* v_snd_529_ = _args[1];
lean_object* v_k_530_ = _args[2];
lean_object* v___x_531_ = _args[3];
lean_object* v___x_532_ = _args[4];
lean_object* v___x_533_ = _args[5];
lean_object* v___x_534_ = _args[6];
lean_object* v___x_535_ = _args[7];
lean_object* v___x_536_ = _args[8];
lean_object* v___x_537_ = _args[9];
lean_object* v_H_538_ = _args[10];
lean_object* v_x_539_ = _args[11];
lean_object* v___y_540_ = _args[12];
lean_object* v___y_541_ = _args[13];
lean_object* v___y_542_ = _args[14];
lean_object* v___y_543_ = _args[15];
lean_object* v___y_544_ = _args[16];
_start:
{
uint8_t v___x_2258__boxed_545_; lean_object* v_res_546_; 
v___x_2258__boxed_545_ = lean_unbox(v___x_531_);
v_res_546_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(v___x_528_, v_snd_529_, v_k_530_, v___x_2258__boxed_545_, v___x_532_, v___x_533_, v___x_534_, v___x_535_, v___x_536_, v___x_537_, v_H_538_, v_x_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(lean_object* v_k_547_, lean_object* v_b_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
v___x_554_ = lean_apply_6(v_k_547_, v_b_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, lean_box(0));
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0(v_k_555_, v_b_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(lean_object* v_name_563_, uint8_t v_bi_564_, lean_object* v_type_565_, lean_object* v_k_566_, uint8_t v_kind_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v___f_573_; lean_object* v___x_574_; 
v___f_573_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_573_, 0, v_k_566_);
v___x_574_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_563_, v_bi_564_, v_type_565_, v___f_573_, v_kind_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_583_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_574_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_574_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg___boxed(lean_object* v_name_591_, lean_object* v_bi_592_, lean_object* v_type_593_, lean_object* v_k_594_, lean_object* v_kind_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
uint8_t v_bi_boxed_601_; uint8_t v_kind_boxed_602_; lean_object* v_res_603_; 
v_bi_boxed_601_ = lean_unbox(v_bi_592_);
v_kind_boxed_602_ = lean_unbox(v_kind_595_);
v_res_603_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_591_, v_bi_boxed_601_, v_type_593_, v_k_594_, v_kind_boxed_602_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(lean_object* v_name_604_, lean_object* v_type_605_, lean_object* v_k_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v___x_612_; uint8_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = 0;
v___x_613_ = 0;
v___x_614_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_604_, v___x_612_, v_type_605_, v_k_606_, v___x_613_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg___boxed(lean_object* v_name_615_, lean_object* v_type_616_, lean_object* v_k_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_615_, v_type_616_, v_k_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_623_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__2));
v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(lean_object* v_H_633_, lean_object* v_name_634_, lean_object* v_k_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_641_ = l_Lean_Expr_consumeMData(v_H_633_);
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_644_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_645_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__0));
v___x_646_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_647_ = lean_unsigned_to_nat(3u);
v___x_648_ = l_Lean_Expr_isAppOfArity(v___x_641_, v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec_ref(v___x_641_);
lean_dec_ref(v_k_635_);
lean_dec(v_name_634_);
v___x_649_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__3);
v___x_650_ = l_Lean_MessageData_ofExpr(v_H_633_);
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_651_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
return v___x_652_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = l_Lean_Expr_appFn_x21(v___x_641_);
v___x_654_ = l_Lean_Expr_appFn_x21(v___x_653_);
v___x_655_ = l_Lean_Expr_appArg_x21(v___x_654_);
lean_dec_ref(v___x_654_);
v___x_656_ = l_Lean_Expr_appArg_x21(v___x_653_);
lean_dec_ref(v___x_653_);
v___x_657_ = l_Lean_Expr_appArg_x21(v___x_641_);
lean_dec_ref(v___x_641_);
v___x_658_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_634_, v_a_638_, v_a_639_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v_fst_660_; lean_object* v_snd_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___x_664_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v_fst_660_ = lean_ctor_get(v_a_659_, 0);
lean_inc(v_fst_660_);
v_snd_661_ = lean_ctor_get(v_a_659_, 1);
lean_inc(v_snd_661_);
lean_dec(v_a_659_);
v___x_662_ = lean_box(v___x_648_);
lean_inc_ref(v___x_655_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed), 17, 11);
lean_closure_set(v___f_663_, 0, v___x_655_);
lean_closure_set(v___f_663_, 1, v_snd_661_);
lean_closure_set(v___f_663_, 2, v_k_635_);
lean_closure_set(v___f_663_, 3, v___x_662_);
lean_closure_set(v___f_663_, 4, v___x_642_);
lean_closure_set(v___f_663_, 5, v___x_643_);
lean_closure_set(v___f_663_, 6, v___x_644_);
lean_closure_set(v___f_663_, 7, v___x_645_);
lean_closure_set(v___f_663_, 8, v___x_656_);
lean_closure_set(v___f_663_, 9, v___x_657_);
lean_closure_set(v___f_663_, 10, v_H_633_);
v___x_664_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_660_, v___x_655_, v___f_663_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
return v___x_664_;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v___x_657_);
lean_dec_ref(v___x_656_);
lean_dec_ref(v___x_655_);
lean_dec_ref(v_k_635_);
lean_dec_ref(v_H_633_);
v_a_665_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_658_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_658_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___boxed(lean_object* v_H_673_, lean_object* v_name_674_, lean_object* v_k_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_673_, v_name_674_, v_k_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(lean_object* v_00_u03b1_682_, lean_object* v_H_683_, lean_object* v_name_684_, lean_object* v_k_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_683_, v_name_684_, v_k_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___boxed(lean_object* v_00_u03b1_692_, lean_object* v_H_693_, lean_object* v_name_694_, lean_object* v_k_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists(v_00_u03b1_692_, v_H_693_, v_name_694_, v_k_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(lean_object* v_00_u03b1_702_, lean_object* v_name_703_, uint8_t v_bi_704_, lean_object* v_type_705_, lean_object* v_k_706_, uint8_t v_kind_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___redArg(v_name_703_, v_bi_704_, v_type_705_, v_k_706_, v_kind_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0___boxed(lean_object* v_00_u03b1_714_, lean_object* v_name_715_, lean_object* v_bi_716_, lean_object* v_type_717_, lean_object* v_k_718_, lean_object* v_kind_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
uint8_t v_bi_boxed_725_; uint8_t v_kind_boxed_726_; lean_object* v_res_727_; 
v_bi_boxed_725_ = lean_unbox(v_bi_716_);
v_kind_boxed_726_ = lean_unbox(v_kind_719_);
v_res_727_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0_spec__0(v_00_u03b1_714_, v_name_715_, v_bi_boxed_725_, v_type_717_, v_k_718_, v_kind_boxed_726_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(lean_object* v_00_u03b1_728_, lean_object* v_name_729_, lean_object* v_type_730_, lean_object* v_k_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_name_729_, v_type_730_, v_k_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___boxed(lean_object* v_00_u03b1_738_, lean_object* v_name_739_, lean_object* v_type_740_, lean_object* v_k_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0(v_00_u03b1_738_, v_name_739_, v_type_740_, v_k_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
return v_res_747_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg(){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___boxed(lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(lean_object* v_00_u03b1_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___boxed(lean_object* v_00_u03b1_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0(v_00_u03b1_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; lean_object* v_ngen_773_; lean_object* v_namePrefix_774_; lean_object* v_idx_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_805_; 
v___x_772_ = lean_st_ref_get(v___y_770_);
v_ngen_773_ = lean_ctor_get(v___x_772_, 2);
lean_inc_ref(v_ngen_773_);
lean_dec(v___x_772_);
v_namePrefix_774_ = lean_ctor_get(v_ngen_773_, 0);
v_idx_775_ = lean_ctor_get(v_ngen_773_, 1);
v_isSharedCheck_805_ = !lean_is_exclusive(v_ngen_773_);
if (v_isSharedCheck_805_ == 0)
{
v___x_777_ = v_ngen_773_;
v_isShared_778_ = v_isSharedCheck_805_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_idx_775_);
lean_inc(v_namePrefix_774_);
lean_dec(v_ngen_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_805_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_r_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
lean_inc(v_idx_775_);
lean_inc(v_namePrefix_774_);
v_r_779_ = l_Lean_Name_num___override(v_namePrefix_774_, v_idx_775_);
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = lean_nat_add(v_idx_775_, v___x_780_);
lean_dec(v_idx_775_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___x_781_);
v___x_783_ = v___x_777_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_namePrefix_774_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_804_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v_env_785_; lean_object* v_nextMacroScope_786_; lean_object* v_auxDeclNGen_787_; lean_object* v_traceState_788_; lean_object* v_cache_789_; lean_object* v_recordedDeps_790_; lean_object* v_messages_791_; lean_object* v_infoState_792_; lean_object* v_snapshotTasks_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_802_; 
v___x_784_ = lean_st_ref_take(v___y_770_);
v_env_785_ = lean_ctor_get(v___x_784_, 0);
v_nextMacroScope_786_ = lean_ctor_get(v___x_784_, 1);
v_auxDeclNGen_787_ = lean_ctor_get(v___x_784_, 3);
v_traceState_788_ = lean_ctor_get(v___x_784_, 4);
v_cache_789_ = lean_ctor_get(v___x_784_, 5);
v_recordedDeps_790_ = lean_ctor_get(v___x_784_, 6);
v_messages_791_ = lean_ctor_get(v___x_784_, 7);
v_infoState_792_ = lean_ctor_get(v___x_784_, 8);
v_snapshotTasks_793_ = lean_ctor_get(v___x_784_, 9);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_784_, 2);
lean_dec(v_unused_803_);
v___x_795_ = v___x_784_;
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snapshotTasks_793_);
lean_inc(v_infoState_792_);
lean_inc(v_messages_791_);
lean_inc(v_recordedDeps_790_);
lean_inc(v_cache_789_);
lean_inc(v_traceState_788_);
lean_inc(v_auxDeclNGen_787_);
lean_inc(v_nextMacroScope_786_);
lean_inc(v_env_785_);
lean_dec(v___x_784_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_802_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 2, v___x_783_);
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_env_785_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_nextMacroScope_786_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_auxDeclNGen_787_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v_traceState_788_);
lean_ctor_set(v_reuseFailAlloc_801_, 5, v_cache_789_);
lean_ctor_set(v_reuseFailAlloc_801_, 6, v_recordedDeps_790_);
lean_ctor_set(v_reuseFailAlloc_801_, 7, v_messages_791_);
lean_ctor_set(v_reuseFailAlloc_801_, 8, v_infoState_792_);
lean_ctor_set(v_reuseFailAlloc_801_, 9, v_snapshotTasks_793_);
v___x_798_ = v_reuseFailAlloc_801_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_st_ref_put(v___y_770_, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_r_779_);
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_806_);
lean_dec(v___y_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(lean_object* v_u_829_, lean_object* v_00_u03c3s_830_, lean_object* v_H_u2081_x27_831_, lean_object* v_k_832_, lean_object* v_H_u2082_x27_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; lean_object* v_fst_840_; lean_object* v_snd_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_919_; 
lean_inc_ref(v_H_u2082_x27_833_);
lean_inc_ref(v_H_u2081_x27_831_);
lean_inc_ref(v_00_u03c3s_830_);
lean_inc(v_u_829_);
v___x_839_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_829_, v_00_u03c3s_830_, v_H_u2081_x27_831_, v_H_u2082_x27_833_);
v_fst_840_ = lean_ctor_get(v___x_839_, 0);
v_snd_841_ = lean_ctor_get(v___x_839_, 1);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_919_ == 0)
{
v___x_843_ = v___x_839_;
v_isShared_844_ = v_isSharedCheck_919_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_snd_841_);
lean_inc(v_fst_840_);
lean_dec(v___x_839_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_919_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; 
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v_fst_840_);
v___x_845_ = lean_apply_6(v_k_832_, v_fst_840_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, lean_box(0));
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v_snd_847_; lean_object* v_fst_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_910_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v_snd_847_ = lean_ctor_get(v_a_846_, 1);
v_fst_848_ = lean_ctor_get(v_a_846_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v_a_846_);
if (v_isSharedCheck_910_ == 0)
{
v___x_850_ = v_a_846_;
v_isShared_851_ = v_isSharedCheck_910_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_847_);
lean_inc(v_fst_848_);
lean_dec(v_a_846_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_910_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_909_; 
v_fst_852_ = lean_ctor_get(v_snd_847_, 0);
v_snd_853_ = lean_ctor_get(v_snd_847_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_snd_847_);
if (v_isSharedCheck_909_ == 0)
{
v___x_855_ = v_snd_847_;
v_isShared_856_ = v_isSharedCheck_909_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_snd_853_);
lean_inc(v_fst_852_);
lean_dec(v_snd_847_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_909_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; 
lean_inc(v_fst_852_);
v___x_857_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_852_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_900_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_900_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_900_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_900_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_fst_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_898_; 
v_fst_862_ = lean_ctor_get(v_a_858_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_a_858_, 1);
lean_dec(v_unused_899_);
v___x_864_ = v_a_858_;
v_isShared_865_ = v_isSharedCheck_898_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_fst_862_);
lean_dec(v_a_858_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_898_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v_u_866_; lean_object* v_00_u03c3s_867_; lean_object* v_target_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_896_; 
v_u_866_ = lean_ctor_get(v_fst_852_, 0);
v_00_u03c3s_867_ = lean_ctor_get(v_fst_852_, 1);
v_target_868_ = lean_ctor_get(v_fst_852_, 3);
v_isSharedCheck_896_ = !lean_is_exclusive(v_fst_852_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v_fst_852_, 2);
lean_dec(v_unused_897_);
v___x_870_ = v_fst_852_;
v_isShared_871_ = v_isSharedCheck_896_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_target_868_);
lean_inc(v_00_u03c3s_867_);
lean_inc(v_u_866_);
lean_dec(v_fst_852_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_896_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_872_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1));
v___x_873_ = lean_box(0);
lean_inc(v_u_829_);
if (v_isShared_844_ == 0)
{
lean_ctor_set_tag(v___x_843_, 1);
lean_ctor_set(v___x_843_, 1, v___x_873_);
lean_ctor_set(v___x_843_, 0, v_u_829_);
v___x_875_ = v___x_843_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_u_829_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_895_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_876_ = l_Lean_mkConst(v___x_872_, v___x_875_);
lean_inc_ref(v_target_868_);
lean_inc_ref(v_H_u2082_x27_833_);
lean_inc_ref(v_H_u2081_x27_831_);
lean_inc_n(v_fst_862_, 2);
lean_inc_ref_n(v_00_u03c3s_830_, 2);
v___x_877_ = l_Lean_mkApp8(v___x_876_, v_00_u03c3s_830_, v_fst_862_, v_H_u2081_x27_831_, v_H_u2082_x27_833_, v_fst_840_, v_target_868_, v_snd_841_, v_snd_853_);
lean_inc(v_u_829_);
v___x_878_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_829_, v_00_u03c3s_830_, v_fst_862_, v_H_u2081_x27_831_);
v___x_879_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_829_, v_00_u03c3s_830_, v___x_878_, v_H_u2082_x27_833_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 2, v___x_879_);
v___x_881_ = v___x_870_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_u_866_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_00_u03c3s_867_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_target_868_);
v___x_881_ = v_reuseFailAlloc_894_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 1, v_fst_862_);
lean_ctor_set(v___x_864_, 0, v_fst_848_);
v___x_883_ = v___x_864_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_fst_848_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_fst_862_);
v___x_883_ = v_reuseFailAlloc_893_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_885_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_877_);
lean_ctor_set(v___x_855_, 0, v___x_881_);
v___x_885_ = v___x_855_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_877_);
v___x_885_ = v_reuseFailAlloc_892_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_885_);
lean_ctor_set(v___x_850_, 0, v___x_883_);
v___x_887_ = v___x_850_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_885_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_887_);
v___x_889_ = v___x_860_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
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
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_del_object(v___x_855_);
lean_dec(v_snd_853_);
lean_dec(v_fst_852_);
lean_del_object(v___x_850_);
lean_dec(v_fst_848_);
lean_del_object(v___x_843_);
lean_dec(v_snd_841_);
lean_dec(v_fst_840_);
lean_dec_ref(v_H_u2082_x27_833_);
lean_dec_ref(v_H_u2081_x27_831_);
lean_dec_ref(v_00_u03c3s_830_);
lean_dec(v_u_829_);
v_a_901_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_857_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_857_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_del_object(v___x_843_);
lean_dec(v_snd_841_);
lean_dec(v_fst_840_);
lean_dec_ref(v_H_u2082_x27_833_);
lean_dec_ref(v_H_u2081_x27_831_);
lean_dec_ref(v_00_u03c3s_830_);
lean_dec(v_u_829_);
v_a_911_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_845_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_845_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(lean_object* v_u_920_, lean_object* v_00_u03c3s_921_, lean_object* v_H_u2081_x27_922_, lean_object* v_k_923_, lean_object* v_H_u2082_x27_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(v_u_920_, v_00_u03c3s_921_, v_H_u2081_x27_922_, v_k_923_, v_H_u2082_x27_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(lean_object* v_a_933_, lean_object* v_snd_934_, lean_object* v_k_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v_00_u03c3s_941_, lean_object* v_hyp_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_h_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_lctx_951_; lean_object* v___x_952_; uint8_t v___x_953_; lean_object* v___x_954_; 
v_lctx_951_ = lean_ctor_get(v___y_946_, 2);
lean_inc_ref(v_a_933_);
v___x_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_952_, 0, v_a_933_);
v___x_953_ = 0;
lean_inc_ref(v_h_945_);
lean_inc_ref(v_lctx_951_);
v___x_954_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_934_, v_lctx_951_, v_h_945_, v___x_952_, v___x_953_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v___x_955_; 
lean_dec_ref_known(v___x_954_, 1);
lean_inc(v___y_949_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_947_);
lean_inc_ref(v___y_946_);
lean_inc_ref(v_h_945_);
lean_inc_ref(v_a_933_);
v___x_955_ = lean_apply_7(v_k_935_, v_a_933_, v_h_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, lean_box(0));
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v_snd_957_; lean_object* v_fst_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1013_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v_snd_957_ = lean_ctor_get(v_a_956_, 1);
v_fst_958_ = lean_ctor_get(v_a_956_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v_a_956_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_960_ = v_a_956_;
v_isShared_961_ = v_isSharedCheck_1013_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_snd_957_);
lean_inc(v_fst_958_);
lean_dec(v_a_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1013_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_fst_962_; lean_object* v_snd_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1012_; 
v_fst_962_ = lean_ctor_get(v_snd_957_, 0);
v_snd_963_ = lean_ctor_get(v_snd_957_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_snd_957_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_965_ = v_snd_957_;
v_isShared_966_ = v_isSharedCheck_1012_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_snd_963_);
lean_inc(v_fst_962_);
lean_dec(v_snd_957_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1012_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_mk_empty_array_with_capacity(v___x_967_);
v___x_969_ = lean_array_push(v___x_968_, v_h_945_);
v___x_970_ = 1;
v___x_971_ = 1;
v___x_972_ = l_Lean_Meta_mkLambdaFVars(v___x_969_, v_snd_963_, v___x_953_, v___x_970_, v___x_953_, v___x_970_, v___x_971_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec_ref(v___x_969_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1003_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1003_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1003_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_u_977_; lean_object* v_00_u03c3s_978_; lean_object* v_hyps_979_; lean_object* v_target_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1002_; 
v_u_977_ = lean_ctor_get(v_fst_962_, 0);
v_00_u03c3s_978_ = lean_ctor_get(v_fst_962_, 1);
v_hyps_979_ = lean_ctor_get(v_fst_962_, 2);
v_target_980_ = lean_ctor_get(v_fst_962_, 3);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_fst_962_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_982_ = v_fst_962_;
v_isShared_983_ = v_isSharedCheck_1002_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_target_980_);
lean_inc(v_hyps_979_);
lean_inc(v_00_u03c3s_978_);
lean_inc(v_u_977_);
lean_dec(v_fst_962_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1002_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v_prf_988_; lean_object* v___x_989_; lean_object* v_goal_991_; 
v___x_984_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0));
v___x_985_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1));
v___x_986_ = l_Lean_Name_mkStr6(v___x_936_, v___x_937_, v___x_938_, v___x_939_, v___x_984_, v___x_985_);
v___x_987_ = l_Lean_mkConst(v___x_986_, v___x_940_);
lean_inc_ref(v_target_980_);
lean_inc_ref(v_hyp_942_);
lean_inc_ref(v_hyps_979_);
lean_inc_ref(v_00_u03c3s_941_);
v_prf_988_ = l_Lean_mkApp7(v___x_987_, v_00_u03c3s_941_, v_hyps_979_, v_hyp_942_, v_target_980_, v_a_933_, v_a_943_, v_a_973_);
v___x_989_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_a_944_, v_00_u03c3s_941_, v_hyps_979_, v_hyp_942_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 2, v___x_989_);
v_goal_991_ = v___x_982_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_u_977_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_00_u03c3s_978_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_target_980_);
v_goal_991_ = v_reuseFailAlloc_1001_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 1, v_prf_988_);
lean_ctor_set(v___x_965_, 0, v_goal_991_);
v___x_993_ = v___x_965_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_goal_991_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_prf_988_);
v___x_993_ = v_reuseFailAlloc_1000_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_995_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v___x_993_);
v___x_995_ = v___x_960_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_fst_958_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_995_);
v___x_997_ = v___x_975_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_del_object(v___x_965_);
lean_dec(v_fst_962_);
lean_del_object(v___x_960_);
lean_dec(v_fst_958_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_hyp_942_);
lean_dec_ref(v_00_u03c3s_941_);
lean_dec(v___x_940_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v___x_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v_a_933_);
v_a_1004_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_972_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_972_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_hyp_942_);
lean_dec_ref(v_00_u03c3s_941_);
lean_dec(v___x_940_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v___x_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v_a_933_);
return v___x_955_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v_h_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec_ref(v_hyp_942_);
lean_dec_ref(v_00_u03c3s_941_);
lean_dec(v___x_940_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v___x_938_);
lean_dec_ref(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v_k_935_);
lean_dec_ref(v_a_933_);
v_a_1014_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_954_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_954_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_1022_ = _args[0];
lean_object* v_snd_1023_ = _args[1];
lean_object* v_k_1024_ = _args[2];
lean_object* v___x_1025_ = _args[3];
lean_object* v___x_1026_ = _args[4];
lean_object* v___x_1027_ = _args[5];
lean_object* v___x_1028_ = _args[6];
lean_object* v___x_1029_ = _args[7];
lean_object* v_00_u03c3s_1030_ = _args[8];
lean_object* v_hyp_1031_ = _args[9];
lean_object* v_a_1032_ = _args[10];
lean_object* v_a_1033_ = _args[11];
lean_object* v_h_1034_ = _args[12];
lean_object* v___y_1035_ = _args[13];
lean_object* v___y_1036_ = _args[14];
lean_object* v___y_1037_ = _args[15];
lean_object* v___y_1038_ = _args[16];
lean_object* v___y_1039_ = _args[17];
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_1022_, v_snd_1023_, v_k_1024_, v___x_1025_, v___x_1026_, v___x_1027_, v___x_1028_, v___x_1029_, v_00_u03c3s_1030_, v_hyp_1031_, v_a_1032_, v_a_1033_, v_h_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1040_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_box(0);
v___x_1042_ = l_Lean_mkSort(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object* v_00_u03c3s_1052_, lean_object* v_hyp_1053_, lean_object* v_name_1054_, lean_object* v_k_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref_known(v___x_1061_, 1);
v___x_1063_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1064_ = 0;
v___x_1065_ = lean_box(0);
v___x_1066_ = l_Lean_Meta_mkFreshExprMVar(v___x_1063_, v___x_1064_, v___x_1065_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc_n(v_a_1067_, 2);
lean_dec_ref_known(v___x_1066_, 1);
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_1069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_1071_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1072_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1073_ = lean_box(0);
lean_inc(v_a_1062_);
v___x_1074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_a_1062_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
lean_inc_ref(v___x_1074_);
v___x_1075_ = l_Lean_mkConst(v___x_1072_, v___x_1074_);
lean_inc_ref(v_hyp_1053_);
lean_inc_ref(v_00_u03c3s_1052_);
v___x_1076_ = l_Lean_mkApp3(v___x_1075_, v_00_u03c3s_1052_, v_hyp_1053_, v_a_1067_);
v___x_1077_ = lean_box(0);
v___x_1078_ = l_Lean_Meta_synthInstance(v___x_1076_, v___x_1077_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref_known(v___x_1078_, 1);
v___x_1080_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_1054_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_fst_1082_; lean_object* v_snd_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v_fst_1082_ = lean_ctor_get(v_a_1081_, 0);
lean_inc(v_fst_1082_);
v_snd_1083_ = lean_ctor_get(v_a_1081_, 1);
lean_inc(v_snd_1083_);
lean_dec(v_a_1081_);
lean_inc(v_a_1067_);
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1084_, 0, v_a_1067_);
lean_closure_set(v___f_1084_, 1, v_snd_1083_);
lean_closure_set(v___f_1084_, 2, v_k_1055_);
lean_closure_set(v___f_1084_, 3, v___x_1068_);
lean_closure_set(v___f_1084_, 4, v___x_1069_);
lean_closure_set(v___f_1084_, 5, v___x_1070_);
lean_closure_set(v___f_1084_, 6, v___x_1071_);
lean_closure_set(v___f_1084_, 7, v___x_1074_);
lean_closure_set(v___f_1084_, 8, v_00_u03c3s_1052_);
lean_closure_set(v___f_1084_, 9, v_hyp_1053_);
lean_closure_set(v___f_1084_, 10, v_a_1079_);
lean_closure_set(v___f_1084_, 11, v_a_1062_);
v___x_1085_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_1082_, v_a_1067_, v___f_1084_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
return v___x_1085_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec(v_a_1079_);
lean_dec_ref_known(v___x_1074_, 2);
lean_dec(v_a_1067_);
lean_dec(v_a_1062_);
lean_dec_ref(v_k_1055_);
lean_dec_ref(v_hyp_1053_);
lean_dec_ref(v_00_u03c3s_1052_);
v_a_1086_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1080_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1080_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref_known(v___x_1074_, 2);
lean_dec(v_a_1067_);
lean_dec(v_a_1062_);
lean_dec_ref(v_k_1055_);
lean_dec(v_name_1054_);
lean_dec_ref(v_hyp_1053_);
lean_dec_ref(v_00_u03c3s_1052_);
v_a_1094_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1078_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1078_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_a_1062_);
lean_dec_ref(v_k_1055_);
lean_dec(v_name_1054_);
lean_dec_ref(v_hyp_1053_);
lean_dec_ref(v_00_u03c3s_1052_);
v_a_1102_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1066_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1066_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_k_1055_);
lean_dec(v_name_1054_);
lean_dec_ref(v_hyp_1053_);
lean_dec_ref(v_00_u03c3s_1052_);
v_a_1110_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1061_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1061_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object* v_00_u03c3s_1118_, lean_object* v_hyp_1119_, lean_object* v_name_1120_, lean_object* v_k_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1118_, v_hyp_1119_, v_name_1120_, v_k_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object* v_u_1136_, lean_object* v_00_u03c3s_1137_, lean_object* v_k_1138_, lean_object* v_x_1139_, lean_object* v___h_u03c6_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v_H_x27_1146_; lean_object* v___x_1147_; 
lean_inc_ref(v_00_u03c3s_1137_);
lean_inc(v_u_1136_);
v_H_x27_1146_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1136_, v_00_u03c3s_1137_);
lean_inc(v___y_1144_);
lean_inc_ref(v___y_1143_);
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
v___x_1147_ = lean_apply_6(v_k_1138_, v_H_x27_1146_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, lean_box(0));
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v_snd_1149_; lean_object* v_fst_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1207_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v_snd_1149_ = lean_ctor_get(v_a_1148_, 1);
v_fst_1150_ = lean_ctor_get(v_a_1148_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1148_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1152_ = v_a_1148_;
v_isShared_1153_ = v_isSharedCheck_1207_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1149_);
lean_inc(v_fst_1150_);
lean_dec(v_a_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1207_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_fst_1154_; lean_object* v_snd_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1206_; 
v_fst_1154_ = lean_ctor_get(v_snd_1149_, 0);
v_snd_1155_ = lean_ctor_get(v_snd_1149_, 1);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_snd_1149_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1157_ = v_snd_1149_;
v_isShared_1158_ = v_isSharedCheck_1206_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_snd_1155_);
lean_inc(v_fst_1154_);
lean_dec(v_snd_1149_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1206_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; 
lean_inc(v_fst_1154_);
v___x_1159_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1154_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1197_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1197_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1197_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_fst_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1195_; 
v_fst_1164_ = lean_ctor_get(v_a_1160_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_a_1160_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_a_1160_, 1);
lean_dec(v_unused_1196_);
v___x_1166_ = v_a_1160_;
v_isShared_1167_ = v_isSharedCheck_1195_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_fst_1164_);
lean_dec(v_a_1160_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1195_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v_u_1168_; lean_object* v_00_u03c3s_1169_; lean_object* v_target_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1193_; 
v_u_1168_ = lean_ctor_get(v_fst_1154_, 0);
v_00_u03c3s_1169_ = lean_ctor_get(v_fst_1154_, 1);
v_target_1170_ = lean_ctor_get(v_fst_1154_, 3);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_fst_1154_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v_fst_1154_, 2);
lean_dec(v_unused_1194_);
v___x_1172_ = v_fst_1154_;
v_isShared_1173_ = v_isSharedCheck_1193_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_target_1170_);
lean_inc(v_00_u03c3s_1169_);
lean_inc(v_u_1168_);
lean_dec(v_fst_1154_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1193_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1));
v___x_1175_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 1);
lean_ctor_set(v___x_1152_, 1, v___x_1175_);
lean_ctor_set(v___x_1152_, 0, v_u_1136_);
v___x_1177_ = v___x_1152_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_u_1136_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1178_ = l_Lean_mkConst(v___x_1174_, v___x_1177_);
lean_inc_ref(v_target_1170_);
lean_inc(v_fst_1164_);
v___x_1179_ = l_Lean_mkApp4(v___x_1178_, v_00_u03c3s_1137_, v_fst_1164_, v_target_1170_, v_snd_1155_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 2, v_fst_1164_);
v___x_1181_ = v___x_1172_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_u_1168_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_00_u03c3s_1169_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_fst_1164_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_target_1170_);
v___x_1181_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1179_);
lean_ctor_set(v___x_1166_, 0, v___x_1181_);
v___x_1183_ = v___x_1166_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v___x_1179_);
v___x_1183_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1185_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v___x_1183_);
lean_ctor_set(v___x_1157_, 0, v_fst_1150_);
v___x_1185_ = v___x_1157_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_fst_1150_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1185_);
v___x_1187_ = v___x_1162_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
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
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
lean_del_object(v___x_1157_);
lean_dec(v_snd_1155_);
lean_dec(v_fst_1154_);
lean_del_object(v___x_1152_);
lean_dec(v_fst_1150_);
lean_dec_ref(v_00_u03c3s_1137_);
lean_dec(v_u_1136_);
v_a_1198_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1159_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1159_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_00_u03c3s_1137_);
lean_dec(v_u_1136_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object* v_u_1208_, lean_object* v_00_u03c3s_1209_, lean_object* v_k_1210_, lean_object* v_x_1211_, lean_object* v___h_u03c6_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(v_u_1208_, v_00_u03c3s_1209_, v_k_1210_, v_x_1211_, v___h_u03c6_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec_ref(v___h_u03c6_1212_);
lean_dec_ref(v_x_1211_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object* v_u_1235_, lean_object* v_00_u03c3s_1236_, lean_object* v_k_1237_, lean_object* v_tail_1238_, lean_object* v_fst_1239_, lean_object* v_H_u2081_x27_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___f_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_inc_ref(v_H_u2081_x27_1240_);
lean_inc_ref_n(v_00_u03c3s_1236_, 2);
lean_inc_n(v_u_1235_, 2);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1246_, 0, v_u_1235_);
lean_closure_set(v___f_1246_, 1, v_00_u03c3s_1236_);
lean_closure_set(v___f_1246_, 2, v_H_u2081_x27_1240_);
lean_closure_set(v___f_1246_, 3, v_k_1237_);
v___x_1247_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1247_, 0, v_tail_1238_);
lean_inc_ref(v_fst_1239_);
v___x_1248_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1235_, v_00_u03c3s_1236_, v_fst_1239_, v___x_1247_, v___f_1246_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1294_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1294_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1294_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_fst_1253_; lean_object* v_snd_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1293_; 
v_fst_1253_ = lean_ctor_get(v_a_1249_, 0);
v_snd_1254_ = lean_ctor_get(v_a_1249_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_a_1249_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1256_ = v_a_1249_;
v_isShared_1257_ = v_isSharedCheck_1293_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1254_);
lean_inc(v_fst_1253_);
lean_dec(v_a_1249_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1293_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v_snd_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1291_; 
v_fst_1258_ = lean_ctor_get(v_snd_1254_, 0);
lean_inc(v_fst_1258_);
v_snd_1259_ = lean_ctor_get(v_fst_1253_, 1);
v_snd_1260_ = lean_ctor_get(v_snd_1254_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_snd_1254_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v_snd_1254_, 0);
lean_dec(v_unused_1292_);
v___x_1262_ = v_snd_1254_;
v_isShared_1263_ = v_isSharedCheck_1291_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_snd_1260_);
lean_dec(v_snd_1254_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1291_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_u_1264_; lean_object* v_00_u03c3s_1265_; lean_object* v_target_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1289_; 
v_u_1264_ = lean_ctor_get(v_fst_1258_, 0);
v_00_u03c3s_1265_ = lean_ctor_get(v_fst_1258_, 1);
v_target_1266_ = lean_ctor_get(v_fst_1258_, 3);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_fst_1258_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_fst_1258_, 2);
lean_dec(v_unused_1290_);
v___x_1268_ = v_fst_1258_;
v_isShared_1269_ = v_isSharedCheck_1289_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_target_1266_);
lean_inc(v_00_u03c3s_1265_);
lean_inc(v_u_1264_);
lean_dec(v_fst_1258_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1289_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1270_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1));
v___x_1271_ = lean_box(0);
lean_inc_n(v_u_1235_, 2);
v___x_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_u_1235_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = l_Lean_mkConst(v___x_1270_, v___x_1272_);
lean_inc_ref(v_target_1266_);
lean_inc_ref(v_fst_1239_);
lean_inc_ref(v_H_u2081_x27_1240_);
lean_inc_n(v_snd_1259_, 2);
lean_inc_ref_n(v_00_u03c3s_1236_, 2);
v___x_1274_ = l_Lean_mkApp6(v___x_1273_, v_00_u03c3s_1236_, v_snd_1259_, v_H_u2081_x27_1240_, v_fst_1239_, v_target_1266_, v_snd_1260_);
v___x_1275_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1235_, v_00_u03c3s_1236_, v_snd_1259_, v_fst_1239_);
v___x_1276_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1235_, v_00_u03c3s_1236_, v___x_1275_, v_H_u2081_x27_1240_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 2, v___x_1276_);
v___x_1278_ = v___x_1268_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_u_1264_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_00_u03c3s_1265_);
lean_ctor_set(v_reuseFailAlloc_1288_, 2, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1288_, 3, v_target_1266_);
v___x_1278_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 1, v___x_1274_);
lean_ctor_set(v___x_1262_, 0, v___x_1278_);
v___x_1280_ = v___x_1262_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v___x_1274_);
v___x_1280_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1282_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1280_);
v___x_1282_ = v___x_1256_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_fst_1253_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
lean_object* v___x_1284_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v___x_1282_);
v___x_1284_ = v___x_1251_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
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
lean_dec_ref(v_H_u2081_x27_1240_);
lean_dec_ref(v_fst_1239_);
lean_dec_ref(v_00_u03c3s_1236_);
lean_dec(v_u_1235_);
return v___x_1248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object* v_u_1295_, lean_object* v_00_u03c3s_1296_, lean_object* v_k_1297_, lean_object* v_tail_1298_, lean_object* v_fst_1299_, lean_object* v_H_u2081_x27_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(v_u_1295_, v_00_u03c3s_1296_, v_k_1297_, v_tail_1298_, v_fst_1299_, v_H_u2081_x27_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1306_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4));
v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(lean_object* v___x_1318_, lean_object* v_tail_1319_, lean_object* v_u_1320_, lean_object* v___x_1321_, lean_object* v_k_1322_, lean_object* v_x_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(v___x_1318_, v_tail_1319_, v_u_1320_, v___x_1321_, v_k_1322_, v_x_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1329_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11(void){
_start:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10));
v___x_1341_ = l_Lean_stringToMessageData(v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(lean_object* v_u_1348_, lean_object* v_00_u03c3s_1349_, lean_object* v_H_1350_, lean_object* v_pat_1351_, lean_object* v_k_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
switch(lean_obj_tag(v_pat_1351_))
{
case 0:
{
lean_object* v_name_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1405_; 
v_name_1358_ = lean_ctor_get(v_pat_1351_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_pat_1351_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1360_ = v_pat_1351_;
v_isShared_1361_ = v_isSharedCheck_1405_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_name_1358_);
lean_dec(v_pat_1351_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1405_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1370_; lean_object* v_a_1371_; lean_object* v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1374_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1375_ = 0;
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Lean_Meta_mkFreshExprMVar(v___x_1374_, v___x_1375_, v___x_1376_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1380_ = lean_box(0);
lean_inc(v_u_1348_);
v___x_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_u_1348_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = l_Lean_mkConst(v___x_1379_, v___x_1381_);
lean_inc_ref(v_H_1350_);
lean_inc_ref(v_00_u03c3s_1349_);
v___x_1383_ = l_Lean_mkApp3(v___x_1382_, v_00_u03c3s_1349_, v_H_1350_, v_a_1378_);
v___x_1384_ = lean_box(0);
v___x_1385_ = l_Lean_Meta_synthInstance(v___x_1383_, v___x_1384_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec_ref_known(v___x_1385_, 1);
lean_inc(v_name_1358_);
v___x_1386_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_name_1358_);
lean_inc_ref(v_k_1352_);
lean_inc_ref(v_H_1350_);
lean_inc_ref(v_00_u03c3s_1349_);
lean_inc(v_u_1348_);
v___x_1387_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1348_, v_00_u03c3s_1349_, v_H_1350_, v___x_1386_, v_k_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_del_object(v___x_1360_);
lean_dec(v_name_1358_);
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
lean_dec(v_u_1348_);
return v___x_1387_;
}
else
{
lean_object* v_a_1388_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
v___y_1370_ = v___x_1387_;
v_a_1371_ = v_a_1388_;
goto v___jp_1369_;
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1385_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1385_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
lean_inc(v_a_1389_);
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v___y_1370_ = v___x_1394_;
v_a_1371_ = v_a_1389_;
goto v___jp_1369_;
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1377_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1377_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
lean_inc(v_a_1397_);
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
v___y_1370_ = v___x_1402_;
v_a_1371_ = v_a_1397_;
goto v___jp_1369_;
}
}
}
v___jp_1362_:
{
if (v___y_1364_ == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref(v___y_1363_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set_tag(v___x_1360_, 5);
v___x_1366_ = v___x_1360_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_name_1358_);
v___x_1366_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
v_pat_1351_ = v___x_1366_;
goto _start;
}
}
else
{
lean_del_object(v___x_1360_);
lean_dec(v_name_1358_);
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
lean_dec(v_u_1348_);
return v___y_1363_;
}
}
v___jp_1369_:
{
uint8_t v___x_1372_; 
v___x_1372_ = l_Lean_Exception_isInterrupt(v_a_1371_);
if (v___x_1372_ == 0)
{
uint8_t v___x_1373_; 
v___x_1373_ = l_Lean_Exception_isRuntime(v_a_1371_);
v___y_1363_ = v___y_1370_;
v___y_1364_ = v___x_1373_;
goto v___jp_1362_;
}
else
{
lean_dec_ref(v_a_1371_);
v___y_1363_ = v___y_1370_;
v___y_1364_ = v___x_1372_;
goto v___jp_1362_;
}
}
}
}
case 1:
{
lean_object* v_H_x27_1406_; lean_object* v___x_1407_; 
lean_inc_ref(v_00_u03c3s_1349_);
lean_inc(v_u_1348_);
v_H_x27_1406_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1348_, v_00_u03c3s_1349_);
lean_inc(v_a_1356_);
lean_inc_ref(v_a_1355_);
lean_inc(v_a_1354_);
lean_inc_ref(v_a_1353_);
v___x_1407_ = lean_apply_6(v_k_1352_, v_H_x27_1406_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, lean_box(0));
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v_snd_1409_; lean_object* v_fst_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1468_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
v_snd_1409_ = lean_ctor_get(v_a_1408_, 1);
v_fst_1410_ = lean_ctor_get(v_a_1408_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_a_1408_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1412_ = v_a_1408_;
v_isShared_1413_ = v_isSharedCheck_1468_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_snd_1409_);
lean_inc(v_fst_1410_);
lean_dec(v_a_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1468_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v_fst_1414_; lean_object* v_snd_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1467_; 
v_fst_1414_ = lean_ctor_get(v_snd_1409_, 0);
v_snd_1415_ = lean_ctor_get(v_snd_1409_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_snd_1409_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1417_ = v_snd_1409_;
v_isShared_1418_ = v_isSharedCheck_1467_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_snd_1415_);
lean_inc(v_fst_1414_);
lean_dec(v_snd_1409_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1467_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; 
lean_inc(v_fst_1414_);
v___x_1419_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1414_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1458_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1458_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1458_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_fst_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1456_; 
v_fst_1424_ = lean_ctor_get(v_a_1420_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_a_1420_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_a_1420_, 1);
lean_dec(v_unused_1457_);
v___x_1426_ = v_a_1420_;
v_isShared_1427_ = v_isSharedCheck_1456_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_fst_1424_);
lean_dec(v_a_1420_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1456_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_u_1428_; lean_object* v_00_u03c3s_1429_; lean_object* v_target_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1454_; 
v_u_1428_ = lean_ctor_get(v_fst_1414_, 0);
v_00_u03c3s_1429_ = lean_ctor_get(v_fst_1414_, 1);
v_target_1430_ = lean_ctor_get(v_fst_1414_, 3);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_fst_1414_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v_fst_1414_, 2);
lean_dec(v_unused_1455_);
v___x_1432_ = v_fst_1414_;
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_target_1430_);
lean_inc(v_00_u03c3s_1429_);
lean_inc(v_u_1428_);
lean_dec(v_fst_1414_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1));
v___x_1435_ = lean_box(0);
lean_inc(v_u_1348_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 1);
lean_ctor_set(v___x_1412_, 1, v___x_1435_);
lean_ctor_set(v___x_1412_, 0, v_u_1348_);
v___x_1437_ = v___x_1412_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_u_1348_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1438_ = l_Lean_mkConst(v___x_1434_, v___x_1437_);
lean_inc_ref(v_target_1430_);
lean_inc_ref(v_H_1350_);
lean_inc(v_fst_1424_);
lean_inc_ref(v_00_u03c3s_1349_);
v___x_1439_ = l_Lean_mkApp5(v___x_1438_, v_00_u03c3s_1349_, v_fst_1424_, v_H_1350_, v_target_1430_, v_snd_1415_);
v___x_1440_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1348_, v_00_u03c3s_1349_, v_fst_1424_, v_H_1350_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 2, v___x_1440_);
v___x_1442_ = v___x_1432_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_u_1428_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_00_u03c3s_1429_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_target_1430_);
v___x_1442_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v___x_1439_);
lean_ctor_set(v___x_1426_, 0, v___x_1442_);
v___x_1444_ = v___x_1426_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1439_);
v___x_1444_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1444_);
lean_ctor_set(v___x_1417_, 0, v_fst_1410_);
v___x_1446_ = v___x_1417_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_fst_1410_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1448_; 
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v___x_1446_);
v___x_1448_ = v___x_1422_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1446_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
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
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
lean_dec(v_fst_1414_);
lean_del_object(v___x_1412_);
lean_dec(v_fst_1410_);
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
lean_dec(v_u_1348_);
v_a_1459_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1419_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1419_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
lean_dec(v_u_1348_);
return v___x_1407_;
}
}
case 2:
{
lean_object* v_args_1469_; 
v_args_1469_ = lean_ctor_get(v_pat_1351_, 0);
lean_inc(v_args_1469_);
lean_dec_ref_known(v_pat_1351_, 1);
if (lean_obj_tag(v_args_1469_) == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_box(1);
v_pat_1351_ = v___x_1470_;
goto _start;
}
else
{
lean_object* v_tail_1472_; 
v_tail_1472_ = lean_ctor_get(v_args_1469_, 1);
if (lean_obj_tag(v_tail_1472_) == 0)
{
lean_object* v_head_1473_; 
v_head_1473_ = lean_ctor_get(v_args_1469_, 0);
lean_inc(v_head_1473_);
lean_dec_ref_known(v_args_1469_, 2);
v_pat_1351_ = v_head_1473_;
goto _start;
}
else
{
lean_object* v_head_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1568_; 
lean_inc(v_tail_1472_);
v_head_1475_ = lean_ctor_get(v_args_1469_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_args_1469_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_args_1469_, 1);
lean_dec(v_unused_1569_);
v___x_1477_ = v_args_1469_;
v_isShared_1478_ = v_isSharedCheck_1568_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_head_1475_);
lean_dec(v_args_1469_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1568_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; 
lean_inc_ref(v_H_1350_);
lean_inc_ref(v_00_u03c3s_1349_);
lean_inc(v_u_1348_);
v___x_1479_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_1348_, v_00_u03c3s_1349_, v_H_1350_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
if (lean_obj_tag(v_a_1480_) == 1)
{
lean_object* v_val_1481_; lean_object* v_snd_1482_; lean_object* v_fst_1483_; lean_object* v_fst_1484_; lean_object* v_snd_1485_; lean_object* v___f_1486_; lean_object* v___x_1487_; 
v_val_1481_ = lean_ctor_get(v_a_1480_, 0);
lean_inc(v_val_1481_);
lean_dec_ref_known(v_a_1480_, 1);
v_snd_1482_ = lean_ctor_get(v_val_1481_, 1);
lean_inc(v_snd_1482_);
v_fst_1483_ = lean_ctor_get(v_val_1481_, 0);
lean_inc_n(v_fst_1483_, 2);
lean_dec(v_val_1481_);
v_fst_1484_ = lean_ctor_get(v_snd_1482_, 0);
lean_inc_n(v_fst_1484_, 2);
v_snd_1485_ = lean_ctor_get(v_snd_1482_, 1);
lean_inc(v_snd_1485_);
lean_dec(v_snd_1482_);
lean_inc_ref_n(v_00_u03c3s_1349_, 2);
lean_inc_n(v_u_1348_, 2);
v___f_1486_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed), 11, 5);
lean_closure_set(v___f_1486_, 0, v_u_1348_);
lean_closure_set(v___f_1486_, 1, v_00_u03c3s_1349_);
lean_closure_set(v___f_1486_, 2, v_k_1352_);
lean_closure_set(v___f_1486_, 3, v_tail_1472_);
lean_closure_set(v___f_1486_, 4, v_fst_1484_);
v___x_1487_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1348_, v_00_u03c3s_1349_, v_fst_1483_, v_head_1475_, v___f_1486_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1535_; 
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1490_ = v___x_1487_;
v_isShared_1491_ = v_isSharedCheck_1535_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1535_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v_fst_1494_; lean_object* v_fst_1495_; lean_object* v_snd_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1534_; 
v_fst_1492_ = lean_ctor_get(v_a_1488_, 0);
lean_inc(v_fst_1492_);
v_snd_1493_ = lean_ctor_get(v_a_1488_, 1);
lean_inc(v_snd_1493_);
lean_dec(v_a_1488_);
v_fst_1494_ = lean_ctor_get(v_snd_1493_, 0);
lean_inc(v_fst_1494_);
v_fst_1495_ = lean_ctor_get(v_fst_1492_, 0);
v_snd_1496_ = lean_ctor_get(v_fst_1492_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_fst_1492_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1498_ = v_fst_1492_;
v_isShared_1499_ = v_isSharedCheck_1534_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snd_1496_);
lean_inc(v_fst_1495_);
lean_dec(v_fst_1492_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1534_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_snd_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1532_; 
v_snd_1500_ = lean_ctor_get(v_snd_1493_, 1);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_snd_1493_);
if (v_isSharedCheck_1532_ == 0)
{
lean_object* v_unused_1533_; 
v_unused_1533_ = lean_ctor_get(v_snd_1493_, 0);
lean_dec(v_unused_1533_);
v___x_1502_ = v_snd_1493_;
v_isShared_1503_ = v_isSharedCheck_1532_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_snd_1500_);
lean_dec(v_snd_1493_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1532_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v_u_1504_; lean_object* v_00_u03c3s_1505_; lean_object* v_target_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1530_; 
v_u_1504_ = lean_ctor_get(v_fst_1494_, 0);
v_00_u03c3s_1505_ = lean_ctor_get(v_fst_1494_, 1);
v_target_1506_ = lean_ctor_get(v_fst_1494_, 3);
v_isSharedCheck_1530_ = !lean_is_exclusive(v_fst_1494_);
if (v_isSharedCheck_1530_ == 0)
{
lean_object* v_unused_1531_; 
v_unused_1531_ = lean_ctor_get(v_fst_1494_, 2);
lean_dec(v_unused_1531_);
v___x_1508_ = v_fst_1494_;
v_isShared_1509_ = v_isSharedCheck_1530_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_target_1506_);
lean_inc(v_00_u03c3s_1505_);
lean_inc(v_u_1504_);
lean_dec(v_fst_1494_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1530_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1510_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3));
v___x_1511_ = lean_box(0);
lean_inc(v_u_1348_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1511_);
lean_ctor_set(v___x_1477_, 0, v_u_1348_);
v___x_1513_ = v___x_1477_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_u_1348_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1514_ = l_Lean_mkConst(v___x_1510_, v___x_1513_);
lean_inc_ref(v_target_1506_);
lean_inc_ref(v_H_1350_);
lean_inc(v_snd_1496_);
lean_inc_ref(v_00_u03c3s_1349_);
v___x_1515_ = l_Lean_mkApp8(v___x_1514_, v_00_u03c3s_1349_, v_snd_1496_, v_fst_1483_, v_fst_1484_, v_H_1350_, v_target_1506_, v_snd_1485_, v_snd_1500_);
v___x_1516_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1348_, v_00_u03c3s_1349_, v_snd_1496_, v_H_1350_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 2, v___x_1516_);
v___x_1518_ = v___x_1508_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_u_1504_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_00_u03c3s_1505_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_target_1506_);
v___x_1518_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1520_; 
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 1, v___x_1515_);
lean_ctor_set(v___x_1502_, 0, v___x_1518_);
v___x_1520_ = v___x_1502_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1527_, 1, v___x_1515_);
v___x_1520_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v___x_1520_);
v___x_1522_ = v___x_1498_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_fst_1495_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1522_);
v___x_1524_ = v___x_1490_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
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
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1543_; 
lean_dec(v_snd_1485_);
lean_dec(v_fst_1484_);
lean_dec(v_fst_1483_);
lean_del_object(v___x_1477_);
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
lean_dec(v_u_1348_);
v_a_1536_ = lean_ctor_get(v___x_1487_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1538_ = v___x_1487_;
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1487_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1543_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_a_1536_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
lean_dec(v_a_1480_);
lean_del_object(v___x_1477_);
lean_dec_ref(v_00_u03c3s_1349_);
v___x_1544_ = l_Lean_Expr_consumeMData(v_H_1350_);
v___x_1545_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_1546_ = lean_unsigned_to_nat(3u);
v___x_1547_ = l_Lean_Expr_isAppOfArity(v___x_1544_, v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v___x_1544_);
lean_dec(v_head_1475_);
lean_dec(v_tail_1472_);
lean_dec_ref(v_k_1352_);
lean_dec(v_u_1348_);
v___x_1548_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5);
v___x_1549_ = l_Lean_MessageData_ofExpr(v_H_1350_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1550_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
return v___x_1551_;
}
else
{
if (lean_obj_tag(v_head_1475_) == 0)
{
lean_object* v_name_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; 
v_name_1552_ = lean_ctor_get(v_head_1475_, 0);
lean_inc(v_name_1552_);
lean_dec_ref_known(v_head_1475_, 1);
v___x_1553_ = l_Lean_Expr_appFn_x21(v___x_1544_);
v___x_1554_ = l_Lean_Expr_appArg_x21(v___x_1553_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = l_Lean_Expr_appArg_x21(v___x_1544_);
lean_dec_ref(v___x_1544_);
v___f_1556_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1556_, 0, v___x_1555_);
lean_closure_set(v___f_1556_, 1, v_tail_1472_);
lean_closure_set(v___f_1556_, 2, v_u_1348_);
lean_closure_set(v___f_1556_, 3, v___x_1554_);
lean_closure_set(v___f_1556_, 4, v_k_1352_);
v___x_1557_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_1350_, v_name_1552_, v___f_1556_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec_ref(v___x_1544_);
lean_dec(v_head_1475_);
lean_dec(v_tail_1472_);
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_H_1350_);
lean_dec(v_u_1348_);
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7);
v___x_1559_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1558_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1477_);
lean_dec(v_head_1475_);
lean_dec(v_tail_1472_);
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
lean_dec(v_u_1348_);
v_a_1560_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1479_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1479_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_args_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1665_; 
v_args_1570_ = lean_ctor_get(v_pat_1351_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_pat_1351_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1572_ = v_pat_1351_;
v_isShared_1573_ = v_isSharedCheck_1665_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_args_1570_);
lean_dec(v_pat_1351_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1665_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
if (lean_obj_tag(v_args_1570_) == 0)
{
lean_object* v___x_1574_; 
lean_del_object(v___x_1572_);
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
lean_dec(v_u_1348_);
v___x_1574_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_1574_;
}
else
{
lean_object* v_tail_1575_; 
v_tail_1575_ = lean_ctor_get(v_args_1570_, 1);
if (lean_obj_tag(v_tail_1575_) == 0)
{
lean_object* v_head_1576_; 
lean_del_object(v___x_1572_);
v_head_1576_ = lean_ctor_get(v_args_1570_, 0);
lean_inc(v_head_1576_);
lean_dec_ref_known(v_args_1570_, 2);
v_pat_1351_ = v_head_1576_;
goto _start;
}
else
{
lean_object* v_head_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1663_; 
lean_inc(v_tail_1575_);
lean_dec_ref(v_00_u03c3s_1349_);
v_head_1578_ = lean_ctor_get(v_args_1570_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_args_1570_);
if (v_isSharedCheck_1663_ == 0)
{
lean_object* v_unused_1664_; 
v_unused_1664_ = lean_ctor_get(v_args_1570_, 1);
lean_dec(v_unused_1664_);
v___x_1580_ = v_args_1570_;
v_isShared_1581_ = v_isSharedCheck_1663_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_head_1578_);
lean_dec(v_args_1570_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1663_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1582_ = l_Lean_Expr_consumeMData(v_H_1350_);
v___x_1583_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9));
v___x_1584_ = lean_unsigned_to_nat(3u);
v___x_1585_ = l_Lean_Expr_isAppOfArity(v___x_1582_, v___x_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v___x_1582_);
lean_del_object(v___x_1580_);
lean_dec(v_head_1578_);
lean_dec(v_tail_1575_);
lean_del_object(v___x_1572_);
lean_dec_ref(v_k_1352_);
lean_dec(v_u_1348_);
v___x_1586_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11);
v___x_1587_ = l_Lean_MessageData_ofExpr(v_H_1350_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1588_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
return v___x_1589_;
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v_H_1350_);
v___x_1590_ = l_Lean_Expr_appFn_x21(v___x_1582_);
v___x_1591_ = l_Lean_Expr_appFn_x21(v___x_1590_);
v___x_1592_ = l_Lean_Expr_appArg_x21(v___x_1591_);
lean_dec_ref(v___x_1591_);
v___x_1593_ = l_Lean_Expr_appArg_x21(v___x_1590_);
lean_dec_ref(v___x_1590_);
v___x_1594_ = l_Lean_Expr_appArg_x21(v___x_1582_);
lean_dec_ref(v___x_1582_);
lean_inc_ref(v_k_1352_);
lean_inc_ref(v___x_1593_);
lean_inc_ref(v___x_1592_);
lean_inc(v_u_1348_);
v___x_1595_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1348_, v___x_1592_, v___x_1593_, v_head_1578_, v_k_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v_snd_1597_; lean_object* v_fst_1598_; lean_object* v_snd_1599_; lean_object* v___x_1601_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v_snd_1597_ = lean_ctor_get(v_a_1596_, 1);
lean_inc(v_snd_1597_);
lean_dec(v_a_1596_);
v_fst_1598_ = lean_ctor_get(v_snd_1597_, 0);
lean_inc(v_fst_1598_);
v_snd_1599_ = lean_ctor_get(v_snd_1597_, 1);
lean_inc(v_snd_1599_);
lean_dec(v_snd_1597_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v_tail_1575_);
v___x_1601_ = v___x_1572_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_tail_1575_);
v___x_1601_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; 
lean_inc_ref(v___x_1594_);
lean_inc_ref(v___x_1592_);
lean_inc(v_u_1348_);
v___x_1602_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1348_, v___x_1592_, v___x_1594_, v___x_1601_, v_k_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; lean_object* v_snd_1604_; lean_object* v_fst_1605_; lean_object* v_snd_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1660_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1602_, 1);
v_snd_1604_ = lean_ctor_get(v_a_1603_, 1);
lean_inc(v_snd_1604_);
v_fst_1605_ = lean_ctor_get(v_a_1603_, 0);
lean_inc(v_fst_1605_);
lean_dec(v_a_1603_);
v_snd_1606_ = lean_ctor_get(v_snd_1604_, 1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_snd_1604_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_snd_1604_, 0);
lean_dec(v_unused_1661_);
v___x_1608_ = v_snd_1604_;
v_isShared_1609_ = v_isSharedCheck_1660_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_snd_1606_);
lean_dec(v_snd_1604_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1660_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; 
lean_inc(v_fst_1598_);
v___x_1610_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1598_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1651_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1651_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1651_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_fst_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1649_; 
v_fst_1615_ = lean_ctor_get(v_a_1611_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_a_1611_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; 
v_unused_1650_ = lean_ctor_get(v_a_1611_, 1);
lean_dec(v_unused_1650_);
v___x_1617_ = v_a_1611_;
v_isShared_1618_ = v_isSharedCheck_1649_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_fst_1615_);
lean_dec(v_a_1611_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1649_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v_u_1619_; lean_object* v_00_u03c3s_1620_; lean_object* v_target_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1647_; 
v_u_1619_ = lean_ctor_get(v_fst_1598_, 0);
v_00_u03c3s_1620_ = lean_ctor_get(v_fst_1598_, 1);
v_target_1621_ = lean_ctor_get(v_fst_1598_, 3);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_fst_1598_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_fst_1598_, 2);
lean_dec(v_unused_1648_);
v___x_1623_ = v_fst_1598_;
v_isShared_1624_ = v_isSharedCheck_1647_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_target_1621_);
lean_inc(v_00_u03c3s_1620_);
lean_inc(v_u_1619_);
lean_dec(v_fst_1598_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1647_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = lean_box(0);
lean_inc(v_u_1348_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v___x_1625_);
lean_ctor_set(v___x_1580_, 0, v_u_1348_);
v___x_1627_ = v___x_1580_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_u_1348_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1632_; 
lean_inc_ref(v___x_1627_);
v___x_1628_ = l_Lean_mkConst(v___x_1583_, v___x_1627_);
lean_inc_ref(v___x_1594_);
lean_inc_ref(v___x_1593_);
lean_inc_ref_n(v___x_1592_, 2);
v___x_1629_ = l_Lean_mkApp3(v___x_1628_, v___x_1592_, v___x_1593_, v___x_1594_);
lean_inc(v_fst_1615_);
v___x_1630_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1348_, v___x_1592_, v_fst_1615_, v___x_1629_);
lean_inc_ref(v_target_1621_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 2, v___x_1630_);
v___x_1632_ = v___x_1623_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_u_1619_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_00_u03c3s_1620_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v___x_1630_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_target_1621_);
v___x_1632_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1633_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13));
v___x_1634_ = l_Lean_mkConst(v___x_1633_, v___x_1627_);
v___x_1635_ = l_Lean_mkApp7(v___x_1634_, v___x_1592_, v_fst_1615_, v___x_1593_, v___x_1594_, v_target_1621_, v_snd_1599_, v_snd_1606_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 1, v___x_1635_);
lean_ctor_set(v___x_1617_, 0, v___x_1632_);
v___x_1637_ = v___x_1617_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 1, v___x_1637_);
lean_ctor_set(v___x_1608_, 0, v_fst_1605_);
v___x_1639_ = v___x_1608_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_fst_1605_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1639_);
v___x_1641_ = v___x_1613_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
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
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_del_object(v___x_1608_);
lean_dec(v_snd_1606_);
lean_dec(v_fst_1605_);
lean_dec(v_snd_1599_);
lean_dec(v_fst_1598_);
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1593_);
lean_dec_ref(v___x_1592_);
lean_del_object(v___x_1580_);
lean_dec(v_u_1348_);
v_a_1652_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1610_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1610_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
else
{
lean_dec(v_snd_1599_);
lean_dec(v_fst_1598_);
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1593_);
lean_dec_ref(v___x_1592_);
lean_del_object(v___x_1580_);
lean_dec(v_u_1348_);
return v___x_1602_;
}
}
}
else
{
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1593_);
lean_dec_ref(v___x_1592_);
lean_del_object(v___x_1580_);
lean_dec(v_tail_1575_);
lean_del_object(v___x_1572_);
lean_dec_ref(v_k_1352_);
lean_dec(v_u_1348_);
return v___x_1595_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_h_1666_; lean_object* v___f_1667_; lean_object* v___x_1668_; 
v_h_1666_ = lean_ctor_get(v_pat_1351_, 0);
lean_inc(v_h_1666_);
lean_dec_ref_known(v_pat_1351_, 1);
lean_inc_ref(v_00_u03c3s_1349_);
v___f_1667_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1667_, 0, v_u_1348_);
lean_closure_set(v___f_1667_, 1, v_00_u03c3s_1349_);
lean_closure_set(v___f_1667_, 2, v_k_1352_);
v___x_1668_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1349_, v_H_1350_, v_h_1666_, v___f_1667_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
return v___x_1668_;
}
default: 
{
lean_object* v_h_1669_; lean_object* v___x_1670_; 
lean_dec(v_u_1348_);
v_h_1669_ = lean_ctor_get(v_pat_1351_, 0);
lean_inc(v_h_1669_);
lean_dec_ref_known(v_pat_1351_, 1);
v___x_1670_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_h_1669_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v_fst_1672_; lean_object* v_snd_1673_; lean_object* v___x_1674_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
v_fst_1672_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_fst_1672_);
v_snd_1673_ = lean_ctor_get(v_a_1671_, 1);
lean_inc(v_snd_1673_);
lean_dec(v_a_1671_);
v___x_1674_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v_a_1356_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; lean_object* v___x_1679_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
v___x_1676_ = l_Lean_Expr_consumeMData(v_H_1350_);
lean_dec_ref(v_H_1350_);
v___x_1677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1677_, 0, v_fst_1672_);
lean_ctor_set(v___x_1677_, 1, v_a_1675_);
lean_ctor_set(v___x_1677_, 2, v___x_1676_);
v___x_1678_ = 1;
lean_inc_ref(v___x_1677_);
v___x_1679_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1673_, v_00_u03c3s_1349_, v___x_1677_, v___x_1678_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec_ref_known(v___x_1679_, 1);
v___x_1680_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1677_);
lean_inc(v_a_1356_);
lean_inc_ref(v_a_1355_);
lean_inc(v_a_1354_);
lean_inc_ref(v_a_1353_);
v___x_1681_ = lean_apply_6(v_k_1352_, v___x_1680_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, lean_box(0));
return v___x_1681_;
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref_known(v___x_1677_, 3);
lean_dec_ref(v_k_1352_);
v_a_1682_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1679_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1679_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_dec(v_snd_1673_);
lean_dec(v_fst_1672_);
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
v_a_1690_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1674_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1674_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec_ref(v_k_1352_);
lean_dec_ref(v_H_1350_);
lean_dec_ref(v_00_u03c3s_1349_);
v_a_1698_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1670_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1670_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(lean_object* v___x_1706_, lean_object* v_tail_1707_, lean_object* v_u_1708_, lean_object* v___x_1709_, lean_object* v_k_1710_, lean_object* v_x_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = lean_mk_empty_array_with_capacity(v___x_1717_);
v___x_1719_ = lean_array_push(v___x_1718_, v_x_1711_);
v___x_1720_ = 0;
v___x_1721_ = l_Lean_Expr_betaRev(v___x_1706_, v___x_1719_, v___x_1720_, v___x_1720_);
lean_dec_ref(v___x_1719_);
v___x_1722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_tail_1707_);
v___x_1723_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1708_, v___x_1709_, v___x_1721_, v___x_1722_, v_k_1710_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(lean_object* v_u_1724_, lean_object* v_00_u03c3s_1725_, lean_object* v_H_1726_, lean_object* v_pat_1727_, lean_object* v_k_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1724_, v_00_u03c3s_1725_, v_H_1726_, v_pat_1727_, v_k_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_object* v_00_u03b1_1735_, lean_object* v_u_1736_, lean_object* v_00_u03c3s_1737_, lean_object* v_H_1738_, lean_object* v_pat_1739_, lean_object* v_k_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1736_, v_00_u03c3s_1737_, v_H_1738_, v_pat_1739_, v_k_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_u_1748_, lean_object* v_00_u03c3s_1749_, lean_object* v_H_1750_, lean_object* v_pat_1751_, lean_object* v_k_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(v_00_u03b1_1747_, v_u_1748_, v_00_u03c3s_1749_, v_H_1750_, v_pat_1751_, v_k_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_);
lean_dec(v_a_1756_);
lean_dec_ref(v_a_1755_);
lean_dec(v_a_1754_);
lean_dec_ref(v_a_1753_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_object* v_00_u03b1_1759_, lean_object* v_00_u03c3s_1760_, lean_object* v_hyp_1761_, lean_object* v_name_1762_, lean_object* v_k_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1760_, v_hyp_1761_, v_name_1762_, v_k_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_00_u03c3s_1771_, lean_object* v_hyp_1772_, lean_object* v_name_1773_, lean_object* v_k_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(v_00_u03b1_1770_, v_00_u03c3s_1771_, v_hyp_1772_, v_name_1773_, v_k_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg(){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_object* v_00_u03b1_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(lean_object* v_00_u03b1_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(v_00_u03b1_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(lean_object* v_x_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
v___x_1818_ = lean_apply_9(v_x_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, lean_box(0));
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(lean_object* v_x_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(lean_object* v_mvarId_1830_, lean_object* v_x_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___f_1841_; lean_object* v___x_1842_; 
lean_inc(v___y_1835_);
lean_inc_ref(v___y_1834_);
lean_inc(v___y_1833_);
lean_inc_ref(v___y_1832_);
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1841_, 0, v_x_1831_);
lean_closure_set(v___f_1841_, 1, v___y_1832_);
lean_closure_set(v___f_1841_, 2, v___y_1833_);
lean_closure_set(v___f_1841_, 3, v___y_1834_);
lean_closure_set(v___f_1841_, 4, v___y_1835_);
v___x_1842_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1830_, v___f_1841_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1842_) == 0)
{
return v___x_1842_;
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(lean_object* v_mvarId_1851_, lean_object* v_x_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1851_, v_x_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec_ref(v___y_1857_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_object* v_00_u03b1_1863_, lean_object* v_mvarId_1864_, lean_object* v_x_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1864_, v_x_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(lean_object* v_00_u03b1_1876_, lean_object* v_mvarId_1877_, lean_object* v_x_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(v_00_u03b1_1876_, v_mvarId_1877_, v_x_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v_ks_1893_; lean_object* v_vs_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1918_; 
v_ks_1893_ = lean_ctor_get(v_x_1889_, 0);
v_vs_1894_ = lean_ctor_get(v_x_1889_, 1);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_x_1889_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1896_ = v_x_1889_;
v_isShared_1897_ = v_isSharedCheck_1918_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_vs_1894_);
lean_inc(v_ks_1893_);
lean_dec(v_x_1889_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1918_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = lean_array_get_size(v_ks_1893_);
v___x_1899_ = lean_nat_dec_lt(v_x_1890_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
lean_dec(v_x_1890_);
v___x_1900_ = lean_array_push(v_ks_1893_, v_x_1891_);
v___x_1901_ = lean_array_push(v_vs_1894_, v_x_1892_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v___x_1901_);
lean_ctor_set(v___x_1896_, 0, v___x_1900_);
v___x_1903_ = v___x_1896_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1900_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
else
{
lean_object* v_k_x27_1905_; uint8_t v___x_1906_; 
v_k_x27_1905_ = lean_array_fget_borrowed(v_ks_1893_, v_x_1890_);
v___x_1906_ = l_Lean_instBEqMVarId_beq(v_x_1891_, v_k_x27_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1908_; 
if (v_isShared_1897_ == 0)
{
v___x_1908_ = v___x_1896_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_ks_1893_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_vs_1894_);
v___x_1908_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_unsigned_to_nat(1u);
v___x_1910_ = lean_nat_add(v_x_1890_, v___x_1909_);
lean_dec(v_x_1890_);
v_x_1889_ = v___x_1908_;
v_x_1890_ = v___x_1910_;
goto _start;
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1913_ = lean_array_fset(v_ks_1893_, v_x_1890_, v_x_1891_);
v___x_1914_ = lean_array_fset(v_vs_1894_, v_x_1890_, v_x_1892_);
lean_dec(v_x_1890_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v___x_1914_);
lean_ctor_set(v___x_1896_, 0, v___x_1913_);
v___x_1916_ = v___x_1896_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(lean_object* v_n_1919_, lean_object* v_k_1920_, lean_object* v_v_1921_){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_unsigned_to_nat(0u);
v___x_1923_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_n_1919_, v___x_1922_, v_k_1920_, v_v_1921_);
return v___x_1923_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(lean_object* v_x_1925_, size_t v_x_1926_, size_t v_x_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_){
_start:
{
if (lean_obj_tag(v_x_1925_) == 0)
{
lean_object* v_es_1930_; size_t v___x_1931_; size_t v___x_1932_; lean_object* v_j_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_es_1930_ = lean_ctor_get(v_x_1925_, 0);
v___x_1931_ = ((size_t)31ULL);
v___x_1932_ = lean_usize_land(v_x_1926_, v___x_1931_);
v_j_1933_ = lean_usize_to_nat(v___x_1932_);
v___x_1934_ = lean_array_get_size(v_es_1930_);
v___x_1935_ = lean_nat_dec_lt(v_j_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_dec(v_j_1933_);
lean_dec(v_x_1929_);
lean_dec(v_x_1928_);
return v_x_1925_;
}
else
{
lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1974_; 
lean_inc_ref(v_es_1930_);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_x_1925_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v_x_1925_, 0);
lean_dec(v_unused_1975_);
v___x_1937_ = v_x_1925_;
v_isShared_1938_ = v_isSharedCheck_1974_;
goto v_resetjp_1936_;
}
else
{
lean_dec(v_x_1925_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1974_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_v_1939_; lean_object* v___x_1940_; lean_object* v_xs_x27_1941_; lean_object* v___y_1943_; 
v_v_1939_ = lean_array_fget(v_es_1930_, v_j_1933_);
v___x_1940_ = lean_box(0);
v_xs_x27_1941_ = lean_array_fset(v_es_1930_, v_j_1933_, v___x_1940_);
switch(lean_obj_tag(v_v_1939_))
{
case 0:
{
lean_object* v_key_1948_; lean_object* v_val_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1959_; 
v_key_1948_ = lean_ctor_get(v_v_1939_, 0);
v_val_1949_ = lean_ctor_get(v_v_1939_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_v_1939_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1951_ = v_v_1939_;
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_val_1949_);
lean_inc(v_key_1948_);
lean_dec(v_v_1939_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1959_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
uint8_t v___x_1953_; 
v___x_1953_ = l_Lean_instBEqMVarId_beq(v_x_1928_, v_key_1948_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_del_object(v___x_1951_);
v___x_1954_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1948_, v_val_1949_, v_x_1928_, v_x_1929_);
v___x_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
v___y_1943_ = v___x_1955_;
goto v___jp_1942_;
}
else
{
lean_object* v___x_1957_; 
lean_dec(v_val_1949_);
lean_dec(v_key_1948_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 1, v_x_1929_);
lean_ctor_set(v___x_1951_, 0, v_x_1928_);
v___x_1957_ = v___x_1951_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_x_1928_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_x_1929_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
v___y_1943_ = v___x_1957_;
goto v___jp_1942_;
}
}
}
}
case 1:
{
lean_object* v_node_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1972_; 
v_node_1960_ = lean_ctor_get(v_v_1939_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_v_1939_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1962_ = v_v_1939_;
v_isShared_1963_ = v_isSharedCheck_1972_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_node_1960_);
lean_dec(v_v_1939_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1972_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
size_t v___x_1964_; size_t v___x_1965_; size_t v___x_1966_; size_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1964_ = ((size_t)5ULL);
v___x_1965_ = lean_usize_shift_right(v_x_1926_, v___x_1964_);
v___x_1966_ = ((size_t)1ULL);
v___x_1967_ = lean_usize_add(v_x_1927_, v___x_1966_);
v___x_1968_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_node_1960_, v___x_1965_, v___x_1967_, v_x_1928_, v_x_1929_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1968_);
v___x_1970_ = v___x_1962_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
v___y_1943_ = v___x_1970_;
goto v___jp_1942_;
}
}
}
default: 
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_x_1928_);
lean_ctor_set(v___x_1973_, 1, v_x_1929_);
v___y_1943_ = v___x_1973_;
goto v___jp_1942_;
}
}
v___jp_1942_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = lean_array_fset(v_xs_x27_1941_, v_j_1933_, v___y_1943_);
lean_dec(v_j_1933_);
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 0, v___x_1944_);
v___x_1946_ = v___x_1937_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
else
{
lean_object* v_ks_1976_; lean_object* v_vs_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1995_; 
v_ks_1976_ = lean_ctor_get(v_x_1925_, 0);
v_vs_1977_ = lean_ctor_get(v_x_1925_, 1);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_x_1925_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1979_ = v_x_1925_;
v_isShared_1980_ = v_isSharedCheck_1995_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_vs_1977_);
lean_inc(v_ks_1976_);
lean_dec(v_x_1925_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1995_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_ks_1976_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_vs_1977_);
v___x_1982_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v_newNode_1983_; size_t v___x_1984_; uint8_t v___x_1985_; 
v_newNode_1983_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v___x_1982_, v_x_1928_, v_x_1929_);
v___x_1984_ = ((size_t)7ULL);
v___x_1985_ = lean_usize_dec_le(v___x_1984_, v_x_1927_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1983_);
v___x_1987_ = lean_unsigned_to_nat(4u);
v___x_1988_ = lean_nat_dec_lt(v___x_1986_, v___x_1987_);
lean_dec(v___x_1986_);
if (v___x_1988_ == 0)
{
lean_object* v_ks_1989_; lean_object* v_vs_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_ks_1989_ = lean_ctor_get(v_newNode_1983_, 0);
lean_inc_ref(v_ks_1989_);
v_vs_1990_ = lean_ctor_get(v_newNode_1983_, 1);
lean_inc_ref(v_vs_1990_);
lean_dec_ref(v_newNode_1983_);
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0);
v___x_1993_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_x_1927_, v_ks_1989_, v_vs_1990_, v___x_1991_, v___x_1992_);
lean_dec_ref(v_vs_1990_);
lean_dec_ref(v_ks_1989_);
return v___x_1993_;
}
else
{
return v_newNode_1983_;
}
}
else
{
return v_newNode_1983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(size_t v_depth_1996_, lean_object* v_keys_1997_, lean_object* v_vals_1998_, lean_object* v_i_1999_, lean_object* v_entries_2000_){
_start:
{
lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = lean_array_get_size(v_keys_1997_);
v___x_2002_ = lean_nat_dec_lt(v_i_1999_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_dec(v_i_1999_);
return v_entries_2000_;
}
else
{
lean_object* v_k_2003_; lean_object* v_v_2004_; uint64_t v___x_2005_; size_t v_h_2006_; size_t v___x_2007_; lean_object* v___x_2008_; size_t v___x_2009_; size_t v___x_2010_; size_t v___x_2011_; size_t v_h_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_k_2003_ = lean_array_fget_borrowed(v_keys_1997_, v_i_1999_);
v_v_2004_ = lean_array_fget_borrowed(v_vals_1998_, v_i_1999_);
v___x_2005_ = l_Lean_instHashableMVarId_hash(v_k_2003_);
v_h_2006_ = lean_uint64_to_usize(v___x_2005_);
v___x_2007_ = ((size_t)5ULL);
v___x_2008_ = lean_unsigned_to_nat(1u);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_sub(v_depth_1996_, v___x_2009_);
v___x_2011_ = lean_usize_mul(v___x_2007_, v___x_2010_);
v_h_2012_ = lean_usize_shift_right(v_h_2006_, v___x_2011_);
v___x_2013_ = lean_nat_add(v_i_1999_, v___x_2008_);
lean_dec(v_i_1999_);
lean_inc(v_v_2004_);
lean_inc(v_k_2003_);
v___x_2014_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_entries_2000_, v_h_2012_, v_depth_1996_, v_k_2003_, v_v_2004_);
v_i_1999_ = v___x_2013_;
v_entries_2000_ = v___x_2014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg___boxed(lean_object* v_depth_2016_, lean_object* v_keys_2017_, lean_object* v_vals_2018_, lean_object* v_i_2019_, lean_object* v_entries_2020_){
_start:
{
size_t v_depth_boxed_2021_; lean_object* v_res_2022_; 
v_depth_boxed_2021_ = lean_unbox_usize(v_depth_2016_);
lean_dec(v_depth_2016_);
v_res_2022_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_boxed_2021_, v_keys_2017_, v_vals_2018_, v_i_2019_, v_entries_2020_);
lean_dec_ref(v_vals_2018_);
lean_dec_ref(v_keys_2017_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
size_t v_x_19739__boxed_2028_; size_t v_x_19740__boxed_2029_; lean_object* v_res_2030_; 
v_x_19739__boxed_2028_ = lean_unbox_usize(v_x_2024_);
lean_dec(v_x_2024_);
v_x_19740__boxed_2029_ = lean_unbox_usize(v_x_2025_);
lean_dec(v_x_2025_);
v_res_2030_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2023_, v_x_19739__boxed_2028_, v_x_19740__boxed_2029_, v_x_2026_, v_x_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
uint64_t v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; lean_object* v___x_2037_; 
v___x_2034_ = l_Lean_instHashableMVarId_hash(v_x_2032_);
v___x_2035_ = lean_uint64_to_usize(v___x_2034_);
v___x_2036_ = ((size_t)1ULL);
v___x_2037_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2031_, v___x_2035_, v___x_2036_, v_x_2032_, v_x_2033_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object* v_mvarId_2038_, lean_object* v_val_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v_mctx_2043_; lean_object* v_cache_2044_; lean_object* v_zetaDeltaFVarIds_2045_; lean_object* v_postponed_2046_; lean_object* v_diag_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2077_; 
v___x_2042_ = lean_st_ref_take(v___y_2040_);
v_mctx_2043_ = lean_ctor_get(v___x_2042_, 0);
v_cache_2044_ = lean_ctor_get(v___x_2042_, 1);
v_zetaDeltaFVarIds_2045_ = lean_ctor_get(v___x_2042_, 2);
v_postponed_2046_ = lean_ctor_get(v___x_2042_, 3);
v_diag_2047_ = lean_ctor_get(v___x_2042_, 4);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2049_ = v___x_2042_;
v_isShared_2050_ = v_isSharedCheck_2077_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_diag_2047_);
lean_inc(v_postponed_2046_);
lean_inc(v_zetaDeltaFVarIds_2045_);
lean_inc(v_cache_2044_);
lean_inc(v_mctx_2043_);
lean_dec(v___x_2042_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2077_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v_depth_2051_; lean_object* v_levelAssignDepth_2052_; lean_object* v_lmvarCounter_2053_; lean_object* v_mvarCounter_2054_; lean_object* v_lDecls_2055_; lean_object* v_decls_2056_; lean_object* v_userNames_2057_; lean_object* v_lAssignment_2058_; lean_object* v_eAssignment_2059_; lean_object* v_dAssignment_2060_; lean_object* v_instanceTypedMVars_2061_; lean_object* v_synthNormMemo_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2076_; 
v_depth_2051_ = lean_ctor_get(v_mctx_2043_, 0);
v_levelAssignDepth_2052_ = lean_ctor_get(v_mctx_2043_, 1);
v_lmvarCounter_2053_ = lean_ctor_get(v_mctx_2043_, 2);
v_mvarCounter_2054_ = lean_ctor_get(v_mctx_2043_, 3);
v_lDecls_2055_ = lean_ctor_get(v_mctx_2043_, 4);
v_decls_2056_ = lean_ctor_get(v_mctx_2043_, 5);
v_userNames_2057_ = lean_ctor_get(v_mctx_2043_, 6);
v_lAssignment_2058_ = lean_ctor_get(v_mctx_2043_, 7);
v_eAssignment_2059_ = lean_ctor_get(v_mctx_2043_, 8);
v_dAssignment_2060_ = lean_ctor_get(v_mctx_2043_, 9);
v_instanceTypedMVars_2061_ = lean_ctor_get(v_mctx_2043_, 10);
v_synthNormMemo_2062_ = lean_ctor_get(v_mctx_2043_, 11);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_mctx_2043_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2064_ = v_mctx_2043_;
v_isShared_2065_ = v_isSharedCheck_2076_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_synthNormMemo_2062_);
lean_inc(v_instanceTypedMVars_2061_);
lean_inc(v_dAssignment_2060_);
lean_inc(v_eAssignment_2059_);
lean_inc(v_lAssignment_2058_);
lean_inc(v_userNames_2057_);
lean_inc(v_decls_2056_);
lean_inc(v_lDecls_2055_);
lean_inc(v_mvarCounter_2054_);
lean_inc(v_lmvarCounter_2053_);
lean_inc(v_levelAssignDepth_2052_);
lean_inc(v_depth_2051_);
lean_dec(v_mctx_2043_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2076_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2066_ = lean_box(0);
v___x_2067_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_eAssignment_2059_, v_mvarId_2038_, v_val_2039_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 8, v___x_2067_);
v___x_2069_ = v___x_2064_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_depth_2051_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_levelAssignDepth_2052_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_lmvarCounter_2053_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_mvarCounter_2054_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_lDecls_2055_);
lean_ctor_set(v_reuseFailAlloc_2075_, 5, v_decls_2056_);
lean_ctor_set(v_reuseFailAlloc_2075_, 6, v_userNames_2057_);
lean_ctor_set(v_reuseFailAlloc_2075_, 7, v_lAssignment_2058_);
lean_ctor_set(v_reuseFailAlloc_2075_, 8, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2075_, 9, v_dAssignment_2060_);
lean_ctor_set(v_reuseFailAlloc_2075_, 10, v_instanceTypedMVars_2061_);
lean_ctor_set(v_reuseFailAlloc_2075_, 11, v_synthNormMemo_2062_);
v___x_2069_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 0, v___x_2069_);
v___x_2071_ = v___x_2049_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_cache_2044_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_zetaDeltaFVarIds_2045_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_postponed_2046_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_diag_2047_);
v___x_2071_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_st_ref_put(v___y_2040_, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2066_);
return v___x_2073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object* v_mvarId_2078_, lean_object* v_val_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_2078_, v_val_2079_, v___y_2080_);
lean_dec(v___y_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object* v_snd_2085_, lean_object* v_hyp_2086_, lean_object* v_a_2087_, lean_object* v_fst_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
lean_inc_ref(v_snd_2085_);
v___x_2098_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_snd_2085_, v_hyp_2086_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v_focusHyp_2100_; lean_object* v_restHyps_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_u_2104_; lean_object* v_00_u03c3s_2105_; lean_object* v_target_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v_focusHyp_2100_ = lean_ctor_get(v_a_2099_, 0);
v_restHyps_2101_ = lean_ctor_get(v_a_2099_, 1);
v___x_2102_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0));
v___x_2103_ = lean_st_mk_ref(v___x_2102_);
v_u_2104_ = lean_ctor_get(v_snd_2085_, 0);
v_00_u03c3s_2105_ = lean_ctor_get(v_snd_2085_, 1);
v_target_2106_ = lean_ctor_get(v_snd_2085_, 3);
lean_inc_ref(v_restHyps_2101_);
lean_inc_ref(v_target_2106_);
lean_inc_ref_n(v_00_u03c3s_2105_, 2);
lean_inc(v___x_2103_);
lean_inc_n(v_u_2104_, 2);
v___x_2107_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed), 11, 5);
lean_closure_set(v___x_2107_, 0, v_u_2104_);
lean_closure_set(v___x_2107_, 1, v___x_2103_);
lean_closure_set(v___x_2107_, 2, v_00_u03c3s_2105_);
lean_closure_set(v___x_2107_, 3, v_target_2106_);
lean_closure_set(v___x_2107_, 4, v_restHyps_2101_);
lean_inc_ref(v_focusHyp_2100_);
v___x_2108_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_2104_, v_00_u03c3s_2105_, v_focusHyp_2100_, v_a_2087_, v___x_2107_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v_snd_2110_; lean_object* v_snd_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v_snd_2110_ = lean_ctor_get(v_a_2109_, 1);
lean_inc(v_snd_2110_);
lean_dec(v_a_2109_);
v_snd_2111_ = lean_ctor_get(v_snd_2110_, 1);
lean_inc(v_snd_2111_);
lean_dec(v_snd_2110_);
v___x_2112_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(v_a_2099_, v_snd_2085_, v_snd_2111_);
v___x_2113_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_fst_2088_, v___x_2112_, v___y_2094_);
lean_dec_ref(v___x_2113_);
v___x_2114_ = lean_st_ref_get(v___x_2103_);
lean_dec(v___x_2103_);
v___x_2115_ = lean_array_to_list(v___x_2114_);
v___x_2116_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2115_, v___y_2090_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
return v___x_2116_;
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v___x_2103_);
lean_dec(v_a_2099_);
lean_dec(v_fst_2088_);
lean_dec_ref(v_snd_2085_);
v_a_2117_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2108_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2108_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_fst_2088_);
lean_dec(v_a_2087_);
lean_dec_ref(v_snd_2085_);
v_a_2125_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2098_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2098_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object* v_snd_2133_, lean_object* v_hyp_2134_, lean_object* v_a_2135_, lean_object* v_fst_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(v_snd_2133_, v_hyp_2134_, v_a_2135_, v_fst_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2146_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2147_; double v___x_2148_; 
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_float_of_nat(v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object* v_cls_2152_, lean_object* v_msg_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_ref_2159_; lean_object* v___x_2160_; lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2206_; 
v_ref_2159_ = lean_ctor_get(v___y_2156_, 2);
v___x_2160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2206_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2206_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v_traceState_2166_; lean_object* v_env_2167_; lean_object* v_nextMacroScope_2168_; lean_object* v_ngen_2169_; lean_object* v_auxDeclNGen_2170_; lean_object* v_cache_2171_; lean_object* v_recordedDeps_2172_; lean_object* v_messages_2173_; lean_object* v_infoState_2174_; lean_object* v_snapshotTasks_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2205_; 
v___x_2165_ = lean_st_ref_take(v___y_2157_);
v_traceState_2166_ = lean_ctor_get(v___x_2165_, 4);
v_env_2167_ = lean_ctor_get(v___x_2165_, 0);
v_nextMacroScope_2168_ = lean_ctor_get(v___x_2165_, 1);
v_ngen_2169_ = lean_ctor_get(v___x_2165_, 2);
v_auxDeclNGen_2170_ = lean_ctor_get(v___x_2165_, 3);
v_cache_2171_ = lean_ctor_get(v___x_2165_, 5);
v_recordedDeps_2172_ = lean_ctor_get(v___x_2165_, 6);
v_messages_2173_ = lean_ctor_get(v___x_2165_, 7);
v_infoState_2174_ = lean_ctor_get(v___x_2165_, 8);
v_snapshotTasks_2175_ = lean_ctor_get(v___x_2165_, 9);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2177_ = v___x_2165_;
v_isShared_2178_ = v_isSharedCheck_2205_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snapshotTasks_2175_);
lean_inc(v_infoState_2174_);
lean_inc(v_messages_2173_);
lean_inc(v_recordedDeps_2172_);
lean_inc(v_cache_2171_);
lean_inc(v_traceState_2166_);
lean_inc(v_auxDeclNGen_2170_);
lean_inc(v_ngen_2169_);
lean_inc(v_nextMacroScope_2168_);
lean_inc(v_env_2167_);
lean_dec(v___x_2165_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2205_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint64_t v_tid_2179_; lean_object* v_traces_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2204_; 
v_tid_2179_ = lean_ctor_get_uint64(v_traceState_2166_, sizeof(void*)*1);
v_traces_2180_ = lean_ctor_get(v_traceState_2166_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_traceState_2166_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2182_ = v_traceState_2166_;
v_isShared_2183_ = v_isSharedCheck_2204_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_traces_2180_);
lean_dec(v_traceState_2166_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2204_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; double v___x_2186_; uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2184_ = lean_box(0);
v___x_2185_ = lean_box(0);
v___x_2186_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0);
v___x_2187_ = 0;
v___x_2188_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2189_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2189_, 0, v_cls_2152_);
lean_ctor_set(v___x_2189_, 1, v___x_2185_);
lean_ctor_set(v___x_2189_, 2, v___x_2188_);
lean_ctor_set_float(v___x_2189_, sizeof(void*)*3, v___x_2186_);
lean_ctor_set_float(v___x_2189_, sizeof(void*)*3 + 8, v___x_2186_);
lean_ctor_set_uint8(v___x_2189_, sizeof(void*)*3 + 16, v___x_2187_);
v___x_2190_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2));
v___x_2191_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v_a_2161_);
lean_ctor_set(v___x_2191_, 2, v___x_2190_);
lean_inc(v_ref_2159_);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v_ref_2159_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = l_Lean_PersistentArray_push___redArg(v_traces_2180_, v___x_2192_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2193_);
v___x_2195_ = v___x_2182_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2193_);
lean_ctor_set_uint64(v_reuseFailAlloc_2203_, sizeof(void*)*1, v_tid_2179_);
v___x_2195_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2197_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 4, v___x_2195_);
v___x_2197_ = v___x_2177_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_env_2167_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_nextMacroScope_2168_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_ngen_2169_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_auxDeclNGen_2170_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2202_, 5, v_cache_2171_);
lean_ctor_set(v_reuseFailAlloc_2202_, 6, v_recordedDeps_2172_);
lean_ctor_set(v_reuseFailAlloc_2202_, 7, v_messages_2173_);
lean_ctor_set(v_reuseFailAlloc_2202_, 8, v_infoState_2174_);
lean_ctor_set(v_reuseFailAlloc_2202_, 9, v_snapshotTasks_2175_);
v___x_2197_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_st_ref_put(v___y_2157_, v___x_2197_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2184_);
v___x_2200_ = v___x_2163_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2184_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2207_, lean_object* v_msg_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2207_, v_msg_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object* v_as_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
if (lean_obj_tag(v_as_2218_) == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
else
{
lean_object* v_toCold_2230_; lean_object* v_options_2231_; uint8_t v_hasTrace_2232_; 
v_toCold_2230_ = lean_ctor_get(v___y_2225_, 0);
v_options_2231_ = lean_ctor_get(v_toCold_2230_, 2);
v_hasTrace_2232_ = lean_ctor_get_uint8(v_options_2231_, sizeof(void*)*1);
if (v_hasTrace_2232_ == 0)
{
lean_object* v_tail_2233_; 
v_tail_2233_ = lean_ctor_get(v_as_2218_, 1);
lean_inc(v_tail_2233_);
lean_dec_ref_known(v_as_2218_, 2);
v_as_2218_ = v_tail_2233_;
goto _start;
}
else
{
lean_object* v_head_2235_; lean_object* v_tail_2236_; lean_object* v_fst_2237_; lean_object* v_snd_2238_; lean_object* v_inheritedTraceOptions_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; 
v_head_2235_ = lean_ctor_get(v_as_2218_, 0);
lean_inc(v_head_2235_);
v_tail_2236_ = lean_ctor_get(v_as_2218_, 1);
lean_inc(v_tail_2236_);
lean_dec_ref_known(v_as_2218_, 2);
v_fst_2237_ = lean_ctor_get(v_head_2235_, 0);
lean_inc_n(v_fst_2237_, 2);
v_snd_2238_ = lean_ctor_get(v_head_2235_, 1);
lean_inc(v_snd_2238_);
lean_dec(v_head_2235_);
v_inheritedTraceOptions_2239_ = lean_ctor_get(v_toCold_2230_, 11);
v___x_2240_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2241_ = l_Lean_Name_append(v___x_2240_, v_fst_2237_);
v___x_2242_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2239_, v_options_2231_, v___x_2241_);
lean_dec(v___x_2241_);
if (v___x_2242_ == 0)
{
lean_dec(v_snd_2238_);
lean_dec(v_fst_2237_);
v_as_2218_ = v_tail_2236_;
goto _start;
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2244_, 0, v_snd_2238_);
v___x_2245_ = l_Lean_MessageData_ofFormat(v___x_2244_);
v___x_2246_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_fst_2237_, v___x_2245_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_dec_ref_known(v___x_2246_, 1);
v_as_2218_ = v_tail_2236_;
goto _start;
}
else
{
lean_dec(v_tail_2236_);
return v___x_2246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object* v_as_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object* v_env_2259_, lean_object* v_declName_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
uint8_t v___x_2263_; lean_object* v_env_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; uint8_t v___x_2267_; 
v___x_2263_ = 0;
v_env_2264_ = l_Lean_Environment_setExporting(v_env_2259_, v___x_2263_);
lean_inc(v_declName_2260_);
v___x_2265_ = l_Lean_mkPrivateName(v_env_2264_, v_declName_2260_);
v___x_2266_ = 1;
lean_inc_ref(v_env_2264_);
v___x_2267_ = l_Lean_Environment_contains(v_env_2264_, v___x_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2268_ = l_Lean_privateToUserName(v_declName_2260_);
v___x_2269_ = l_Lean_Environment_contains(v_env_2264_, v___x_2268_, v___x_2266_);
v___x_2270_ = lean_box(v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
lean_ctor_set(v___x_2271_, 1, v___y_2262_);
return v___x_2271_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v_env_2264_);
lean_dec(v_declName_2260_);
v___x_2272_ = lean_box(v___x_2267_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___y_2262_);
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object* v_env_2274_, lean_object* v_declName_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(v_env_2274_, v_declName_2275_, v___y_2276_, v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object* v_msg_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_ref_2285_; lean_object* v___x_2286_; lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2295_; 
v_ref_2285_ = lean_ctor_get(v___y_2282_, 2);
v___x_2286_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2289_ = v___x_2286_;
v_isShared_2290_ = v_isSharedCheck_2295_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2295_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
lean_inc(v_ref_2285_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v_ref_2285_);
lean_ctor_set(v___x_2291_, 1, v_a_2287_);
if (v_isShared_2290_ == 0)
{
lean_ctor_set_tag(v___x_2289_, 1);
lean_ctor_set(v___x_2289_, 0, v___x_2291_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_msg_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object* v_ref_2303_, lean_object* v_msg_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_toCold_2314_; lean_object* v_currRecDepth_2315_; lean_object* v_ref_2316_; uint16_t v_optionFlags_2317_; uint8_t v_suppressElabErrors_2318_; uint8_t v_isRecordingDeps_2319_; lean_object* v_ref_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_toCold_2314_ = lean_ctor_get(v___y_2311_, 0);
v_currRecDepth_2315_ = lean_ctor_get(v___y_2311_, 1);
v_ref_2316_ = lean_ctor_get(v___y_2311_, 2);
v_optionFlags_2317_ = lean_ctor_get_uint16(v___y_2311_, sizeof(void*)*3);
v_suppressElabErrors_2318_ = lean_ctor_get_uint8(v___y_2311_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2319_ = lean_ctor_get_uint8(v___y_2311_, sizeof(void*)*3 + 3);
v_ref_2320_ = l_Lean_replaceRef(v_ref_2303_, v_ref_2316_);
lean_inc(v_currRecDepth_2315_);
lean_inc_ref(v_toCold_2314_);
v___x_2321_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2321_, 0, v_toCold_2314_);
lean_ctor_set(v___x_2321_, 1, v_currRecDepth_2315_);
lean_ctor_set(v___x_2321_, 2, v_ref_2320_);
lean_ctor_set_uint16(v___x_2321_, sizeof(void*)*3, v_optionFlags_2317_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*3 + 2, v_suppressElabErrors_2318_);
lean_ctor_set_uint8(v___x_2321_, sizeof(void*)*3 + 3, v_isRecordingDeps_2319_);
v___x_2322_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2304_, v___y_2309_, v___y_2310_, v___x_2321_, v___y_2312_);
lean_dec_ref_known(v___x_2321_, 3);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2323_, lean_object* v_msg_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_2323_, v_msg_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v_ref_2323_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object* v_env_2335_, lean_object* v_currNamespace_2336_, lean_object* v_openDecls_2337_, lean_object* v_n_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = l_Lean_ResolveName_resolveNamespace(v_env_2335_, v_currNamespace_2336_, v_openDecls_2337_, v_n_2338_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v___y_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object* v_env_2343_, lean_object* v_currNamespace_2344_, lean_object* v_openDecls_2345_, lean_object* v_n_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(v_env_2343_, v_currNamespace_2344_, v_openDecls_2345_, v_n_2346_, v___y_2347_, v___y_2348_);
lean_dec_ref(v___y_2347_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object* v_env_2350_, lean_object* v___x_2351_, lean_object* v_currNamespace_2352_, lean_object* v_openDecls_2353_, lean_object* v_n_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = l_Lean_ResolveName_resolveGlobalName(v_env_2350_, v___x_2351_, v_currNamespace_2352_, v_openDecls_2353_, v_n_2354_);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object* v_env_2359_, lean_object* v___x_2360_, lean_object* v_currNamespace_2361_, lean_object* v_openDecls_2362_, lean_object* v_n_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(v_env_2359_, v___x_2360_, v_currNamespace_2361_, v_openDecls_2362_, v_n_2363_, v___y_2364_, v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec_ref(v___x_2360_);
return v_res_2366_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = l_Lean_maxRecDepthErrorMessage;
v___x_2373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3);
v___x_2375_ = l_Lean_MessageData_ofFormat(v___x_2374_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4);
v___x_2377_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2));
v___x_2378_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
lean_ctor_set(v___x_2378_, 1, v___x_2376_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object* v_ref_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_ref_2379_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object* v_currNamespace_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_currNamespace_2387_);
lean_ctor_set(v___x_2390_, 1, v___y_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object* v_currNamespace_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(v_currNamespace_2391_, v___y_2392_, v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2394_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object* v_keys_2395_, lean_object* v_i_2396_, lean_object* v_k_2397_){
_start:
{
lean_object* v___x_2398_; uint8_t v___x_2399_; 
v___x_2398_ = lean_array_get_size(v_keys_2395_);
v___x_2399_ = lean_nat_dec_lt(v_i_2396_, v___x_2398_);
if (v___x_2399_ == 0)
{
lean_dec(v_i_2396_);
return v___x_2399_;
}
else
{
lean_object* v_k_x27_2400_; uint8_t v___x_2401_; 
v_k_x27_2400_ = lean_array_fget_borrowed(v_keys_2395_, v_i_2396_);
v___x_2401_ = l_Lean_instBEqExtraModUse_beq(v_k_2397_, v_k_x27_2400_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_unsigned_to_nat(1u);
v___x_2403_ = lean_nat_add(v_i_2396_, v___x_2402_);
lean_dec(v_i_2396_);
v_i_2396_ = v___x_2403_;
goto _start;
}
else
{
lean_dec(v_i_2396_);
return v___x_2399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object* v_keys_2405_, lean_object* v_i_2406_, lean_object* v_k_2407_){
_start:
{
uint8_t v_res_2408_; lean_object* v_r_2409_; 
v_res_2408_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_2405_, v_i_2406_, v_k_2407_);
lean_dec_ref(v_k_2407_);
lean_dec_ref(v_keys_2405_);
v_r_2409_ = lean_box(v_res_2408_);
return v_r_2409_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object* v_x_2410_, size_t v_x_2411_, lean_object* v_x_2412_){
_start:
{
if (lean_obj_tag(v_x_2410_) == 0)
{
lean_object* v_es_2413_; lean_object* v___x_2414_; size_t v___x_2415_; size_t v___x_2416_; lean_object* v_j_2417_; lean_object* v___x_2418_; 
v_es_2413_ = lean_ctor_get(v_x_2410_, 0);
v___x_2414_ = lean_box(2);
v___x_2415_ = ((size_t)31ULL);
v___x_2416_ = lean_usize_land(v_x_2411_, v___x_2415_);
v_j_2417_ = lean_usize_to_nat(v___x_2416_);
v___x_2418_ = lean_array_get_borrowed(v___x_2414_, v_es_2413_, v_j_2417_);
lean_dec(v_j_2417_);
switch(lean_obj_tag(v___x_2418_))
{
case 0:
{
lean_object* v_key_2419_; uint8_t v___x_2420_; 
v_key_2419_ = lean_ctor_get(v___x_2418_, 0);
v___x_2420_ = l_Lean_instBEqExtraModUse_beq(v_x_2412_, v_key_2419_);
return v___x_2420_;
}
case 1:
{
lean_object* v_node_2421_; size_t v___x_2422_; size_t v___x_2423_; 
v_node_2421_ = lean_ctor_get(v___x_2418_, 0);
v___x_2422_ = ((size_t)5ULL);
v___x_2423_ = lean_usize_shift_right(v_x_2411_, v___x_2422_);
v_x_2410_ = v_node_2421_;
v_x_2411_ = v___x_2423_;
goto _start;
}
default: 
{
uint8_t v___x_2425_; 
v___x_2425_ = 0;
return v___x_2425_;
}
}
}
else
{
lean_object* v_ks_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v_ks_2426_ = lean_ctor_get(v_x_2410_, 0);
v___x_2427_ = lean_unsigned_to_nat(0u);
v___x_2428_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_ks_2426_, v___x_2427_, v_x_2412_);
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_x_2429_, lean_object* v_x_2430_, lean_object* v_x_2431_){
_start:
{
size_t v_x_20406__boxed_2432_; uint8_t v_res_2433_; lean_object* v_r_2434_; 
v_x_20406__boxed_2432_ = lean_unbox_usize(v_x_2430_);
lean_dec(v_x_2430_);
v_res_2433_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2429_, v_x_20406__boxed_2432_, v_x_2431_);
lean_dec_ref(v_x_2431_);
lean_dec_ref(v_x_2429_);
v_r_2434_ = lean_box(v_res_2433_);
return v_r_2434_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object* v_x_2435_, lean_object* v_x_2436_){
_start:
{
uint64_t v___x_2437_; size_t v___x_2438_; uint8_t v___x_2439_; 
v___x_2437_ = l_Lean_instHashableExtraModUse_hash(v_x_2436_);
v___x_2438_ = lean_uint64_to_usize(v___x_2437_);
v___x_2439_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2435_, v___x_2438_, v_x_2436_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_2440_, lean_object* v_x_2441_){
_start:
{
uint8_t v_res_2442_; lean_object* v_r_2443_; 
v_res_2442_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_2440_, v_x_2441_);
lean_dec_ref(v_x_2441_);
lean_dec_ref(v_x_2440_);
v_r_2443_ = lean_box(v_res_2442_);
return v_r_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___lam__0(lean_object* v___x_2444_, lean_object* v_entry_2445_, lean_object* v_s_2446_){
_start:
{
lean_object* v_addEntryFn_2447_; lean_object* v_importedEntries_2448_; lean_object* v_state_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2457_; 
v_addEntryFn_2447_ = lean_ctor_get(v___x_2444_, 3);
lean_inc(v_addEntryFn_2447_);
lean_dec_ref(v___x_2444_);
v_importedEntries_2448_ = lean_ctor_get(v_s_2446_, 0);
v_state_2449_ = lean_ctor_get(v_s_2446_, 1);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_s_2446_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2451_ = v_s_2446_;
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_state_2449_);
lean_inc(v_importedEntries_2448_);
lean_dec(v_s_2446_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_state_2453_; lean_object* v___x_2455_; 
v_state_2453_ = lean_apply_2(v_addEntryFn_2447_, v_state_2449_, v_entry_2445_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v_state_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_importedEntries_2448_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_state_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2458_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0);
v___x_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2461_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
return v___x_2462_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2463_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1);
v___x_2464_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
lean_ctor_set(v___x_2464_, 2, v___x_2463_);
lean_ctor_set(v___x_2464_, 3, v___x_2463_);
lean_ctor_set(v___x_2464_, 4, v___x_2463_);
lean_ctor_set(v___x_2464_, 5, v___x_2463_);
return v___x_2464_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_2465_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7));
v___x_2471_ = l_Lean_stringToMessageData(v___x_2470_);
return v___x_2471_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9));
v___x_2474_ = l_Lean_stringToMessageData(v___x_2473_);
return v___x_2474_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11(void){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2476_ = l_Lean_stringToMessageData(v___x_2475_);
return v___x_2476_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v_cls_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_cls_2477_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6));
v___x_2478_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2479_ = l_Lean_Name_append(v___x_2478_, v_cls_2477_);
return v___x_2479_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13));
v___x_2482_ = l_Lean_stringToMessageData(v___x_2481_);
return v___x_2482_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15));
v___x_2485_ = l_Lean_stringToMessageData(v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object* v_mod_2490_, uint8_t v_isMeta_2491_, lean_object* v_hint_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_env_2536_; uint8_t v_isExporting_2537_; lean_object* v_entry_2538_; lean_object* v___x_2539_; lean_object* v_env_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v___x_2534_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
v___x_2535_ = lean_st_ref_get(v___y_2500_);
v_env_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc_ref(v_env_2536_);
lean_dec(v___x_2535_);
v_isExporting_2537_ = lean_ctor_get_uint8(v_env_2536_, sizeof(void*)*13);
lean_dec_ref(v_env_2536_);
lean_inc(v_mod_2490_);
v_entry_2538_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2538_, 0, v_mod_2490_);
lean_ctor_set_uint8(v_entry_2538_, sizeof(void*)*1, v_isExporting_2537_);
lean_ctor_set_uint8(v_entry_2538_, sizeof(void*)*1 + 1, v_isMeta_2491_);
v___x_2539_ = lean_st_ref_get(v___y_2500_);
v_env_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc_ref(v_env_2540_);
lean_dec(v___x_2539_);
v___x_2541_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2542_ = lean_box(1);
v___x_2543_ = lean_box(0);
v___x_2544_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2534_, v___x_2541_, v_env_2540_, v___x_2542_, v___x_2543_);
v___x_2545_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v___x_2544_, v_entry_2538_);
lean_dec(v___x_2544_);
if (v___x_2545_ == 0)
{
lean_object* v_toCold_2546_; lean_object* v_options_2547_; lean_object* v_inheritedTraceOptions_2548_; uint8_t v_hasTrace_2549_; lean_object* v___f_2550_; uint8_t v___x_2551_; lean_object* v___y_2553_; lean_object* v___y_2554_; 
v_toCold_2546_ = lean_ctor_get(v___y_2499_, 0);
v_options_2547_ = lean_ctor_get(v_toCold_2546_, 2);
v_inheritedTraceOptions_2548_ = lean_ctor_get(v_toCold_2546_, 11);
v_hasTrace_2549_ = lean_ctor_get_uint8(v_options_2547_, sizeof(void*)*1);
v___f_2550_ = lean_alloc_closure((void*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___lam__0), 3, 2);
lean_closure_set(v___f_2550_, 0, v___x_2541_);
lean_closure_set(v___f_2550_, 1, v_entry_2538_);
v___x_2551_ = 1;
if (v_hasTrace_2549_ == 0)
{
lean_dec(v_hint_2492_);
lean_dec(v_mod_2490_);
v___y_2553_ = v___y_2498_;
v___y_2554_ = v___y_2500_;
goto v___jp_2552_;
}
else
{
lean_object* v_cls_2581_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___x_2601_; uint8_t v___x_2602_; 
v_cls_2581_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6));
v___x_2601_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12);
v___x_2602_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2548_, v_options_2547_, v___x_2601_);
if (v___x_2602_ == 0)
{
lean_dec(v_hint_2492_);
lean_dec(v_mod_2490_);
v___y_2553_ = v___y_2498_;
v___y_2554_ = v___y_2500_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2603_; lean_object* v___y_2605_; 
v___x_2603_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14);
if (v_isExporting_2537_ == 0)
{
lean_object* v___x_2612_; 
v___x_2612_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19));
v___y_2605_ = v___x_2612_;
goto v___jp_2604_;
}
else
{
lean_object* v___x_2613_; 
v___x_2613_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20));
v___y_2605_ = v___x_2613_;
goto v___jp_2604_;
}
v___jp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_inc_ref(v___y_2605_);
v___x_2606_ = l_Lean_stringToMessageData(v___y_2605_);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2603_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
if (v_isMeta_2491_ == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17));
v___y_2588_ = v___x_2609_;
v___y_2589_ = v___x_2610_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2611_; 
v___x_2611_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18));
v___y_2588_ = v___x_2609_;
v___y_2589_ = v___x_2611_;
goto v___jp_2587_;
}
}
}
v___jp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___y_2583_);
lean_ctor_set(v___x_2585_, 1, v___y_2584_);
v___x_2586_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2581_, v___x_2585_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_dec_ref_known(v___x_2586_, 1);
v___y_2553_ = v___y_2498_;
v___y_2554_ = v___y_2500_;
goto v___jp_2552_;
}
else
{
lean_dec_ref(v___f_2550_);
return v___x_2586_;
}
}
v___jp_2587_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; uint8_t v___x_2596_; 
lean_inc_ref(v___y_2589_);
v___x_2590_ = l_Lean_stringToMessageData(v___y_2589_);
v___x_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___y_2588_);
lean_ctor_set(v___x_2591_, 1, v___x_2590_);
v___x_2592_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8);
v___x_2593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2591_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = l_Lean_MessageData_ofName(v_mod_2490_);
v___x_2595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2593_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = l_Lean_Name_isAnonymous(v_hint_2492_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10);
v___x_2598_ = l_Lean_MessageData_ofName(v_hint_2492_);
v___x_2599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2597_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___y_2583_ = v___x_2595_;
v___y_2584_ = v___x_2599_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2600_; 
lean_dec(v_hint_2492_);
v___x_2600_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11);
v___y_2583_ = v___x_2595_;
v___y_2584_ = v___x_2600_;
goto v___jp_2582_;
}
}
}
v___jp_2552_:
{
lean_object* v___x_2555_; lean_object* v_toEnvExtension_2556_; uint8_t v_logWrites_2557_; 
v___x_2555_ = lean_st_ref_take(v___y_2554_);
v_toEnvExtension_2556_ = lean_ctor_get(v___x_2541_, 0);
v_logWrites_2557_ = lean_ctor_get_uint8(v_toEnvExtension_2556_, sizeof(void*)*6);
if (v_logWrites_2557_ == 0)
{
lean_object* v_env_2558_; lean_object* v_nextMacroScope_2559_; lean_object* v_ngen_2560_; lean_object* v_auxDeclNGen_2561_; lean_object* v_traceState_2562_; lean_object* v_recordedDeps_2563_; lean_object* v_messages_2564_; lean_object* v_infoState_2565_; lean_object* v_snapshotTasks_2566_; lean_object* v_asyncMode_2567_; lean_object* v___x_2568_; 
v_env_2558_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_env_2558_);
v_nextMacroScope_2559_ = lean_ctor_get(v___x_2555_, 1);
lean_inc(v_nextMacroScope_2559_);
v_ngen_2560_ = lean_ctor_get(v___x_2555_, 2);
lean_inc_ref(v_ngen_2560_);
v_auxDeclNGen_2561_ = lean_ctor_get(v___x_2555_, 3);
lean_inc_ref(v_auxDeclNGen_2561_);
v_traceState_2562_ = lean_ctor_get(v___x_2555_, 4);
lean_inc_ref(v_traceState_2562_);
v_recordedDeps_2563_ = lean_ctor_get(v___x_2555_, 6);
lean_inc_ref(v_recordedDeps_2563_);
v_messages_2564_ = lean_ctor_get(v___x_2555_, 7);
lean_inc_ref(v_messages_2564_);
v_infoState_2565_ = lean_ctor_get(v___x_2555_, 8);
lean_inc_ref(v_infoState_2565_);
v_snapshotTasks_2566_ = lean_ctor_get(v___x_2555_, 9);
lean_inc_ref(v_snapshotTasks_2566_);
lean_dec(v___x_2555_);
v_asyncMode_2567_ = lean_ctor_get(v_toEnvExtension_2556_, 2);
lean_inc_ref(v_toEnvExtension_2556_);
v___x_2568_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2556_, v_env_2558_, v___f_2550_, v_asyncMode_2567_, v___x_2543_, v___x_2551_);
v___y_2503_ = v_snapshotTasks_2566_;
v___y_2504_ = v___y_2554_;
v___y_2505_ = v_auxDeclNGen_2561_;
v___y_2506_ = v_infoState_2565_;
v___y_2507_ = v_nextMacroScope_2559_;
v___y_2508_ = v_messages_2564_;
v___y_2509_ = v___y_2553_;
v___y_2510_ = v_recordedDeps_2563_;
v___y_2511_ = v_traceState_2562_;
v___y_2512_ = v_ngen_2560_;
v___y_2513_ = v___x_2568_;
goto v___jp_2502_;
}
else
{
lean_object* v_env_2569_; lean_object* v_nextMacroScope_2570_; lean_object* v_ngen_2571_; lean_object* v_auxDeclNGen_2572_; lean_object* v_traceState_2573_; lean_object* v_recordedDeps_2574_; lean_object* v_messages_2575_; lean_object* v_infoState_2576_; lean_object* v_snapshotTasks_2577_; lean_object* v_asyncMode_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_env_2569_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_env_2569_);
v_nextMacroScope_2570_ = lean_ctor_get(v___x_2555_, 1);
lean_inc(v_nextMacroScope_2570_);
v_ngen_2571_ = lean_ctor_get(v___x_2555_, 2);
lean_inc_ref(v_ngen_2571_);
v_auxDeclNGen_2572_ = lean_ctor_get(v___x_2555_, 3);
lean_inc_ref(v_auxDeclNGen_2572_);
v_traceState_2573_ = lean_ctor_get(v___x_2555_, 4);
lean_inc_ref(v_traceState_2573_);
v_recordedDeps_2574_ = lean_ctor_get(v___x_2555_, 6);
lean_inc_ref(v_recordedDeps_2574_);
v_messages_2575_ = lean_ctor_get(v___x_2555_, 7);
lean_inc_ref(v_messages_2575_);
v_infoState_2576_ = lean_ctor_get(v___x_2555_, 8);
lean_inc_ref(v_infoState_2576_);
v_snapshotTasks_2577_ = lean_ctor_get(v___x_2555_, 9);
lean_inc_ref(v_snapshotTasks_2577_);
lean_dec(v___x_2555_);
v_asyncMode_2578_ = lean_ctor_get(v_toEnvExtension_2556_, 2);
lean_inc_ref_n(v_toEnvExtension_2556_, 2);
v___x_2579_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2556_, v_env_2569_);
lean_dec_ref(v_env_2569_);
v___x_2580_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2556_, v___x_2579_, v___f_2550_, v_asyncMode_2578_, v___x_2543_, v___x_2551_);
v___y_2503_ = v_snapshotTasks_2577_;
v___y_2504_ = v___y_2554_;
v___y_2505_ = v_auxDeclNGen_2572_;
v___y_2506_ = v_infoState_2576_;
v___y_2507_ = v_nextMacroScope_2570_;
v___y_2508_ = v_messages_2575_;
v___y_2509_ = v___y_2553_;
v___y_2510_ = v_recordedDeps_2574_;
v___y_2511_ = v_traceState_2573_;
v___y_2512_ = v_ngen_2571_;
v___y_2513_ = v___x_2580_;
goto v___jp_2502_;
}
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec_ref_known(v_entry_2538_, 1);
lean_dec(v_hint_2492_);
lean_dec(v_mod_2490_);
v___x_2614_ = lean_box(0);
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
return v___x_2615_;
}
v___jp_2502_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_mctx_2518_; lean_object* v_zetaDeltaFVarIds_2519_; lean_object* v_postponed_2520_; lean_object* v_diag_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2532_; 
v___x_2514_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2);
v___x_2515_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2515_, 0, v___y_2513_);
lean_ctor_set(v___x_2515_, 1, v___y_2507_);
lean_ctor_set(v___x_2515_, 2, v___y_2512_);
lean_ctor_set(v___x_2515_, 3, v___y_2505_);
lean_ctor_set(v___x_2515_, 4, v___y_2511_);
lean_ctor_set(v___x_2515_, 5, v___x_2514_);
lean_ctor_set(v___x_2515_, 6, v___y_2510_);
lean_ctor_set(v___x_2515_, 7, v___y_2508_);
lean_ctor_set(v___x_2515_, 8, v___y_2506_);
lean_ctor_set(v___x_2515_, 9, v___y_2503_);
v___x_2516_ = lean_st_ref_put(v___y_2504_, v___x_2515_);
v___x_2517_ = lean_st_ref_take(v___y_2509_);
v_mctx_2518_ = lean_ctor_get(v___x_2517_, 0);
v_zetaDeltaFVarIds_2519_ = lean_ctor_get(v___x_2517_, 2);
v_postponed_2520_ = lean_ctor_get(v___x_2517_, 3);
v_diag_2521_ = lean_ctor_get(v___x_2517_, 4);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2517_, 1);
lean_dec(v_unused_2533_);
v___x_2523_ = v___x_2517_;
v_isShared_2524_ = v_isSharedCheck_2532_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_diag_2521_);
lean_inc(v_postponed_2520_);
lean_inc(v_zetaDeltaFVarIds_2519_);
lean_inc(v_mctx_2518_);
lean_dec(v___x_2517_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2532_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2528_; 
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 1, v___x_2526_);
v___x_2528_ = v___x_2523_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_mctx_2518_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_zetaDeltaFVarIds_2519_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_postponed_2520_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_diag_2521_);
v___x_2528_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_st_ref_put(v___y_2509_, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2525_);
return v___x_2530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2616_, lean_object* v_isMeta_2617_, lean_object* v_hint_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
uint8_t v_isMeta_boxed_2628_; lean_object* v_res_2629_; 
v_isMeta_boxed_2628_ = lean_unbox(v_isMeta_2617_);
v_res_2629_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_mod_2616_, v_isMeta_boxed_2628_, v_hint_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2630_, lean_object* v_x_2631_){
_start:
{
if (lean_obj_tag(v_x_2631_) == 0)
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_box(0);
return v___x_2632_;
}
else
{
lean_object* v_key_2633_; lean_object* v_value_2634_; lean_object* v_tail_2635_; uint8_t v___x_2636_; 
v_key_2633_ = lean_ctor_get(v_x_2631_, 0);
v_value_2634_ = lean_ctor_get(v_x_2631_, 1);
v_tail_2635_ = lean_ctor_get(v_x_2631_, 2);
v___x_2636_ = lean_name_eq(v_key_2633_, v_a_2630_);
if (v___x_2636_ == 0)
{
v_x_2631_ = v_tail_2635_;
goto _start;
}
else
{
lean_object* v___x_2638_; 
lean_inc(v_value_2634_);
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_value_2634_);
return v___x_2638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_2639_, lean_object* v_x_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2639_, v_x_2640_);
lean_dec(v_x_2640_);
lean_dec(v_a_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2642_, lean_object* v_a_2643_){
_start:
{
lean_object* v_buckets_2644_; lean_object* v___x_2645_; uint64_t v___y_2647_; 
v_buckets_2644_ = lean_ctor_get(v_m_2642_, 1);
v___x_2645_ = lean_array_get_size(v_buckets_2644_);
if (lean_obj_tag(v_a_2643_) == 0)
{
uint64_t v___x_2661_; 
v___x_2661_ = 1723ULL;
v___y_2647_ = v___x_2661_;
goto v___jp_2646_;
}
else
{
uint64_t v_hash_2662_; 
v_hash_2662_ = lean_ctor_get_uint64(v_a_2643_, sizeof(void*)*2);
v___y_2647_ = v_hash_2662_;
goto v___jp_2646_;
}
v___jp_2646_:
{
uint64_t v___x_2648_; uint64_t v___x_2649_; uint64_t v_fold_2650_; uint64_t v___x_2651_; uint64_t v___x_2652_; uint64_t v___x_2653_; size_t v___x_2654_; size_t v___x_2655_; size_t v___x_2656_; size_t v___x_2657_; size_t v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2648_ = 32ULL;
v___x_2649_ = lean_uint64_shift_right(v___y_2647_, v___x_2648_);
v_fold_2650_ = lean_uint64_xor(v___y_2647_, v___x_2649_);
v___x_2651_ = 16ULL;
v___x_2652_ = lean_uint64_shift_right(v_fold_2650_, v___x_2651_);
v___x_2653_ = lean_uint64_xor(v_fold_2650_, v___x_2652_);
v___x_2654_ = lean_uint64_to_usize(v___x_2653_);
v___x_2655_ = lean_usize_of_nat(v___x_2645_);
v___x_2656_ = ((size_t)1ULL);
v___x_2657_ = lean_usize_sub(v___x_2655_, v___x_2656_);
v___x_2658_ = lean_usize_land(v___x_2654_, v___x_2657_);
v___x_2659_ = lean_array_uget_borrowed(v_buckets_2644_, v___x_2658_);
v___x_2660_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2643_, v___x_2659_);
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_m_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object* v___x_2666_, lean_object* v_declName_2667_, lean_object* v_as_2668_, size_t v_sz_2669_, size_t v_i_2670_, lean_object* v_b_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v___x_2681_; 
v___x_2681_ = lean_usize_dec_lt(v_i_2670_, v_sz_2669_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; 
lean_dec(v_declName_2667_);
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v_b_2671_);
return v___x_2682_;
}
else
{
lean_object* v___x_2683_; lean_object* v_modules_2684_; lean_object* v___x_2685_; lean_object* v_a_2686_; lean_object* v___x_2687_; lean_object* v_toImport_2688_; lean_object* v_module_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; lean_object* v___x_2692_; 
v___x_2683_ = l_Lean_Environment_header(v___x_2666_);
v_modules_2684_ = lean_ctor_get(v___x_2683_, 3);
lean_inc_ref(v_modules_2684_);
lean_dec_ref(v___x_2683_);
v___x_2685_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2686_ = lean_array_uget_borrowed(v_as_2668_, v_i_2670_);
v___x_2687_ = lean_array_get(v___x_2685_, v_modules_2684_, v_a_2686_);
lean_dec_ref(v_modules_2684_);
v_toImport_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc_ref(v_toImport_2688_);
lean_dec(v___x_2687_);
v_module_2689_ = lean_ctor_get(v_toImport_2688_, 0);
lean_inc(v_module_2689_);
lean_dec_ref(v_toImport_2688_);
v___x_2690_ = lean_box(0);
v___x_2691_ = 0;
lean_inc(v_declName_2667_);
v___x_2692_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2689_, v___x_2691_, v_declName_2667_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
if (lean_obj_tag(v___x_2692_) == 0)
{
size_t v___x_2693_; size_t v___x_2694_; 
lean_dec_ref_known(v___x_2692_, 1);
v___x_2693_ = ((size_t)1ULL);
v___x_2694_ = lean_usize_add(v_i_2670_, v___x_2693_);
v_i_2670_ = v___x_2694_;
v_b_2671_ = v___x_2690_;
goto _start;
}
else
{
lean_dec(v_declName_2667_);
return v___x_2692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2696_, lean_object* v_declName_2697_, lean_object* v_as_2698_, lean_object* v_sz_2699_, lean_object* v_i_2700_, lean_object* v_b_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
size_t v_sz_boxed_2711_; size_t v_i_boxed_2712_; lean_object* v_res_2713_; 
v_sz_boxed_2711_ = lean_unbox_usize(v_sz_2699_);
lean_dec(v_sz_2699_);
v_i_boxed_2712_ = lean_unbox_usize(v_i_2700_);
lean_dec(v_i_2700_);
v_res_2713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v___x_2696_, v_declName_2697_, v_as_2698_, v_sz_boxed_2711_, v_i_boxed_2712_, v_b_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec_ref(v_as_2698_);
lean_dec_ref(v___x_2696_);
return v_res_2713_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Std_HashMap_instInhabited___redArg();
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object* v_declName_2717_, uint8_t v_isMeta_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v_env_2733_; lean_object* v___y_2735_; lean_object* v___x_2748_; 
v___x_2728_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0);
v___x_2729_ = lean_st_ref_get(v___y_2726_);
v_env_2733_ = lean_ctor_get(v___x_2729_, 0);
lean_inc_ref(v_env_2733_);
lean_dec(v___x_2729_);
v___x_2748_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2733_, v_declName_2717_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_dec_ref(v_env_2733_);
lean_dec(v_declName_2717_);
goto v___jp_2730_;
}
else
{
lean_object* v_val_2749_; lean_object* v___x_2750_; lean_object* v_modules_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v_val_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_val_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = l_Lean_Environment_header(v_env_2733_);
v_modules_2751_ = lean_ctor_get(v___x_2750_, 3);
lean_inc_ref(v_modules_2751_);
lean_dec_ref(v___x_2750_);
v___x_2752_ = lean_array_get_size(v_modules_2751_);
v___x_2753_ = lean_nat_dec_lt(v_val_2749_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_dec_ref(v_modules_2751_);
lean_dec(v_val_2749_);
lean_dec_ref(v_env_2733_);
lean_dec(v_declName_2717_);
goto v___jp_2730_;
}
else
{
lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___y_2757_; 
v___x_2754_ = lean_array_fget(v_modules_2751_, v_val_2749_);
lean_dec(v_val_2749_);
lean_dec_ref(v_modules_2751_);
v___x_2755_ = lean_st_ref_get(v___y_2726_);
if (v_isMeta_2718_ == 0)
{
lean_dec(v___x_2755_);
v___y_2757_ = v_isMeta_2718_;
goto v___jp_2756_;
}
else
{
lean_object* v_env_2768_; uint8_t v___x_2769_; 
v_env_2768_ = lean_ctor_get(v___x_2755_, 0);
lean_inc_ref(v_env_2768_);
lean_dec(v___x_2755_);
lean_inc(v_declName_2717_);
v___x_2769_ = l_Lean_isMarkedMeta(v_env_2768_, v_declName_2717_);
if (v___x_2769_ == 0)
{
v___y_2757_ = v_isMeta_2718_;
goto v___jp_2756_;
}
else
{
uint8_t v___x_2770_; 
v___x_2770_ = 0;
v___y_2757_ = v___x_2770_;
goto v___jp_2756_;
}
}
v___jp_2756_:
{
lean_object* v_toImport_2758_; lean_object* v_module_2759_; lean_object* v___x_2760_; 
v_toImport_2758_ = lean_ctor_get(v___x_2754_, 0);
lean_inc_ref(v_toImport_2758_);
lean_dec(v___x_2754_);
v_module_2759_ = lean_ctor_get(v_toImport_2758_, 0);
lean_inc(v_module_2759_);
lean_dec_ref(v_toImport_2758_);
lean_inc(v_declName_2717_);
v___x_2760_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2759_, v___y_2757_, v_declName_2717_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_dec_ref_known(v___x_2760_, 1);
v___x_2761_ = l_Lean_indirectModUseExt;
v___x_2762_ = lean_box(1);
v___x_2763_ = lean_box(0);
lean_inc_ref(v_env_2733_);
v___x_2764_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2728_, v___x_2761_, v_env_2733_, v___x_2762_, v___x_2763_);
v___x_2765_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v___x_2764_, v_declName_2717_);
lean_dec(v___x_2764_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1));
v___y_2735_ = v___x_2766_;
goto v___jp_2734_;
}
else
{
lean_object* v_val_2767_; 
v_val_2767_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_val_2767_);
lean_dec_ref_known(v___x_2765_, 1);
v___y_2735_ = v_val_2767_;
goto v___jp_2734_;
}
}
else
{
lean_dec_ref(v_env_2733_);
lean_dec(v_declName_2717_);
return v___x_2760_;
}
}
}
}
v___jp_2730_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_box(0);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
return v___x_2732_;
}
v___jp_2734_:
{
lean_object* v___x_2736_; size_t v_sz_2737_; size_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2736_ = lean_box(0);
v_sz_2737_ = lean_array_size(v___y_2735_);
v___x_2738_ = ((size_t)0ULL);
v___x_2739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v_env_2733_, v_declName_2717_, v___y_2735_, v_sz_2737_, v___x_2738_, v___x_2736_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec_ref(v___y_2735_);
lean_dec_ref(v_env_2733_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2746_ == 0)
{
lean_object* v_unused_2747_; 
v_unused_2747_ = lean_ctor_get(v___x_2739_, 0);
lean_dec(v_unused_2747_);
v___x_2741_ = v___x_2739_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_dec(v___x_2739_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2736_);
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2736_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
return v___x_2739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object* v_declName_2771_, lean_object* v_isMeta_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
uint8_t v_isMeta_boxed_2782_; lean_object* v_res_2783_; 
v_isMeta_boxed_2782_ = lean_unbox(v_isMeta_2772_);
v_res_2783_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_declName_2771_, v_isMeta_boxed_2782_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object* v_as_x27_2784_, lean_object* v_b_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
if (lean_obj_tag(v_as_x27_2784_) == 0)
{
lean_object* v___x_2795_; 
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_b_2785_);
return v___x_2795_;
}
else
{
lean_object* v_head_2796_; lean_object* v_tail_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; lean_object* v___x_2800_; 
v_head_2796_ = lean_ctor_get(v_as_x27_2784_, 0);
v_tail_2797_ = lean_ctor_get(v_as_x27_2784_, 1);
v___x_2798_ = lean_box(0);
v___x_2799_ = 1;
lean_inc(v_head_2796_);
v___x_2800_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_head_2796_, v___x_2799_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_dec_ref_known(v___x_2800_, 1);
v_as_x27_2784_ = v_tail_2797_;
v_b_2785_ = v___x_2798_;
goto _start;
}
else
{
return v___x_2800_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2802_, lean_object* v_b_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_2802_, v_b_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
lean_dec(v_as_x27_2802_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object* v_x_2814_, lean_object* v___y_2815_){
_start:
{
if (lean_obj_tag(v_x_2814_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v_x_2814_, 0);
lean_inc(v_a_2816_);
v___x_2817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2816_);
lean_ctor_set(v___x_2817_, 1, v___y_2815_);
return v___x_2817_;
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2819_; 
v_a_2818_ = lean_ctor_get(v_x_2814_, 0);
lean_inc(v_a_2818_);
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v_a_2818_);
lean_ctor_set(v___x_2819_, 1, v___y_2815_);
return v___x_2819_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object* v_x_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_2820_, v___y_2821_);
lean_dec_ref(v_x_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(lean_object* v_env_2823_, lean_object* v_stx_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2823_, v_stx_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
if (lean_obj_tag(v_a_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2837_; 
v_a_2829_ = lean_ctor_get(v___x_2827_, 1);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; 
v_unused_2838_ = lean_ctor_get(v___x_2827_, 0);
lean_dec(v_unused_2838_);
v___x_2831_ = v___x_2827_;
v_isShared_2832_ = v_isSharedCheck_2837_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2827_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2837_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = lean_box(0);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2833_);
v___x_2835_ = v___x_2831_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v_a_2829_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
else
{
lean_object* v_val_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2867_; 
v_val_2839_ = lean_ctor_get(v_a_2828_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v_a_2828_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2841_ = v_a_2828_;
v_isShared_2842_ = v_isSharedCheck_2867_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_val_2839_);
lean_dec(v_a_2828_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2867_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v_snd_2843_; 
v_snd_2843_ = lean_ctor_get(v_val_2839_, 1);
lean_inc(v_snd_2843_);
lean_dec(v_val_2839_);
if (lean_obj_tag(v_snd_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2853_; 
lean_del_object(v___x_2841_);
v_a_2844_ = lean_ctor_get(v___x_2827_, 1);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2827_, 2);
v_a_2845_ = lean_ctor_get(v_snd_2843_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_snd_2843_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2847_ = v_snd_2843_;
v_isShared_2848_ = v_isSharedCheck_2853_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v_snd_2843_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2853_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; 
v___x_2851_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2850_, v_a_2844_);
lean_dec_ref(v___x_2850_);
return v___x_2851_;
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2866_; 
v_a_2854_ = lean_ctor_get(v___x_2827_, 1);
lean_inc(v_a_2854_);
lean_dec_ref_known(v___x_2827_, 2);
v_a_2855_ = lean_ctor_get(v_snd_2843_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_snd_2843_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2857_ = v_snd_2843_;
v_isShared_2858_ = v_isSharedCheck_2866_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v_snd_2843_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2866_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v_a_2855_);
v___x_2860_ = v___x_2841_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
lean_object* v___x_2862_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2860_);
v___x_2862_ = v___x_2857_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2860_);
v___x_2862_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2862_, v_a_2854_);
lean_dec_ref(v___x_2862_);
return v___x_2863_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
v_a_2868_ = lean_ctor_get(v___x_2827_, 0);
v_a_2869_ = lean_ctor_get(v___x_2827_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2827_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_inc(v_a_2868_);
lean_dec(v___x_2827_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2868_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(lean_object* v_env_2877_, lean_object* v_stx_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(v_env_2877_, v_stx_2878_, v___y_2879_, v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(lean_object* v_x_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; lean_object* v_toCold_2894_; lean_object* v_env_2895_; lean_object* v_currRecDepth_2896_; lean_object* v_ref_2897_; lean_object* v_maxRecDepth_2898_; lean_object* v_currNamespace_2899_; lean_object* v_openDecls_2900_; lean_object* v_quotContext_2901_; lean_object* v_currMacroScope_2902_; lean_object* v___f_2903_; lean_object* v___f_2904_; lean_object* v___x_2905_; lean_object* v___f_2906_; lean_object* v___f_2907_; lean_object* v___f_2908_; lean_object* v_methods_2909_; lean_object* v___x_2910_; lean_object* v_nextMacroScope_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2893_ = lean_st_ref_get(v___y_2891_);
v_toCold_2894_ = lean_ctor_get(v___y_2890_, 0);
v_env_2895_ = lean_ctor_get(v___x_2893_, 0);
lean_inc_ref_n(v_env_2895_, 4);
lean_dec(v___x_2893_);
v_currRecDepth_2896_ = lean_ctor_get(v___y_2890_, 1);
v_ref_2897_ = lean_ctor_get(v___y_2890_, 2);
v_maxRecDepth_2898_ = lean_ctor_get(v_toCold_2894_, 3);
v_currNamespace_2899_ = lean_ctor_get(v_toCold_2894_, 4);
v_openDecls_2900_ = lean_ctor_get(v_toCold_2894_, 5);
v_quotContext_2901_ = lean_ctor_get(v_toCold_2894_, 8);
v_currMacroScope_2902_ = lean_ctor_get(v_toCold_2894_, 9);
v___f_2903_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2903_, 0, v_env_2895_);
v___f_2904_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2904_, 0, v_env_2895_);
v___x_2905_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2890_);
lean_inc_n(v_currNamespace_2899_, 3);
v___f_2906_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v___f_2906_, 0, v_currNamespace_2899_);
lean_inc_n(v_openDecls_2900_, 2);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed), 7, 4);
lean_closure_set(v___f_2907_, 0, v_env_2895_);
lean_closure_set(v___f_2907_, 1, v___x_2905_);
lean_closure_set(v___f_2907_, 2, v_currNamespace_2899_);
lean_closure_set(v___f_2907_, 3, v_openDecls_2900_);
v___f_2908_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed), 6, 3);
lean_closure_set(v___f_2908_, 0, v_env_2895_);
lean_closure_set(v___f_2908_, 1, v_currNamespace_2899_);
lean_closure_set(v___f_2908_, 2, v_openDecls_2900_);
v_methods_2909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2909_, 0, v___f_2904_);
lean_ctor_set(v_methods_2909_, 1, v___f_2906_);
lean_ctor_set(v_methods_2909_, 2, v___f_2903_);
lean_ctor_set(v_methods_2909_, 3, v___f_2908_);
lean_ctor_set(v_methods_2909_, 4, v___f_2907_);
v___x_2910_ = lean_st_ref_get(v___y_2891_);
v_nextMacroScope_2911_ = lean_ctor_get(v___x_2910_, 1);
lean_inc(v_nextMacroScope_2911_);
lean_dec(v___x_2910_);
lean_inc(v_ref_2897_);
lean_inc(v_maxRecDepth_2898_);
lean_inc(v_currRecDepth_2896_);
lean_inc(v_currMacroScope_2902_);
lean_inc(v_quotContext_2901_);
v___x_2912_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2912_, 0, v_methods_2909_);
lean_ctor_set(v___x_2912_, 1, v_quotContext_2901_);
lean_ctor_set(v___x_2912_, 2, v_currMacroScope_2902_);
lean_ctor_set(v___x_2912_, 3, v_currRecDepth_2896_);
lean_ctor_set(v___x_2912_, 4, v_maxRecDepth_2898_);
lean_ctor_set(v___x_2912_, 5, v_ref_2897_);
v___x_2913_ = lean_box(0);
v___x_2914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2914_, 0, v_nextMacroScope_2911_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
lean_ctor_set(v___x_2914_, 2, v___x_2913_);
v___x_2915_ = lean_apply_2(v_x_2883_, v___x_2912_, v___x_2914_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v_a_2917_; lean_object* v_macroScope_2918_; lean_object* v_traceMsgs_2919_; lean_object* v_expandedMacroDecls_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 1);
lean_inc(v_a_2916_);
v_a_2917_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2915_, 2);
v_macroScope_2918_ = lean_ctor_get(v_a_2916_, 0);
lean_inc(v_macroScope_2918_);
v_traceMsgs_2919_ = lean_ctor_get(v_a_2916_, 1);
lean_inc(v_traceMsgs_2919_);
v_expandedMacroDecls_2920_ = lean_ctor_get(v_a_2916_, 2);
lean_inc(v_expandedMacroDecls_2920_);
lean_dec(v_a_2916_);
v___x_2921_ = lean_box(0);
v___x_2922_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_expandedMacroDecls_2920_, v___x_2921_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v_expandedMacroDecls_2920_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2923_; lean_object* v_env_2924_; lean_object* v_ngen_2925_; lean_object* v_auxDeclNGen_2926_; lean_object* v_traceState_2927_; lean_object* v_cache_2928_; lean_object* v_recordedDeps_2929_; lean_object* v_messages_2930_; lean_object* v_infoState_2931_; lean_object* v_snapshotTasks_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2958_; 
lean_dec_ref_known(v___x_2922_, 1);
v___x_2923_ = lean_st_ref_take(v___y_2891_);
v_env_2924_ = lean_ctor_get(v___x_2923_, 0);
v_ngen_2925_ = lean_ctor_get(v___x_2923_, 2);
v_auxDeclNGen_2926_ = lean_ctor_get(v___x_2923_, 3);
v_traceState_2927_ = lean_ctor_get(v___x_2923_, 4);
v_cache_2928_ = lean_ctor_get(v___x_2923_, 5);
v_recordedDeps_2929_ = lean_ctor_get(v___x_2923_, 6);
v_messages_2930_ = lean_ctor_get(v___x_2923_, 7);
v_infoState_2931_ = lean_ctor_get(v___x_2923_, 8);
v_snapshotTasks_2932_ = lean_ctor_get(v___x_2923_, 9);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; 
v_unused_2959_ = lean_ctor_get(v___x_2923_, 1);
lean_dec(v_unused_2959_);
v___x_2934_ = v___x_2923_;
v_isShared_2935_ = v_isSharedCheck_2958_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_snapshotTasks_2932_);
lean_inc(v_infoState_2931_);
lean_inc(v_messages_2930_);
lean_inc(v_recordedDeps_2929_);
lean_inc(v_cache_2928_);
lean_inc(v_traceState_2927_);
lean_inc(v_auxDeclNGen_2926_);
lean_inc(v_ngen_2925_);
lean_inc(v_env_2924_);
lean_dec(v___x_2923_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2958_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 1, v_macroScope_2918_);
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_env_2924_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_macroScope_2918_);
lean_ctor_set(v_reuseFailAlloc_2957_, 2, v_ngen_2925_);
lean_ctor_set(v_reuseFailAlloc_2957_, 3, v_auxDeclNGen_2926_);
lean_ctor_set(v_reuseFailAlloc_2957_, 4, v_traceState_2927_);
lean_ctor_set(v_reuseFailAlloc_2957_, 5, v_cache_2928_);
lean_ctor_set(v_reuseFailAlloc_2957_, 6, v_recordedDeps_2929_);
lean_ctor_set(v_reuseFailAlloc_2957_, 7, v_messages_2930_);
lean_ctor_set(v_reuseFailAlloc_2957_, 8, v_infoState_2931_);
lean_ctor_set(v_reuseFailAlloc_2957_, 9, v_snapshotTasks_2932_);
v___x_2937_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2938_ = lean_st_ref_put(v___y_2891_, v___x_2937_);
v___x_2939_ = l_List_reverse___redArg(v_traceMsgs_2919_);
v___x_2940_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v___x_2939_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2947_ == 0)
{
lean_object* v_unused_2948_; 
v_unused_2948_ = lean_ctor_get(v___x_2940_, 0);
lean_dec(v_unused_2948_);
v___x_2942_ = v___x_2940_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_dec(v___x_2940_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v_a_2917_);
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2917_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec(v_a_2917_);
v_a_2949_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2940_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2940_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec(v_traceMsgs_2919_);
lean_dec(v_macroScope_2918_);
lean_dec(v_a_2917_);
v_a_2960_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2922_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2922_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_2968_; 
v_a_2968_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2915_, 2);
if (lean_obj_tag(v_a_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v_a_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_a_2969_ = lean_ctor_get(v_a_2968_, 0);
lean_inc(v_a_2969_);
v_a_2970_ = lean_ctor_get(v_a_2968_, 1);
lean_inc_ref(v_a_2970_);
lean_dec_ref_known(v_a_2968_, 2);
v___x_2971_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0));
v___x_2972_ = lean_string_dec_eq(v_a_2970_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2973_, 0, v_a_2970_);
v___x_2974_ = l_Lean_MessageData_ofFormat(v___x_2973_);
v___x_2975_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_a_2969_, v___x_2974_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v_a_2969_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; 
lean_dec_ref(v_a_2970_);
v___x_2976_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_a_2969_);
return v___x_2976_;
}
}
else
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(lean_object* v_x_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object* v_x_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v___x_3009_; uint8_t v___x_3010_; 
v___x_3009_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
lean_inc(v_x_2999_);
v___x_3010_ = l_Lean_Syntax_isOfKind(v_x_2999_, v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; 
lean_dec(v_x_2999_);
v___x_3011_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; lean_object* v_hyp_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3012_ = lean_unsigned_to_nat(1u);
v_hyp_3013_ = l_Lean_Syntax_getArg(v_x_2999_, v___x_3012_);
v___x_3014_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4));
lean_inc(v_hyp_3013_);
v___x_3015_ = l_Lean_Syntax_isOfKind(v_hyp_3013_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; 
lean_dec(v_hyp_3013_);
lean_dec(v_x_2999_);
v___x_3016_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_3016_;
}
else
{
lean_object* v___x_3017_; lean_object* v_pat_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3017_ = lean_unsigned_to_nat(3u);
v_pat_3018_ = l_Lean_Syntax_getArg(v_x_2999_, v___x_3017_);
lean_dec(v_x_2999_);
v___x_3019_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MCasesPat_parse___boxed), 3, 1);
lean_closure_set(v___x_3019_, 0, v_pat_3018_);
v___x_3020_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v___x_3019_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_3001_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v_fst_3024_; lean_object* v_snd_3025_; lean_object* v___f_3026_; lean_object* v___x_3027_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v_fst_3024_ = lean_ctor_get(v_a_3023_, 0);
lean_inc_n(v_fst_3024_, 2);
v_snd_3025_ = lean_ctor_get(v_a_3023_, 1);
lean_inc(v_snd_3025_);
lean_dec(v_a_3023_);
v___f_3026_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed), 13, 4);
lean_closure_set(v___f_3026_, 0, v_snd_3025_);
lean_closure_set(v___f_3026_, 1, v_hyp_3013_);
lean_closure_set(v___f_3026_, 2, v_a_3021_);
lean_closure_set(v___f_3026_, 3, v_fst_3024_);
v___x_3027_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_fst_3024_, v___f_3026_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
return v___x_3027_;
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_a_3021_);
lean_dec(v_hyp_3013_);
v_a_3028_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3022_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3022_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_hyp_3013_);
v_a_3036_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3020_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3020_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object* v_x_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(v_x_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_);
lean_dec(v_a_3052_);
lean_dec_ref(v_a_3051_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object* v_00_u03b1_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_3056_, v___y_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3060_, lean_object* v_x_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(v_00_u03b1_3060_, v_x_3061_, v___y_3062_, v___y_3063_);
lean_dec_ref(v___y_3062_);
lean_dec_ref(v_x_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object* v_00_u03b1_3065_, lean_object* v_ref_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_3066_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3077_, lean_object* v_ref_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(v_00_u03b1_3077_, v_ref_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object* v_00_u03b1_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___x_3100_; 
v___x_3100_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object* v_00_u03b1_3101_, lean_object* v_x_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(v_00_u03b1_3101_, v_x_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
return v_res_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object* v_mvarId_3113_, lean_object* v_val_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_3113_, v_val_3114_, v___y_3120_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object* v_mvarId_3125_, lean_object* v_val_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(v_mvarId_3125_, v_val_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object* v_cls_3137_, lean_object* v_msg_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_3137_, v_msg_3138_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object* v_cls_3149_, lean_object* v_msg_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_res_3160_; 
v_res_3160_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_3149_, v_msg_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object* v_as_3161_, lean_object* v_as_x27_3162_, lean_object* v_b_3163_, lean_object* v_a_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; 
v___x_3174_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_3162_, v_b_3163_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object* v_as_3175_, lean_object* v_as_x27_3176_, lean_object* v_b_3177_, lean_object* v_a_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_as_3175_, v_as_x27_3176_, v_b_3177_, v_a_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec(v_as_x27_3176_);
lean_dec(v_as_3175_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object* v_00_u03b1_3189_, lean_object* v_ref_3190_, lean_object* v_msg_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_3190_, v_msg_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3202_, lean_object* v_ref_3203_, lean_object* v_msg_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v_00_u03b1_3202_, v_ref_3203_, v_msg_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v_ref_3203_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(lean_object* v_00_u03b2_3215_, lean_object* v_x_3216_, lean_object* v_x_3217_, lean_object* v_x_3218_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_x_3216_, v_x_3217_, v_x_3218_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3220_, lean_object* v_m_3221_, lean_object* v_a_3222_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_3221_, v_a_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3224_, lean_object* v_m_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(v_00_u03b2_3224_, v_m_3225_, v_a_3226_);
lean_dec(v_a_3226_);
lean_dec_ref(v_m_3225_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_3228_, lean_object* v_msg_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_3229_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_3240_, lean_object* v_msg_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(v_00_u03b1_3240_, v_msg_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(lean_object* v_00_u03b2_3252_, lean_object* v_x_3253_, size_t v_x_3254_, size_t v_x_3255_, lean_object* v_x_3256_, lean_object* v_x_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_3253_, v_x_3254_, v_x_3255_, v_x_3256_, v_x_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(lean_object* v_00_u03b2_3259_, lean_object* v_x_3260_, lean_object* v_x_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_, lean_object* v_x_3264_){
_start:
{
size_t v_x_21646__boxed_3265_; size_t v_x_21647__boxed_3266_; lean_object* v_res_3267_; 
v_x_21646__boxed_3265_ = lean_unbox_usize(v_x_3261_);
lean_dec(v_x_3261_);
v_x_21647__boxed_3266_ = lean_unbox_usize(v_x_3262_);
lean_dec(v_x_3262_);
v_res_3267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(v_00_u03b2_3259_, v_x_3260_, v_x_21646__boxed_3265_, v_x_21647__boxed_3266_, v_x_3263_, v_x_3264_);
return v_res_3267_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
uint8_t v___x_3271_; 
v___x_3271_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_3269_, v_x_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3272_, lean_object* v_x_3273_, lean_object* v_x_3274_){
_start:
{
uint8_t v_res_3275_; lean_object* v_r_3276_; 
v_res_3275_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(v_00_u03b2_3272_, v_x_3273_, v_x_3274_);
lean_dec_ref(v_x_3274_);
lean_dec_ref(v_x_3273_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3277_, lean_object* v_a_3278_, lean_object* v_x_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_3278_, v_x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3281_, lean_object* v_a_3282_, lean_object* v_x_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(v_00_u03b2_3281_, v_a_3282_, v_x_3283_);
lean_dec(v_x_3283_);
lean_dec(v_a_3282_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_3285_, lean_object* v_n_3286_, lean_object* v_k_3287_, lean_object* v_v_3288_){
_start:
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v_n_3286_, v_k_3287_, v_v_3288_);
return v___x_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_3290_, size_t v_depth_3291_, lean_object* v_keys_3292_, lean_object* v_vals_3293_, lean_object* v_heq_3294_, lean_object* v_i_3295_, lean_object* v_entries_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_3291_, v_keys_3292_, v_vals_3293_, v_i_3295_, v_entries_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3298_, lean_object* v_depth_3299_, lean_object* v_keys_3300_, lean_object* v_vals_3301_, lean_object* v_heq_3302_, lean_object* v_i_3303_, lean_object* v_entries_3304_){
_start:
{
size_t v_depth_boxed_3305_; lean_object* v_res_3306_; 
v_depth_boxed_3305_ = lean_unbox_usize(v_depth_3299_);
lean_dec(v_depth_3299_);
v_res_3306_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(v_00_u03b2_3298_, v_depth_boxed_3305_, v_keys_3300_, v_vals_3301_, v_heq_3302_, v_i_3303_, v_entries_3304_);
lean_dec_ref(v_vals_3301_);
lean_dec_ref(v_keys_3300_);
return v_res_3306_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_3307_, lean_object* v_x_3308_, size_t v_x_3309_, lean_object* v_x_3310_){
_start:
{
uint8_t v___x_3311_; 
v___x_3311_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_3308_, v_x_3309_, v_x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(lean_object* v_00_u03b2_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_){
_start:
{
size_t v_x_21680__boxed_3316_; uint8_t v_res_3317_; lean_object* v_r_3318_; 
v_x_21680__boxed_3316_ = lean_unbox_usize(v_x_3314_);
lean_dec(v_x_3314_);
v_res_3317_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(v_00_u03b2_3312_, v_x_3313_, v_x_21680__boxed_3316_, v_x_3315_);
lean_dec_ref(v_x_3315_);
lean_dec_ref(v_x_3313_);
v_r_3318_ = lean_box(v_res_3317_);
return v_r_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(lean_object* v_00_u03b2_3319_, lean_object* v_x_3320_, lean_object* v_x_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_){
_start:
{
lean_object* v___x_3324_; 
v___x_3324_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_x_3320_, v_x_3321_, v_x_3322_, v_x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object* v_00_u03b2_3325_, lean_object* v_keys_3326_, lean_object* v_vals_3327_, lean_object* v_heq_3328_, lean_object* v_i_3329_, lean_object* v_k_3330_){
_start:
{
uint8_t v___x_3331_; 
v___x_3331_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_3326_, v_i_3329_, v_k_3330_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3332_, lean_object* v_keys_3333_, lean_object* v_vals_3334_, lean_object* v_heq_3335_, lean_object* v_i_3336_, lean_object* v_k_3337_){
_start:
{
uint8_t v_res_3338_; lean_object* v_r_3339_; 
v_res_3338_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(v_00_u03b2_3332_, v_keys_3333_, v_vals_3334_, v_heq_3335_, v_i_3336_, v_k_3337_);
lean_dec_ref(v_k_3337_);
lean_dec_ref(v_vals_3334_);
lean_dec_ref(v_keys_3333_);
v_r_3339_ = lean_box(v_res_3338_);
return v_r_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1(){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3349_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3350_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
v___x_3351_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1));
v___x_3352_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed), 10, 0);
v___x_3353_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3349_, v___x_3350_, v___x_3351_, v___x_3352_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object* v_a_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
return v_res_3355_;
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
