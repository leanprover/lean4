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
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_2308__boxed_543_; lean_object* v_res_544_; 
v___x_2308__boxed_543_ = lean_unbox(v___x_529_);
v_res_544_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0(v___x_526_, v_snd_527_, v_k_528_, v___x_2308__boxed_543_, v___x_530_, v___x_531_, v___x_532_, v___x_533_, v___x_534_, v___x_535_, v_H_536_, v_x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
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
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_632_, v_a_636_, v_a_637_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___f_661_; lean_object* v___x_662_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v_fst_653_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_fst_653_);
v_snd_654_ = lean_ctor_get(v_a_652_, 1);
lean_inc(v_snd_654_);
lean_dec(v_a_652_);
v___x_655_ = l_Lean_Expr_appFn_x21(v___x_639_);
v___x_656_ = l_Lean_Expr_appFn_x21(v___x_655_);
v___x_657_ = l_Lean_Expr_appArg_x21(v___x_656_);
lean_dec_ref(v___x_656_);
v___x_658_ = l_Lean_Expr_appArg_x21(v___x_655_);
lean_dec_ref(v___x_655_);
v___x_659_ = l_Lean_Expr_appArg_x21(v___x_639_);
lean_dec_ref(v___x_639_);
v___x_660_ = lean_box(v___x_646_);
lean_inc_ref(v___x_657_);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___lam__0___boxed), 17, 11);
lean_closure_set(v___f_661_, 0, v___x_657_);
lean_closure_set(v___f_661_, 1, v_snd_654_);
lean_closure_set(v___f_661_, 2, v_k_633_);
lean_closure_set(v___f_661_, 3, v___x_660_);
lean_closure_set(v___f_661_, 4, v___x_640_);
lean_closure_set(v___f_661_, 5, v___x_641_);
lean_closure_set(v___f_661_, 6, v___x_642_);
lean_closure_set(v___f_661_, 7, v___x_643_);
lean_closure_set(v___f_661_, 8, v___x_658_);
lean_closure_set(v___f_661_, 9, v___x_659_);
lean_closure_set(v___f_661_, 10, v_H_631_);
v___x_662_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_653_, v___x_657_, v___f_661_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
return v___x_662_;
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v___x_639_);
lean_dec_ref(v_k_633_);
lean_dec_ref(v_H_631_);
v_a_663_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_651_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_651_);
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
lean_object* v___x_770_; lean_object* v_ngen_771_; lean_object* v_namePrefix_772_; lean_object* v_idx_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_802_; 
v___x_770_ = lean_st_ref_get(v___y_768_);
v_ngen_771_ = lean_ctor_get(v___x_770_, 2);
lean_inc_ref(v_ngen_771_);
lean_dec(v___x_770_);
v_namePrefix_772_ = lean_ctor_get(v_ngen_771_, 0);
v_idx_773_ = lean_ctor_get(v_ngen_771_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_ngen_771_);
if (v_isSharedCheck_802_ == 0)
{
v___x_775_ = v_ngen_771_;
v_isShared_776_ = v_isSharedCheck_802_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_idx_773_);
lean_inc(v_namePrefix_772_);
lean_dec(v_ngen_771_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_802_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v_env_778_; lean_object* v_nextMacroScope_779_; lean_object* v_auxDeclNGen_780_; lean_object* v_traceState_781_; lean_object* v_cache_782_; lean_object* v_messages_783_; lean_object* v_infoState_784_; lean_object* v_snapshotTasks_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_800_; 
v___x_777_ = lean_st_ref_take(v___y_768_);
v_env_778_ = lean_ctor_get(v___x_777_, 0);
v_nextMacroScope_779_ = lean_ctor_get(v___x_777_, 1);
v_auxDeclNGen_780_ = lean_ctor_get(v___x_777_, 3);
v_traceState_781_ = lean_ctor_get(v___x_777_, 4);
v_cache_782_ = lean_ctor_get(v___x_777_, 5);
v_messages_783_ = lean_ctor_get(v___x_777_, 6);
v_infoState_784_ = lean_ctor_get(v___x_777_, 7);
v_snapshotTasks_785_ = lean_ctor_get(v___x_777_, 8);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_777_, 2);
lean_dec(v_unused_801_);
v___x_787_ = v___x_777_;
v_isShared_788_ = v_isSharedCheck_800_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snapshotTasks_785_);
lean_inc(v_infoState_784_);
lean_inc(v_messages_783_);
lean_inc(v_cache_782_);
lean_inc(v_traceState_781_);
lean_inc(v_auxDeclNGen_780_);
lean_inc(v_nextMacroScope_779_);
lean_inc(v_env_778_);
lean_dec(v___x_777_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_800_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_r_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
lean_inc(v_idx_773_);
lean_inc(v_namePrefix_772_);
v_r_789_ = l_Lean_Name_num___override(v_namePrefix_772_, v_idx_773_);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_add(v_idx_773_, v___x_790_);
lean_dec(v_idx_773_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_791_);
v___x_793_ = v___x_775_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_namePrefix_772_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_799_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 2, v___x_793_);
v___x_795_ = v___x_787_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_env_778_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_nextMacroScope_779_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_auxDeclNGen_780_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_traceState_781_);
lean_ctor_set(v_reuseFailAlloc_798_, 5, v_cache_782_);
lean_ctor_set(v_reuseFailAlloc_798_, 6, v_messages_783_);
lean_ctor_set(v_reuseFailAlloc_798_, 7, v_infoState_784_);
lean_ctor_set(v_reuseFailAlloc_798_, 8, v_snapshotTasks_785_);
v___x_795_ = v_reuseFailAlloc_798_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_st_ref_put(v___y_768_, v___x_795_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v_r_789_);
return v___x_797_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg___boxed(lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_803_);
lean_dec(v___y_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v___y_809_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___boxed(lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2(v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(lean_object* v_u_826_, lean_object* v_00_u03c3s_827_, lean_object* v_H_u2081_x27_828_, lean_object* v_k_829_, lean_object* v_H_u2082_x27_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_836_; lean_object* v_fst_837_; lean_object* v_snd_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_916_; 
lean_inc_ref(v_H_u2082_x27_830_);
lean_inc_ref(v_H_u2081_x27_828_);
lean_inc_ref(v_00_u03c3s_827_);
lean_inc(v_u_826_);
v___x_836_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(v_u_826_, v_00_u03c3s_827_, v_H_u2081_x27_828_, v_H_u2082_x27_830_);
v_fst_837_ = lean_ctor_get(v___x_836_, 0);
v_snd_838_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_916_ == 0)
{
v___x_840_ = v___x_836_;
v_isShared_841_ = v_isSharedCheck_916_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_snd_838_);
lean_inc(v_fst_837_);
lean_dec(v___x_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_916_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; 
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v_fst_837_);
v___x_842_ = lean_apply_6(v_k_829_, v_fst_837_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, lean_box(0));
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v_snd_844_; lean_object* v_fst_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_907_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v_snd_844_ = lean_ctor_get(v_a_843_, 1);
v_fst_845_ = lean_ctor_get(v_a_843_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_843_);
if (v_isSharedCheck_907_ == 0)
{
v___x_847_ = v_a_843_;
v_isShared_848_ = v_isSharedCheck_907_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snd_844_);
lean_inc(v_fst_845_);
lean_dec(v_a_843_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_907_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_906_; 
v_fst_849_ = lean_ctor_get(v_snd_844_, 0);
v_snd_850_ = lean_ctor_get(v_snd_844_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_snd_844_);
if (v_isSharedCheck_906_ == 0)
{
v___x_852_ = v_snd_844_;
v_isShared_853_ = v_isSharedCheck_906_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_snd_850_);
lean_inc(v_fst_849_);
lean_dec(v_snd_844_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_906_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; 
lean_inc(v_fst_849_);
v___x_854_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_849_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_897_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_897_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_897_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_897_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_fst_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_895_; 
v_fst_859_ = lean_ctor_get(v_a_855_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_855_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_a_855_, 1);
lean_dec(v_unused_896_);
v___x_861_ = v_a_855_;
v_isShared_862_ = v_isSharedCheck_895_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_fst_859_);
lean_dec(v_a_855_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_895_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_u_863_; lean_object* v_00_u03c3s_864_; lean_object* v_target_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_893_; 
v_u_863_ = lean_ctor_get(v_fst_849_, 0);
v_00_u03c3s_864_ = lean_ctor_get(v_fst_849_, 1);
v_target_865_ = lean_ctor_get(v_fst_849_, 3);
v_isSharedCheck_893_ = !lean_is_exclusive(v_fst_849_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v_fst_849_, 2);
lean_dec(v_unused_894_);
v___x_867_ = v_fst_849_;
v_isShared_868_ = v_isSharedCheck_893_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_target_865_);
lean_inc(v_00_u03c3s_864_);
lean_inc(v_u_863_);
lean_dec(v_fst_849_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_893_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___closed__1));
v___x_870_ = lean_box(0);
lean_inc(v_u_826_);
if (v_isShared_841_ == 0)
{
lean_ctor_set_tag(v___x_840_, 1);
lean_ctor_set(v___x_840_, 1, v___x_870_);
lean_ctor_set(v___x_840_, 0, v_u_826_);
v___x_872_ = v___x_840_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_u_826_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_870_);
v___x_872_ = v_reuseFailAlloc_892_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_873_ = l_Lean_mkConst(v___x_869_, v___x_872_);
lean_inc_ref(v_target_865_);
lean_inc_ref(v_H_u2082_x27_830_);
lean_inc_ref(v_H_u2081_x27_828_);
lean_inc_n(v_fst_859_, 2);
lean_inc_ref_n(v_00_u03c3s_827_, 2);
v___x_874_ = l_Lean_mkApp8(v___x_873_, v_00_u03c3s_827_, v_fst_859_, v_H_u2081_x27_828_, v_H_u2082_x27_830_, v_fst_837_, v_target_865_, v_snd_838_, v_snd_850_);
lean_inc(v_u_826_);
v___x_875_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_826_, v_00_u03c3s_827_, v_fst_859_, v_H_u2081_x27_828_);
v___x_876_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_826_, v_00_u03c3s_827_, v___x_875_, v_H_u2082_x27_830_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 2, v___x_876_);
v___x_878_ = v___x_867_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_u_863_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_00_u03c3s_864_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_891_, 3, v_target_865_);
v___x_878_ = v_reuseFailAlloc_891_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v_fst_859_);
lean_ctor_set(v___x_861_, 0, v_fst_845_);
v___x_880_ = v___x_861_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_fst_845_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v_fst_859_);
v___x_880_ = v_reuseFailAlloc_890_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_874_);
lean_ctor_set(v___x_852_, 0, v___x_878_);
v___x_882_ = v___x_852_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_874_);
v___x_882_ = v_reuseFailAlloc_889_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_882_);
lean_ctor_set(v___x_847_, 0, v___x_880_);
v___x_884_ = v___x_847_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_882_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_884_);
v___x_886_ = v___x_857_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
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
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_852_);
lean_dec(v_snd_850_);
lean_dec(v_fst_849_);
lean_del_object(v___x_847_);
lean_dec(v_fst_845_);
lean_del_object(v___x_840_);
lean_dec(v_snd_838_);
lean_dec(v_fst_837_);
lean_dec_ref(v_H_u2082_x27_830_);
lean_dec_ref(v_H_u2081_x27_828_);
lean_dec_ref(v_00_u03c3s_827_);
lean_dec(v_u_826_);
v_a_898_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_854_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_854_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_del_object(v___x_840_);
lean_dec(v_snd_838_);
lean_dec(v_fst_837_);
lean_dec_ref(v_H_u2082_x27_830_);
lean_dec_ref(v_H_u2081_x27_828_);
lean_dec_ref(v_00_u03c3s_827_);
lean_dec(v_u_826_);
v_a_908_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_842_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_842_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed(lean_object* v_u_917_, lean_object* v_00_u03c3s_918_, lean_object* v_H_u2081_x27_919_, lean_object* v_k_920_, lean_object* v_H_u2082_x27_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0(v_u_917_, v_00_u03c3s_918_, v_H_u2081_x27_919_, v_k_920_, v_H_u2082_x27_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(lean_object* v_a_930_, lean_object* v_snd_931_, lean_object* v_k_932_, lean_object* v___x_933_, lean_object* v___x_934_, lean_object* v___x_935_, lean_object* v___x_936_, lean_object* v___x_937_, lean_object* v_00_u03c3s_938_, lean_object* v_hyp_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_h_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_lctx_948_; lean_object* v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; 
v_lctx_948_ = lean_ctor_get(v___y_943_, 2);
lean_inc_ref(v_a_930_);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v_a_930_);
v___x_950_ = 0;
lean_inc_ref(v_h_942_);
lean_inc_ref(v_lctx_948_);
v___x_951_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(v_snd_931_, v_lctx_948_, v_h_942_, v___x_949_, v___x_950_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v___x_952_; 
lean_dec_ref_known(v___x_951_, 1);
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
lean_inc_ref(v_h_942_);
lean_inc_ref(v_a_930_);
v___x_952_ = lean_apply_7(v_k_932_, v_a_930_, v_h_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, lean_box(0));
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v_snd_954_; lean_object* v_fst_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1010_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v_snd_954_ = lean_ctor_get(v_a_953_, 1);
v_fst_955_ = lean_ctor_get(v_a_953_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_a_953_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_957_ = v_a_953_;
v_isShared_958_ = v_isSharedCheck_1010_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_snd_954_);
lean_inc(v_fst_955_);
lean_dec(v_a_953_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1010_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_1009_; 
v_fst_959_ = lean_ctor_get(v_snd_954_, 0);
v_snd_960_ = lean_ctor_get(v_snd_954_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_snd_954_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_962_ = v_snd_954_;
v_isShared_963_ = v_isSharedCheck_1009_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_snd_960_);
lean_inc(v_fst_959_);
lean_dec(v_snd_954_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_1009_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; uint8_t v___x_968_; lean_object* v___x_969_; 
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_mk_empty_array_with_capacity(v___x_964_);
v___x_966_ = lean_array_push(v___x_965_, v_h_942_);
v___x_967_ = 1;
v___x_968_ = 1;
v___x_969_ = l_Lean_Meta_mkLambdaFVars(v___x_966_, v_snd_960_, v___x_950_, v___x_967_, v___x_950_, v___x_967_, v___x_968_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec_ref(v___x_966_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1000_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_u_974_; lean_object* v_00_u03c3s_975_; lean_object* v_hyps_976_; lean_object* v_target_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_999_; 
v_u_974_ = lean_ctor_get(v_fst_959_, 0);
v_00_u03c3s_975_ = lean_ctor_get(v_fst_959_, 1);
v_hyps_976_ = lean_ctor_get(v_fst_959_, 2);
v_target_977_ = lean_ctor_get(v_fst_959_, 3);
v_isSharedCheck_999_ = !lean_is_exclusive(v_fst_959_);
if (v_isSharedCheck_999_ == 0)
{
v___x_979_ = v_fst_959_;
v_isShared_980_ = v_isSharedCheck_999_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_target_977_);
lean_inc(v_hyps_976_);
lean_inc(v_00_u03c3s_975_);
lean_inc(v_u_974_);
lean_dec(v_fst_959_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_999_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_prf_985_; lean_object* v___x_986_; lean_object* v_goal_988_; 
v___x_981_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__0));
v___x_982_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___closed__1));
v___x_983_ = l_Lean_Name_mkStr6(v___x_933_, v___x_934_, v___x_935_, v___x_936_, v___x_981_, v___x_982_);
v___x_984_ = l_Lean_mkConst(v___x_983_, v___x_937_);
lean_inc_ref(v_target_977_);
lean_inc_ref(v_hyp_939_);
lean_inc_ref(v_hyps_976_);
lean_inc_ref(v_00_u03c3s_938_);
v_prf_985_ = l_Lean_mkApp7(v___x_984_, v_00_u03c3s_938_, v_hyps_976_, v_hyp_939_, v_target_977_, v_a_930_, v_a_940_, v_a_970_);
v___x_986_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_a_941_, v_00_u03c3s_938_, v_hyps_976_, v_hyp_939_);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 2, v___x_986_);
v_goal_988_ = v___x_979_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_u_974_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_00_u03c3s_975_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_target_977_);
v_goal_988_ = v_reuseFailAlloc_998_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v_prf_985_);
lean_ctor_set(v___x_962_, 0, v_goal_988_);
v___x_990_ = v___x_962_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_goal_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_prf_985_);
v___x_990_ = v_reuseFailAlloc_997_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_990_);
v___x_992_ = v___x_957_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_fst_955_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_990_);
v___x_992_ = v_reuseFailAlloc_996_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_994_; 
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_992_);
v___x_994_ = v___x_972_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_del_object(v___x_962_);
lean_dec(v_fst_959_);
lean_del_object(v___x_957_);
lean_dec(v_fst_955_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_hyp_939_);
lean_dec_ref(v_00_u03c3s_938_);
lean_dec(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v_a_930_);
v_a_1001_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_969_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_969_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_hyp_939_);
lean_dec_ref(v_00_u03c3s_938_);
lean_dec(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v_a_930_);
return v___x_952_;
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v_h_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec_ref(v_hyp_939_);
lean_dec_ref(v_00_u03c3s_938_);
lean_dec(v___x_937_);
lean_dec_ref(v___x_936_);
lean_dec_ref(v___x_935_);
lean_dec_ref(v___x_934_);
lean_dec_ref(v___x_933_);
lean_dec_ref(v_k_932_);
lean_dec_ref(v_a_930_);
v_a_1011_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_951_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_951_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_a_1019_ = _args[0];
lean_object* v_snd_1020_ = _args[1];
lean_object* v_k_1021_ = _args[2];
lean_object* v___x_1022_ = _args[3];
lean_object* v___x_1023_ = _args[4];
lean_object* v___x_1024_ = _args[5];
lean_object* v___x_1025_ = _args[6];
lean_object* v___x_1026_ = _args[7];
lean_object* v_00_u03c3s_1027_ = _args[8];
lean_object* v_hyp_1028_ = _args[9];
lean_object* v_a_1029_ = _args[10];
lean_object* v_a_1030_ = _args[11];
lean_object* v_h_1031_ = _args[12];
lean_object* v___y_1032_ = _args[13];
lean_object* v___y_1033_ = _args[14];
lean_object* v___y_1034_ = _args[15];
lean_object* v___y_1035_ = _args[16];
lean_object* v___y_1036_ = _args[17];
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0(v_a_1019_, v_snd_1020_, v_k_1021_, v___x_1022_, v___x_1023_, v___x_1024_, v___x_1025_, v___x_1026_, v_00_u03c3s_1027_, v_hyp_1028_, v_a_1029_, v_a_1030_, v_h_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = l_Lean_mkSort(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__0);
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(lean_object* v_00_u03c3s_1049_, lean_object* v_hyp_1050_, lean_object* v_name_1051_, lean_object* v_k_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Meta_mkFreshLevelMVar(v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1061_ = 0;
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_Meta_mkFreshExprMVar(v___x_1060_, v___x_1061_, v___x_1062_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc_n(v_a_1064_, 2);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__0));
v___x_1066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__2_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd___closed__1));
v___x_1068_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_initFn___closed__1_00___x40_Lean_Elab_Tactic_Do_ProofMode_Cases_723085142____hygCtx___hyg_2_));
v___x_1069_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1070_ = lean_box(0);
lean_inc(v_a_1059_);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v_a_1059_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
lean_inc_ref(v___x_1071_);
v___x_1072_ = l_Lean_mkConst(v___x_1069_, v___x_1071_);
lean_inc_ref(v_hyp_1050_);
lean_inc_ref(v_00_u03c3s_1049_);
v___x_1073_ = l_Lean_mkApp3(v___x_1072_, v_00_u03c3s_1049_, v_hyp_1050_, v_a_1064_);
v___x_1074_ = lean_box(0);
v___x_1075_ = l_Lean_Meta_synthInstance(v___x_1073_, v___x_1074_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_name_1051_, v___y_1055_, v___y_1056_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___f_1081_; lean_object* v___x_1082_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v_fst_1079_ = lean_ctor_get(v_a_1078_, 0);
lean_inc(v_fst_1079_);
v_snd_1080_ = lean_ctor_get(v_a_1078_, 1);
lean_inc(v_snd_1080_);
lean_dec(v_a_1078_);
lean_inc(v_a_1064_);
v___f_1081_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1081_, 0, v_a_1064_);
lean_closure_set(v___f_1081_, 1, v_snd_1080_);
lean_closure_set(v___f_1081_, 2, v_k_1052_);
lean_closure_set(v___f_1081_, 3, v___x_1065_);
lean_closure_set(v___f_1081_, 4, v___x_1066_);
lean_closure_set(v___f_1081_, 5, v___x_1067_);
lean_closure_set(v___f_1081_, 6, v___x_1068_);
lean_closure_set(v___f_1081_, 7, v___x_1071_);
lean_closure_set(v___f_1081_, 8, v_00_u03c3s_1049_);
lean_closure_set(v___f_1081_, 9, v_hyp_1050_);
lean_closure_set(v___f_1081_, 10, v_a_1076_);
lean_closure_set(v___f_1081_, 11, v_a_1059_);
v___x_1082_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesExists_spec__0___redArg(v_fst_1079_, v_a_1064_, v___f_1081_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
return v___x_1082_;
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec(v_a_1076_);
lean_dec_ref_known(v___x_1071_, 2);
lean_dec(v_a_1064_);
lean_dec(v_a_1059_);
lean_dec_ref(v_k_1052_);
lean_dec_ref(v_hyp_1050_);
lean_dec_ref(v_00_u03c3s_1049_);
v_a_1083_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1077_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1077_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref_known(v___x_1071_, 2);
lean_dec(v_a_1064_);
lean_dec(v_a_1059_);
lean_dec_ref(v_k_1052_);
lean_dec(v_name_1051_);
lean_dec_ref(v_hyp_1050_);
lean_dec_ref(v_00_u03c3s_1049_);
v_a_1091_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1075_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1075_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_a_1059_);
lean_dec_ref(v_k_1052_);
lean_dec(v_name_1051_);
lean_dec_ref(v_hyp_1050_);
lean_dec_ref(v_00_u03c3s_1049_);
v_a_1099_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1063_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1063_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v_k_1052_);
lean_dec(v_name_1051_);
lean_dec_ref(v_hyp_1050_);
lean_dec_ref(v_00_u03c3s_1049_);
v_a_1107_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1058_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1058_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___boxed(lean_object* v_00_u03c3s_1115_, lean_object* v_hyp_1116_, lean_object* v_name_1117_, lean_object* v_k_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1115_, v_hyp_1116_, v_name_1117_, v_k_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(lean_object* v_u_1133_, lean_object* v_00_u03c3s_1134_, lean_object* v_k_1135_, lean_object* v_x_1136_, lean_object* v___h_u03c6_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_H_x27_1143_; lean_object* v___x_1144_; 
lean_inc_ref(v_00_u03c3s_1134_);
lean_inc(v_u_1133_);
v_H_x27_1143_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1133_, v_00_u03c3s_1134_);
lean_inc(v___y_1141_);
lean_inc_ref(v___y_1140_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
v___x_1144_ = lean_apply_6(v_k_1135_, v_H_x27_1143_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, lean_box(0));
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v_snd_1146_; lean_object* v_fst_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1204_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v_snd_1146_ = lean_ctor_get(v_a_1145_, 1);
v_fst_1147_ = lean_ctor_get(v_a_1145_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_a_1145_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1149_ = v_a_1145_;
v_isShared_1150_ = v_isSharedCheck_1204_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_snd_1146_);
lean_inc(v_fst_1147_);
lean_dec(v_a_1145_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1204_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1203_; 
v_fst_1151_ = lean_ctor_get(v_snd_1146_, 0);
v_snd_1152_ = lean_ctor_get(v_snd_1146_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_snd_1146_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1154_ = v_snd_1146_;
v_isShared_1155_ = v_isSharedCheck_1203_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_inc(v_fst_1151_);
lean_dec(v_snd_1146_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1203_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; 
lean_inc(v_fst_1151_);
v___x_1156_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1151_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1194_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1194_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1194_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_fst_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1192_; 
v_fst_1161_ = lean_ctor_get(v_a_1157_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_a_1157_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v_a_1157_, 1);
lean_dec(v_unused_1193_);
v___x_1163_ = v_a_1157_;
v_isShared_1164_ = v_isSharedCheck_1192_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_fst_1161_);
lean_dec(v_a_1157_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1192_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_u_1165_; lean_object* v_00_u03c3s_1166_; lean_object* v_target_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1190_; 
v_u_1165_ = lean_ctor_get(v_fst_1151_, 0);
v_00_u03c3s_1166_ = lean_ctor_get(v_fst_1151_, 1);
v_target_1167_ = lean_ctor_get(v_fst_1151_, 3);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_fst_1151_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v_fst_1151_, 2);
lean_dec(v_unused_1191_);
v___x_1169_ = v_fst_1151_;
v_isShared_1170_ = v_isSharedCheck_1190_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_target_1167_);
lean_inc(v_00_u03c3s_1166_);
lean_inc(v_u_1165_);
lean_dec(v_fst_1151_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1190_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___closed__1));
v___x_1172_ = lean_box(0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 1);
lean_ctor_set(v___x_1149_, 1, v___x_1172_);
lean_ctor_set(v___x_1149_, 0, v_u_1133_);
v___x_1174_ = v___x_1149_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_u_1133_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1175_ = l_Lean_mkConst(v___x_1171_, v___x_1174_);
lean_inc_ref(v_target_1167_);
lean_inc(v_fst_1161_);
v___x_1176_ = l_Lean_mkApp4(v___x_1175_, v_00_u03c3s_1134_, v_fst_1161_, v_target_1167_, v_snd_1152_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 2, v_fst_1161_);
v___x_1178_ = v___x_1169_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_u_1165_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_00_u03c3s_1166_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_fst_1161_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_target_1167_);
v___x_1178_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1176_);
lean_ctor_set(v___x_1163_, 0, v___x_1178_);
v___x_1180_ = v___x_1163_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v___x_1176_);
v___x_1180_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1182_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v___x_1180_);
lean_ctor_set(v___x_1154_, 0, v_fst_1147_);
v___x_1182_ = v___x_1154_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_fst_1147_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1182_);
v___x_1184_ = v___x_1159_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
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
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_del_object(v___x_1154_);
lean_dec(v_snd_1152_);
lean_dec(v_fst_1151_);
lean_del_object(v___x_1149_);
lean_dec(v_fst_1147_);
lean_dec_ref(v_00_u03c3s_1134_);
lean_dec(v_u_1133_);
v_a_1195_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1156_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1156_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_00_u03c3s_1134_);
lean_dec(v_u_1133_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed(lean_object* v_u_1205_, lean_object* v_00_u03c3s_1206_, lean_object* v_k_1207_, lean_object* v_x_1208_, lean_object* v___h_u03c6_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3(v_u_1205_, v_00_u03c3s_1206_, v_k_1207_, v_x_1208_, v___h_u03c6_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec_ref(v___h_u03c6_1209_);
lean_dec_ref(v_x_1208_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(lean_object* v_u_1232_, lean_object* v_00_u03c3s_1233_, lean_object* v_k_1234_, lean_object* v_tail_1235_, lean_object* v_fst_1236_, lean_object* v_H_u2081_x27_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v___f_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
lean_inc_ref(v_H_u2081_x27_1237_);
lean_inc_ref_n(v_00_u03c3s_1233_, 2);
lean_inc_n(v_u_1232_, 2);
v___f_1243_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_1243_, 0, v_u_1232_);
lean_closure_set(v___f_1243_, 1, v_00_u03c3s_1233_);
lean_closure_set(v___f_1243_, 2, v_H_u2081_x27_1237_);
lean_closure_set(v___f_1243_, 3, v_k_1234_);
v___x_1244_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1244_, 0, v_tail_1235_);
lean_inc_ref(v_fst_1236_);
v___x_1245_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1232_, v_00_u03c3s_1233_, v_fst_1236_, v___x_1244_, v___f_1243_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1291_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1291_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1291_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_fst_1250_; lean_object* v_snd_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1290_; 
v_fst_1250_ = lean_ctor_get(v_a_1246_, 0);
v_snd_1251_ = lean_ctor_get(v_a_1246_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_a_1246_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1253_ = v_a_1246_;
v_isShared_1254_ = v_isSharedCheck_1290_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_snd_1251_);
lean_inc(v_fst_1250_);
lean_dec(v_a_1246_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1290_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_fst_1255_; lean_object* v_snd_1256_; lean_object* v_snd_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1288_; 
v_fst_1255_ = lean_ctor_get(v_snd_1251_, 0);
lean_inc(v_fst_1255_);
v_snd_1256_ = lean_ctor_get(v_fst_1250_, 1);
v_snd_1257_ = lean_ctor_get(v_snd_1251_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_snd_1251_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_snd_1251_, 0);
lean_dec(v_unused_1289_);
v___x_1259_ = v_snd_1251_;
v_isShared_1260_ = v_isSharedCheck_1288_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_snd_1257_);
lean_dec(v_snd_1251_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1288_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_u_1261_; lean_object* v_00_u03c3s_1262_; lean_object* v_target_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1286_; 
v_u_1261_ = lean_ctor_get(v_fst_1255_, 0);
v_00_u03c3s_1262_ = lean_ctor_get(v_fst_1255_, 1);
v_target_1263_ = lean_ctor_get(v_fst_1255_, 3);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_fst_1255_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v_fst_1255_, 2);
lean_dec(v_unused_1287_);
v___x_1265_ = v_fst_1255_;
v_isShared_1266_ = v_isSharedCheck_1286_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_target_1263_);
lean_inc(v_00_u03c3s_1262_);
lean_inc(v_u_1261_);
lean_dec(v_fst_1255_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1286_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1267_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___closed__1));
v___x_1268_ = lean_box(0);
lean_inc_n(v_u_1232_, 2);
v___x_1269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_u_1232_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = l_Lean_mkConst(v___x_1267_, v___x_1269_);
lean_inc_ref(v_target_1263_);
lean_inc_ref(v_fst_1236_);
lean_inc_ref(v_H_u2081_x27_1237_);
lean_inc_n(v_snd_1256_, 2);
lean_inc_ref_n(v_00_u03c3s_1233_, 2);
v___x_1271_ = l_Lean_mkApp6(v___x_1270_, v_00_u03c3s_1233_, v_snd_1256_, v_H_u2081_x27_1237_, v_fst_1236_, v_target_1263_, v_snd_1257_);
v___x_1272_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1232_, v_00_u03c3s_1233_, v_snd_1256_, v_fst_1236_);
v___x_1273_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1232_, v_00_u03c3s_1233_, v___x_1272_, v_H_u2081_x27_1237_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 2, v___x_1273_);
v___x_1275_ = v___x_1265_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_u_1261_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_00_u03c3s_1262_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_target_1263_);
v___x_1275_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1271_);
lean_ctor_set(v___x_1259_, 0, v___x_1275_);
v___x_1277_ = v___x_1259_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1271_);
v___x_1277_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1279_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v___x_1277_);
v___x_1279_ = v___x_1253_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_fst_1250_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1281_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1279_);
v___x_1281_ = v___x_1248_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
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
lean_dec_ref(v_H_u2081_x27_1237_);
lean_dec_ref(v_fst_1236_);
lean_dec_ref(v_00_u03c3s_1233_);
lean_dec(v_u_1232_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed(lean_object* v_u_1292_, lean_object* v_00_u03c3s_1293_, lean_object* v_k_1294_, lean_object* v_tail_1295_, lean_object* v_fst_1296_, lean_object* v_H_u2081_x27_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1(v_u_1292_, v_00_u03c3s_1293_, v_k_1294_, v_tail_1295_, v_fst_1296_, v_H_u2081_x27_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
return v_res_1303_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5(void){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__4));
v___x_1314_ = l_Lean_stringToMessageData(v___x_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed(lean_object* v___x_1315_, lean_object* v_tail_1316_, lean_object* v_u_1317_, lean_object* v___x_1318_, lean_object* v_k_1319_, lean_object* v_x_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(v___x_1315_, v_tail_1316_, v_u_1317_, v___x_1318_, v_k_1319_, v_x_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
return v_res_1326_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__6));
v___x_1329_ = l_Lean_stringToMessageData(v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__10));
v___x_1338_ = l_Lean_stringToMessageData(v___x_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(lean_object* v_u_1345_, lean_object* v_00_u03c3s_1346_, lean_object* v_H_1347_, lean_object* v_pat_1348_, lean_object* v_k_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
switch(lean_obj_tag(v_pat_1348_))
{
case 0:
{
lean_object* v_name_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1402_; 
v_name_1355_ = lean_ctor_get(v_pat_1348_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v_pat_1348_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1357_ = v_pat_1348_;
v_isShared_1358_ = v_isSharedCheck_1402_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_name_1355_);
lean_dec(v_pat_1348_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1402_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___y_1360_; uint8_t v___y_1361_; lean_object* v___y_1367_; lean_object* v_a_1368_; lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1371_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__1);
v___x_1372_ = 0;
v___x_1373_ = lean_box(0);
v___x_1374_ = l_Lean_Meta_mkFreshExprMVar(v___x_1371_, v___x_1372_, v___x_1373_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg___closed__3));
v___x_1377_ = lean_box(0);
lean_inc(v_u_1345_);
v___x_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_u_1345_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = l_Lean_mkConst(v___x_1376_, v___x_1378_);
lean_inc_ref(v_H_1347_);
lean_inc_ref(v_00_u03c3s_1346_);
v___x_1380_ = l_Lean_mkApp3(v___x_1379_, v_00_u03c3s_1346_, v_H_1347_, v_a_1375_);
v___x_1381_ = lean_box(0);
v___x_1382_ = l_Lean_Meta_synthInstance(v___x_1380_, v___x_1381_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_dec_ref_known(v___x_1382_, 1);
lean_inc(v_name_1355_);
v___x_1383_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_name_1355_);
lean_inc_ref(v_k_1349_);
lean_inc_ref(v_H_1347_);
lean_inc_ref(v_00_u03c3s_1346_);
lean_inc(v_u_1345_);
v___x_1384_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1345_, v_00_u03c3s_1346_, v_H_1347_, v___x_1383_, v_k_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_del_object(v___x_1357_);
lean_dec(v_name_1355_);
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
lean_dec(v_u_1345_);
return v___x_1384_;
}
else
{
lean_object* v_a_1385_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
v___y_1367_ = v___x_1384_;
v_a_1368_ = v_a_1385_;
goto v___jp_1366_;
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_a_1386_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1382_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1382_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
lean_inc(v_a_1386_);
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
v___y_1367_ = v___x_1391_;
v_a_1368_ = v_a_1386_;
goto v___jp_1366_;
}
}
}
}
else
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
v_a_1394_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1374_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1374_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
lean_inc(v_a_1394_);
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
v___y_1367_ = v___x_1399_;
v_a_1368_ = v_a_1394_;
goto v___jp_1366_;
}
}
}
v___jp_1359_:
{
if (v___y_1361_ == 0)
{
lean_object* v___x_1363_; 
lean_dec_ref(v___y_1360_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set_tag(v___x_1357_, 5);
v___x_1363_ = v___x_1357_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_name_1355_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
v_pat_1348_ = v___x_1363_;
goto _start;
}
}
else
{
lean_del_object(v___x_1357_);
lean_dec(v_name_1355_);
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
lean_dec(v_u_1345_);
return v___y_1360_;
}
}
v___jp_1366_:
{
uint8_t v___x_1369_; 
v___x_1369_ = l_Lean_Exception_isInterrupt(v_a_1368_);
if (v___x_1369_ == 0)
{
uint8_t v___x_1370_; 
v___x_1370_ = l_Lean_Exception_isRuntime(v_a_1368_);
v___y_1360_ = v___y_1367_;
v___y_1361_ = v___x_1370_;
goto v___jp_1359_;
}
else
{
lean_dec_ref(v_a_1368_);
v___y_1360_ = v___y_1367_;
v___y_1361_ = v___x_1369_;
goto v___jp_1359_;
}
}
}
}
case 1:
{
lean_object* v_H_x27_1403_; lean_object* v___x_1404_; 
lean_inc_ref(v_00_u03c3s_1346_);
lean_inc(v_u_1345_);
v_H_x27_1403_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_1345_, v_00_u03c3s_1346_);
lean_inc(v_a_1353_);
lean_inc_ref(v_a_1352_);
lean_inc(v_a_1351_);
lean_inc_ref(v_a_1350_);
v___x_1404_ = lean_apply_6(v_k_1349_, v_H_x27_1403_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, lean_box(0));
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_object* v_a_1405_; lean_object* v_snd_1406_; lean_object* v_fst_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1465_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___x_1404_, 1);
v_snd_1406_ = lean_ctor_get(v_a_1405_, 1);
v_fst_1407_ = lean_ctor_get(v_a_1405_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_a_1405_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1409_ = v_a_1405_;
v_isShared_1410_ = v_isSharedCheck_1465_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_snd_1406_);
lean_inc(v_fst_1407_);
lean_dec(v_a_1405_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1465_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v_fst_1411_; lean_object* v_snd_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1464_; 
v_fst_1411_ = lean_ctor_get(v_snd_1406_, 0);
v_snd_1412_ = lean_ctor_get(v_snd_1406_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_snd_1406_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1414_ = v_snd_1406_;
v_isShared_1415_ = v_isSharedCheck_1464_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_snd_1412_);
lean_inc(v_fst_1411_);
lean_dec(v_snd_1406_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1464_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; 
lean_inc(v_fst_1411_);
v___x_1416_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1411_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1455_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1455_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1455_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_fst_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1453_; 
v_fst_1421_ = lean_ctor_get(v_a_1417_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_a_1417_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_a_1417_, 1);
lean_dec(v_unused_1454_);
v___x_1423_ = v_a_1417_;
v_isShared_1424_ = v_isSharedCheck_1453_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_fst_1421_);
lean_dec(v_a_1417_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1453_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v_u_1425_; lean_object* v_00_u03c3s_1426_; lean_object* v_target_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1451_; 
v_u_1425_ = lean_ctor_get(v_fst_1411_, 0);
v_00_u03c3s_1426_ = lean_ctor_get(v_fst_1411_, 1);
v_target_1427_ = lean_ctor_get(v_fst_1411_, 3);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_fst_1411_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v_fst_1411_, 2);
lean_dec(v_unused_1452_);
v___x_1429_ = v_fst_1411_;
v_isShared_1430_ = v_isSharedCheck_1451_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_target_1427_);
lean_inc(v_00_u03c3s_1426_);
lean_inc(v_u_1425_);
lean_dec(v_fst_1411_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1451_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1431_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__1));
v___x_1432_ = lean_box(0);
lean_inc(v_u_1345_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 1);
lean_ctor_set(v___x_1409_, 1, v___x_1432_);
lean_ctor_set(v___x_1409_, 0, v_u_1345_);
v___x_1434_ = v___x_1409_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_u_1345_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1435_ = l_Lean_mkConst(v___x_1431_, v___x_1434_);
lean_inc_ref(v_target_1427_);
lean_inc_ref(v_H_1347_);
lean_inc(v_fst_1421_);
lean_inc_ref(v_00_u03c3s_1346_);
v___x_1436_ = l_Lean_mkApp5(v___x_1435_, v_00_u03c3s_1346_, v_fst_1421_, v_H_1347_, v_target_1427_, v_snd_1412_);
v___x_1437_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1345_, v_00_u03c3s_1346_, v_fst_1421_, v_H_1347_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 2, v___x_1437_);
v___x_1439_ = v___x_1429_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_u_1425_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_00_u03c3s_1426_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v_target_1427_);
v___x_1439_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1441_; 
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1436_);
lean_ctor_set(v___x_1423_, 0, v___x_1439_);
v___x_1441_ = v___x_1423_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1436_);
v___x_1441_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1443_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v___x_1441_);
lean_ctor_set(v___x_1414_, 0, v_fst_1407_);
v___x_1443_ = v___x_1414_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_fst_1407_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1441_);
v___x_1443_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1445_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1443_);
v___x_1445_ = v___x_1419_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
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
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_del_object(v___x_1414_);
lean_dec(v_snd_1412_);
lean_dec(v_fst_1411_);
lean_del_object(v___x_1409_);
lean_dec(v_fst_1407_);
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
lean_dec(v_u_1345_);
v_a_1456_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1416_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1416_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
lean_dec(v_u_1345_);
return v___x_1404_;
}
}
case 2:
{
lean_object* v_args_1466_; 
v_args_1466_ = lean_ctor_get(v_pat_1348_, 0);
lean_inc(v_args_1466_);
lean_dec_ref_known(v_pat_1348_, 1);
if (lean_obj_tag(v_args_1466_) == 0)
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_box(1);
v_pat_1348_ = v___x_1467_;
goto _start;
}
else
{
lean_object* v_tail_1469_; 
v_tail_1469_ = lean_ctor_get(v_args_1466_, 1);
if (lean_obj_tag(v_tail_1469_) == 0)
{
lean_object* v_head_1470_; 
v_head_1470_ = lean_ctor_get(v_args_1466_, 0);
lean_inc(v_head_1470_);
lean_dec_ref_known(v_args_1466_, 2);
v_pat_1348_ = v_head_1470_;
goto _start;
}
else
{
lean_object* v_head_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1565_; 
lean_inc(v_tail_1469_);
v_head_1472_ = lean_ctor_get(v_args_1466_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_args_1466_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v_args_1466_, 1);
lean_dec(v_unused_1566_);
v___x_1474_ = v_args_1466_;
v_isShared_1475_ = v_isSharedCheck_1565_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_head_1472_);
lean_dec(v_args_1466_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1565_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; 
lean_inc_ref(v_H_1347_);
lean_inc_ref(v_00_u03c3s_1346_);
lean_inc(v_u_1345_);
v___x_1476_ = l_Lean_Elab_Tactic_Do_ProofMode_synthIsAnd(v_u_1345_, v_00_u03c3s_1346_, v_H_1347_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
if (lean_obj_tag(v_a_1477_) == 1)
{
lean_object* v_val_1478_; lean_object* v_snd_1479_; lean_object* v_fst_1480_; lean_object* v_fst_1481_; lean_object* v_snd_1482_; lean_object* v___f_1483_; lean_object* v___x_1484_; 
v_val_1478_ = lean_ctor_get(v_a_1477_, 0);
lean_inc(v_val_1478_);
lean_dec_ref_known(v_a_1477_, 1);
v_snd_1479_ = lean_ctor_get(v_val_1478_, 1);
lean_inc(v_snd_1479_);
v_fst_1480_ = lean_ctor_get(v_val_1478_, 0);
lean_inc_n(v_fst_1480_, 2);
lean_dec(v_val_1478_);
v_fst_1481_ = lean_ctor_get(v_snd_1479_, 0);
lean_inc_n(v_fst_1481_, 2);
v_snd_1482_ = lean_ctor_get(v_snd_1479_, 1);
lean_inc(v_snd_1482_);
lean_dec(v_snd_1479_);
lean_inc_ref_n(v_00_u03c3s_1346_, 2);
lean_inc_n(v_u_1345_, 2);
v___f_1483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__1___boxed), 11, 5);
lean_closure_set(v___f_1483_, 0, v_u_1345_);
lean_closure_set(v___f_1483_, 1, v_00_u03c3s_1346_);
lean_closure_set(v___f_1483_, 2, v_k_1349_);
lean_closure_set(v___f_1483_, 3, v_tail_1469_);
lean_closure_set(v___f_1483_, 4, v_fst_1481_);
v___x_1484_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1345_, v_00_u03c3s_1346_, v_fst_1480_, v_head_1472_, v___f_1483_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1532_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1532_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1532_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_fst_1489_; lean_object* v_snd_1490_; lean_object* v_fst_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1531_; 
v_fst_1489_ = lean_ctor_get(v_a_1485_, 0);
lean_inc(v_fst_1489_);
v_snd_1490_ = lean_ctor_get(v_a_1485_, 1);
lean_inc(v_snd_1490_);
lean_dec(v_a_1485_);
v_fst_1491_ = lean_ctor_get(v_snd_1490_, 0);
lean_inc(v_fst_1491_);
v_fst_1492_ = lean_ctor_get(v_fst_1489_, 0);
v_snd_1493_ = lean_ctor_get(v_fst_1489_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_fst_1489_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1495_ = v_fst_1489_;
v_isShared_1496_ = v_isSharedCheck_1531_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_snd_1493_);
lean_inc(v_fst_1492_);
lean_dec(v_fst_1489_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1531_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_snd_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1529_; 
v_snd_1497_ = lean_ctor_get(v_snd_1490_, 1);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_snd_1490_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_snd_1490_, 0);
lean_dec(v_unused_1530_);
v___x_1499_ = v_snd_1490_;
v_isShared_1500_ = v_isSharedCheck_1529_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snd_1497_);
lean_dec(v_snd_1490_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1529_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_u_1501_; lean_object* v_00_u03c3s_1502_; lean_object* v_target_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1527_; 
v_u_1501_ = lean_ctor_get(v_fst_1491_, 0);
v_00_u03c3s_1502_ = lean_ctor_get(v_fst_1491_, 1);
v_target_1503_ = lean_ctor_get(v_fst_1491_, 3);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_fst_1491_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v_fst_1491_, 2);
lean_dec(v_unused_1528_);
v___x_1505_ = v_fst_1491_;
v_isShared_1506_ = v_isSharedCheck_1527_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_target_1503_);
lean_inc(v_00_u03c3s_1502_);
lean_inc(v_u_1501_);
lean_dec(v_fst_1491_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1527_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1507_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__3));
v___x_1508_ = lean_box(0);
lean_inc(v_u_1345_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 1, v___x_1508_);
lean_ctor_set(v___x_1474_, 0, v_u_1345_);
v___x_1510_ = v___x_1474_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_u_1345_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1511_ = l_Lean_mkConst(v___x_1507_, v___x_1510_);
lean_inc_ref(v_target_1503_);
lean_inc_ref(v_H_1347_);
lean_inc(v_snd_1493_);
lean_inc_ref(v_00_u03c3s_1346_);
v___x_1512_ = l_Lean_mkApp8(v___x_1511_, v_00_u03c3s_1346_, v_snd_1493_, v_fst_1480_, v_fst_1481_, v_H_1347_, v_target_1503_, v_snd_1482_, v_snd_1497_);
v___x_1513_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1345_, v_00_u03c3s_1346_, v_snd_1493_, v_H_1347_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 2, v___x_1513_);
v___x_1515_ = v___x_1505_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_u_1501_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_00_u03c3s_1502_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_target_1503_);
v___x_1515_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1517_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v___x_1512_);
lean_ctor_set(v___x_1499_, 0, v___x_1515_);
v___x_1517_ = v___x_1499_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1515_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1512_);
v___x_1517_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
lean_object* v___x_1519_; 
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 1, v___x_1517_);
v___x_1519_ = v___x_1495_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_fst_1492_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1519_);
v___x_1521_ = v___x_1487_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
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
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_snd_1482_);
lean_dec(v_fst_1481_);
lean_dec(v_fst_1480_);
lean_del_object(v___x_1474_);
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
lean_dec(v_u_1345_);
v_a_1533_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1484_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1484_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
lean_dec(v_a_1477_);
lean_del_object(v___x_1474_);
lean_dec_ref(v_00_u03c3s_1346_);
v___x_1541_ = l_Lean_Expr_consumeMData(v_H_1347_);
v___x_1542_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg___closed__1));
v___x_1543_ = lean_unsigned_to_nat(3u);
v___x_1544_ = l_Lean_Expr_isAppOfArity(v___x_1541_, v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec_ref(v___x_1541_);
lean_dec(v_head_1472_);
lean_dec(v_tail_1469_);
lean_dec_ref(v_k_1349_);
lean_dec(v_u_1345_);
v___x_1545_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__5);
v___x_1546_ = l_Lean_MessageData_ofExpr(v_H_1347_);
v___x_1547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1545_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1547_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
return v___x_1548_;
}
else
{
if (lean_obj_tag(v_head_1472_) == 0)
{
lean_object* v_name_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; 
v_name_1549_ = lean_ctor_get(v_head_1472_, 0);
lean_inc(v_name_1549_);
lean_dec_ref_known(v_head_1472_, 1);
v___x_1550_ = l_Lean_Expr_appFn_x21(v___x_1541_);
v___x_1551_ = l_Lean_Expr_appArg_x21(v___x_1550_);
lean_dec_ref(v___x_1550_);
v___x_1552_ = l_Lean_Expr_appArg_x21(v___x_1541_);
lean_dec_ref(v___x_1541_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2___boxed), 11, 5);
lean_closure_set(v___f_1553_, 0, v___x_1552_);
lean_closure_set(v___f_1553_, 1, v_tail_1469_);
lean_closure_set(v___f_1553_, 2, v_u_1345_);
lean_closure_set(v___f_1553_, 3, v___x_1551_);
lean_closure_set(v___f_1553_, 4, v_k_1349_);
v___x_1554_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesExists___redArg(v_H_1347_, v_name_1549_, v___f_1553_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
lean_dec_ref(v___x_1541_);
lean_dec(v_head_1472_);
lean_dec(v_tail_1469_);
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_H_1347_);
lean_dec(v_u_1345_);
v___x_1555_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__7);
v___x_1556_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1555_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_del_object(v___x_1474_);
lean_dec(v_head_1472_);
lean_dec(v_tail_1469_);
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
lean_dec(v_u_1345_);
v_a_1557_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1476_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1476_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
}
}
}
case 3:
{
lean_object* v_args_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1662_; 
v_args_1567_ = lean_ctor_get(v_pat_1348_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_pat_1348_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1569_ = v_pat_1348_;
v_isShared_1570_ = v_isSharedCheck_1662_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_args_1567_);
lean_dec(v_pat_1348_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1662_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
if (lean_obj_tag(v_args_1567_) == 0)
{
lean_object* v___x_1571_; 
lean_del_object(v___x_1569_);
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
lean_dec(v_u_1345_);
v___x_1571_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg();
return v___x_1571_;
}
else
{
lean_object* v_tail_1572_; 
v_tail_1572_ = lean_ctor_get(v_args_1567_, 1);
if (lean_obj_tag(v_tail_1572_) == 0)
{
lean_object* v_head_1573_; 
lean_del_object(v___x_1569_);
v_head_1573_ = lean_ctor_get(v_args_1567_, 0);
lean_inc(v_head_1573_);
lean_dec_ref_known(v_args_1567_, 2);
v_pat_1348_ = v_head_1573_;
goto _start;
}
else
{
lean_object* v_head_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1660_; 
lean_inc(v_tail_1572_);
lean_dec_ref(v_00_u03c3s_1346_);
v_head_1575_ = lean_ctor_get(v_args_1567_, 0);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_args_1567_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_args_1567_, 1);
lean_dec(v_unused_1661_);
v___x_1577_ = v_args_1567_;
v_isShared_1578_ = v_isSharedCheck_1660_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_head_1575_);
lean_dec(v_args_1567_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1660_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1579_ = l_Lean_Expr_consumeMData(v_H_1347_);
v___x_1580_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__9));
v___x_1581_ = lean_unsigned_to_nat(3u);
v___x_1582_ = l_Lean_Expr_isAppOfArity(v___x_1579_, v___x_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v___x_1579_);
lean_del_object(v___x_1577_);
lean_dec(v_head_1575_);
lean_dec(v_tail_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v_k_1349_);
lean_dec(v_u_1345_);
v___x_1583_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__11);
v___x_1584_ = l_Lean_MessageData_ofExpr(v_H_1347_);
v___x_1585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
v___x_1586_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0___redArg(v___x_1585_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec_ref(v_H_1347_);
v___x_1587_ = l_Lean_Expr_appFn_x21(v___x_1579_);
v___x_1588_ = l_Lean_Expr_appFn_x21(v___x_1587_);
v___x_1589_ = l_Lean_Expr_appArg_x21(v___x_1588_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = l_Lean_Expr_appArg_x21(v___x_1587_);
lean_dec_ref(v___x_1587_);
lean_inc_ref(v_k_1349_);
lean_inc_ref(v___x_1590_);
lean_inc_ref(v___x_1589_);
lean_inc(v_u_1345_);
v___x_1591_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1345_, v___x_1589_, v___x_1590_, v_head_1575_, v_k_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v_snd_1593_; lean_object* v_fst_1594_; lean_object* v_snd_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v_snd_1593_ = lean_ctor_get(v_a_1592_, 1);
lean_inc(v_snd_1593_);
lean_dec(v_a_1592_);
v_fst_1594_ = lean_ctor_get(v_snd_1593_, 0);
lean_inc(v_fst_1594_);
v_snd_1595_ = lean_ctor_get(v_snd_1593_, 1);
lean_inc(v_snd_1595_);
lean_dec(v_snd_1593_);
v___x_1596_ = l_Lean_Expr_appArg_x21(v___x_1579_);
lean_dec_ref(v___x_1579_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v_tail_1572_);
v___x_1598_ = v___x_1569_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_tail_1572_);
v___x_1598_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
lean_inc_ref(v___x_1596_);
lean_inc_ref(v___x_1589_);
lean_inc(v_u_1345_);
v___x_1599_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1345_, v___x_1589_, v___x_1596_, v___x_1598_, v_k_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v_snd_1601_; lean_object* v_fst_1602_; lean_object* v_snd_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1657_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v_snd_1601_ = lean_ctor_get(v_a_1600_, 1);
lean_inc(v_snd_1601_);
v_fst_1602_ = lean_ctor_get(v_a_1600_, 0);
lean_inc(v_fst_1602_);
lean_dec(v_a_1600_);
v_snd_1603_ = lean_ctor_get(v_snd_1601_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_snd_1601_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_snd_1601_, 0);
lean_dec(v_unused_1658_);
v___x_1605_ = v_snd_1601_;
v_isShared_1606_ = v_isSharedCheck_1657_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_snd_1603_);
lean_dec(v_snd_1601_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1657_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; 
lean_inc(v_fst_1594_);
v___x_1607_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH(v_fst_1594_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1648_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1648_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1648_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_fst_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1646_; 
v_fst_1612_ = lean_ctor_get(v_a_1608_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_a_1608_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v_a_1608_, 1);
lean_dec(v_unused_1647_);
v___x_1614_ = v_a_1608_;
v_isShared_1615_ = v_isSharedCheck_1646_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_fst_1612_);
lean_dec(v_a_1608_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1646_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_u_1616_; lean_object* v_00_u03c3s_1617_; lean_object* v_target_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1644_; 
v_u_1616_ = lean_ctor_get(v_fst_1594_, 0);
v_00_u03c3s_1617_ = lean_ctor_get(v_fst_1594_, 1);
v_target_1618_ = lean_ctor_get(v_fst_1594_, 3);
v_isSharedCheck_1644_ = !lean_is_exclusive(v_fst_1594_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v_fst_1594_, 2);
lean_dec(v_unused_1645_);
v___x_1620_ = v_fst_1594_;
v_isShared_1621_ = v_isSharedCheck_1644_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_target_1618_);
lean_inc(v_00_u03c3s_1617_);
lean_inc(v_u_1616_);
lean_dec(v_fst_1594_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1644_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = lean_box(0);
lean_inc(v_u_1345_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v___x_1622_);
lean_ctor_set(v___x_1577_, 0, v_u_1345_);
v___x_1624_ = v___x_1577_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_u_1345_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_inc_ref(v___x_1624_);
v___x_1625_ = l_Lean_mkConst(v___x_1580_, v___x_1624_);
lean_inc_ref(v___x_1596_);
lean_inc_ref(v___x_1590_);
lean_inc_ref_n(v___x_1589_, 2);
v___x_1626_ = l_Lean_mkApp3(v___x_1625_, v___x_1589_, v___x_1590_, v___x_1596_);
lean_inc(v_fst_1612_);
v___x_1627_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(v_u_1345_, v___x_1589_, v_fst_1612_, v___x_1626_);
lean_inc_ref(v_target_1618_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 2, v___x_1627_);
v___x_1629_ = v___x_1620_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_u_1616_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_00_u03c3s_1617_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1642_, 3, v_target_1618_);
v___x_1629_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1630_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___closed__13));
v___x_1631_ = l_Lean_mkConst(v___x_1630_, v___x_1624_);
v___x_1632_ = l_Lean_mkApp7(v___x_1631_, v___x_1589_, v_fst_1612_, v___x_1590_, v___x_1596_, v_target_1618_, v_snd_1595_, v_snd_1603_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 1, v___x_1632_);
lean_ctor_set(v___x_1614_, 0, v___x_1629_);
v___x_1634_ = v___x_1614_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 1, v___x_1634_);
lean_ctor_set(v___x_1605_, 0, v_fst_1602_);
v___x_1636_ = v___x_1605_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_fst_1602_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1636_);
v___x_1638_ = v___x_1610_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
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
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_del_object(v___x_1605_);
lean_dec(v_snd_1603_);
lean_dec(v_fst_1602_);
lean_dec_ref(v___x_1596_);
lean_dec(v_snd_1595_);
lean_dec(v_fst_1594_);
lean_dec_ref(v___x_1590_);
lean_dec_ref(v___x_1589_);
lean_del_object(v___x_1577_);
lean_dec(v_u_1345_);
v_a_1649_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1607_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1607_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1596_);
lean_dec(v_snd_1595_);
lean_dec(v_fst_1594_);
lean_dec_ref(v___x_1590_);
lean_dec_ref(v___x_1589_);
lean_del_object(v___x_1577_);
lean_dec(v_u_1345_);
return v___x_1599_;
}
}
}
else
{
lean_dec_ref(v___x_1590_);
lean_dec_ref(v___x_1589_);
lean_dec_ref(v___x_1579_);
lean_del_object(v___x_1577_);
lean_dec(v_tail_1572_);
lean_del_object(v___x_1569_);
lean_dec_ref(v_k_1349_);
lean_dec(v_u_1345_);
return v___x_1591_;
}
}
}
}
}
}
}
case 4:
{
lean_object* v_h_1663_; lean_object* v___f_1664_; lean_object* v___x_1665_; 
v_h_1663_ = lean_ctor_get(v_pat_1348_, 0);
lean_inc(v_h_1663_);
lean_dec_ref_known(v_pat_1348_, 1);
lean_inc_ref(v_00_u03c3s_1346_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__3___boxed), 10, 3);
lean_closure_set(v___f_1664_, 0, v_u_1345_);
lean_closure_set(v___f_1664_, 1, v_00_u03c3s_1346_);
lean_closure_set(v___f_1664_, 2, v_k_1349_);
v___x_1665_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1346_, v_H_1347_, v_h_1663_, v___f_1664_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
return v___x_1665_;
}
default: 
{
lean_object* v_h_1666_; lean_object* v___x_1667_; 
lean_dec(v_u_1345_);
v_h_1666_ = lean_ctor_get(v_pat_1348_, 0);
lean_inc(v_h_1666_);
lean_dec_ref_known(v_pat_1348_, 1);
v___x_1667_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_h_1666_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v_fst_1669_; lean_object* v_snd_1670_; lean_object* v___x_1671_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1667_, 1);
v_fst_1669_ = lean_ctor_get(v_a_1668_, 0);
lean_inc(v_fst_1669_);
v_snd_1670_ = lean_ctor_get(v_a_1668_, 1);
lean_inc(v_snd_1670_);
lean_dec(v_a_1668_);
v___x_1671_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__2___redArg(v_a_1353_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1671_, 1);
v___x_1673_ = l_Lean_Expr_consumeMData(v_H_1347_);
lean_dec_ref(v_H_1347_);
v___x_1674_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1674_, 0, v_fst_1669_);
lean_ctor_set(v___x_1674_, 1, v_a_1672_);
lean_ctor_set(v___x_1674_, 2, v___x_1673_);
v___x_1675_ = 1;
lean_inc_ref(v___x_1674_);
v___x_1676_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(v_snd_1670_, v_00_u03c3s_1346_, v___x_1674_, v___x_1675_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec_ref_known(v___x_1676_, 1);
v___x_1677_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1674_);
lean_inc(v_a_1353_);
lean_inc_ref(v_a_1352_);
lean_inc(v_a_1351_);
lean_inc_ref(v_a_1350_);
v___x_1678_ = lean_apply_6(v_k_1349_, v___x_1677_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, lean_box(0));
return v___x_1678_;
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref_known(v___x_1674_, 3);
lean_dec_ref(v_k_1349_);
v_a_1679_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1676_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1676_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_snd_1670_);
lean_dec(v_fst_1669_);
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
v_a_1687_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1671_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1671_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v_k_1349_);
lean_dec_ref(v_H_1347_);
lean_dec_ref(v_00_u03c3s_1346_);
v_a_1695_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1667_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1667_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___lam__2(lean_object* v___x_1703_, lean_object* v_tail_1704_, lean_object* v_u_1705_, lean_object* v___x_1706_, lean_object* v_k_1707_, lean_object* v_x_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_mk_empty_array_with_capacity(v___x_1714_);
v___x_1716_ = lean_array_push(v___x_1715_, v_x_1708_);
v___x_1717_ = 0;
v___x_1718_ = l_Lean_Expr_betaRev(v___x_1703_, v___x_1716_, v___x_1717_, v___x_1717_);
lean_dec_ref(v___x_1716_);
v___x_1719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1719_, 0, v_tail_1704_);
v___x_1720_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1705_, v___x_1706_, v___x_1718_, v___x_1719_, v_k_1707_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg___boxed(lean_object* v_u_1721_, lean_object* v_00_u03c3s_1722_, lean_object* v_H_1723_, lean_object* v_pat_1724_, lean_object* v_k_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1721_, v_00_u03c3s_1722_, v_H_1723_, v_pat_1724_, v_k_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(lean_object* v_00_u03b1_1732_, lean_object* v_u_1733_, lean_object* v_00_u03c3s_1734_, lean_object* v_H_1735_, lean_object* v_pat_1736_, lean_object* v_k_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_1733_, v_00_u03c3s_1734_, v_H_1735_, v_pat_1736_, v_k_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___boxed(lean_object* v_00_u03b1_1744_, lean_object* v_u_1745_, lean_object* v_00_u03c3s_1746_, lean_object* v_H_1747_, lean_object* v_pat_1748_, lean_object* v_k_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore(v_00_u03b1_1744_, v_u_1745_, v_00_u03c3s_1746_, v_H_1747_, v_pat_1748_, v_k_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(lean_object* v_00_u03b1_1756_, lean_object* v_00_u03c3s_1757_, lean_object* v_hyp_1758_, lean_object* v_name_1759_, lean_object* v_k_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___redArg(v_00_u03c3s_1757_, v_hyp_1758_, v_name_1759_, v_k_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_00_u03c3s_1768_, lean_object* v_hyp_1769_, lean_object* v_name_1770_, lean_object* v_k_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Elab_Tactic_Do_ProofMode_mPureCore___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__1(v_00_u03b1_1767_, v_00_u03c3s_1768_, v_hyp_1769_, v_name_1770_, v_k_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg(){
_start:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mCasesCore_spec__0___redArg___closed__0);
v___x_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg___boxed(lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(lean_object* v_00_u03b1_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___boxed(lean_object* v_00_u03b1_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0(v_00_u03b1_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec_ref(v___y_1797_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(lean_object* v_x_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v___x_1815_; 
lean_inc(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc(v___y_1807_);
lean_inc_ref(v___y_1806_);
v___x_1815_ = lean_apply_9(v_x_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, lean_box(0));
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed(lean_object* v_x_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0(v_x_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(lean_object* v_mvarId_1827_, lean_object* v_x_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___f_1838_; lean_object* v___x_1839_; 
lean_inc(v___y_1832_);
lean_inc_ref(v___y_1831_);
lean_inc(v___y_1830_);
lean_inc_ref(v___y_1829_);
v___f_1838_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_1838_, 0, v_x_1828_);
lean_closure_set(v___f_1838_, 1, v___y_1829_);
lean_closure_set(v___f_1838_, 2, v___y_1830_);
lean_closure_set(v___f_1838_, 3, v___y_1831_);
lean_closure_set(v___f_1838_, 4, v___y_1832_);
v___x_1839_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1827_, v___f_1838_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1839_) == 0)
{
return v___x_1839_;
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg___boxed(lean_object* v_mvarId_1848_, lean_object* v_x_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1848_, v_x_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v___y_1853_);
lean_dec_ref(v___y_1852_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(lean_object* v_00_u03b1_1860_, lean_object* v_mvarId_1861_, lean_object* v_x_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_mvarId_1861_, v_x_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___boxed(lean_object* v_00_u03b1_1873_, lean_object* v_mvarId_1874_, lean_object* v_x_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3(v_00_u03b1_1873_, v_mvarId_1874_, v_x_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v_ks_1890_; lean_object* v_vs_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1915_; 
v_ks_1890_ = lean_ctor_get(v_x_1886_, 0);
v_vs_1891_ = lean_ctor_get(v_x_1886_, 1);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_x_1886_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1893_ = v_x_1886_;
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_vs_1891_);
lean_inc(v_ks_1890_);
lean_dec(v_x_1886_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1915_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = lean_array_get_size(v_ks_1890_);
v___x_1896_ = lean_nat_dec_lt(v_x_1887_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
lean_dec(v_x_1887_);
v___x_1897_ = lean_array_push(v_ks_1890_, v_x_1888_);
v___x_1898_ = lean_array_push(v_vs_1891_, v_x_1889_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v___x_1898_);
lean_ctor_set(v___x_1893_, 0, v___x_1897_);
v___x_1900_ = v___x_1893_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1897_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
lean_object* v_k_x27_1902_; uint8_t v___x_1903_; 
v_k_x27_1902_ = lean_array_fget_borrowed(v_ks_1890_, v_x_1887_);
v___x_1903_ = l_Lean_instBEqMVarId_beq(v_x_1888_, v_k_x27_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1905_; 
if (v_isShared_1894_ == 0)
{
v___x_1905_ = v___x_1893_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_ks_1890_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_vs_1891_);
v___x_1905_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_unsigned_to_nat(1u);
v___x_1907_ = lean_nat_add(v_x_1887_, v___x_1906_);
lean_dec(v_x_1887_);
v_x_1886_ = v___x_1905_;
v_x_1887_ = v___x_1907_;
goto _start;
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1910_ = lean_array_fset(v_ks_1890_, v_x_1887_, v_x_1888_);
v___x_1911_ = lean_array_fset(v_vs_1891_, v_x_1887_, v_x_1889_);
lean_dec(v_x_1887_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v___x_1911_);
lean_ctor_set(v___x_1893_, 0, v___x_1910_);
v___x_1913_ = v___x_1893_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1910_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(lean_object* v_n_1916_, lean_object* v_k_1917_, lean_object* v_v_1918_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_n_1916_, v___x_1919_, v_k_1917_, v_v_1918_);
return v___x_1920_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(lean_object* v_x_1922_, size_t v_x_1923_, size_t v_x_1924_, lean_object* v_x_1925_, lean_object* v_x_1926_){
_start:
{
if (lean_obj_tag(v_x_1922_) == 0)
{
lean_object* v_es_1927_; size_t v___x_1928_; size_t v___x_1929_; lean_object* v_j_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_es_1927_ = lean_ctor_get(v_x_1922_, 0);
v___x_1928_ = ((size_t)31ULL);
v___x_1929_ = lean_usize_land(v_x_1923_, v___x_1928_);
v_j_1930_ = lean_usize_to_nat(v___x_1929_);
v___x_1931_ = lean_array_get_size(v_es_1927_);
v___x_1932_ = lean_nat_dec_lt(v_j_1930_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_dec(v_j_1930_);
lean_dec(v_x_1926_);
lean_dec(v_x_1925_);
return v_x_1922_;
}
else
{
lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1971_; 
lean_inc_ref(v_es_1927_);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_x_1922_);
if (v_isSharedCheck_1971_ == 0)
{
lean_object* v_unused_1972_; 
v_unused_1972_ = lean_ctor_get(v_x_1922_, 0);
lean_dec(v_unused_1972_);
v___x_1934_ = v_x_1922_;
v_isShared_1935_ = v_isSharedCheck_1971_;
goto v_resetjp_1933_;
}
else
{
lean_dec(v_x_1922_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1971_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_v_1936_; lean_object* v___x_1937_; lean_object* v_xs_x27_1938_; lean_object* v___y_1940_; 
v_v_1936_ = lean_array_fget(v_es_1927_, v_j_1930_);
v___x_1937_ = lean_box(0);
v_xs_x27_1938_ = lean_array_fset(v_es_1927_, v_j_1930_, v___x_1937_);
switch(lean_obj_tag(v_v_1936_))
{
case 0:
{
lean_object* v_key_1945_; lean_object* v_val_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1956_; 
v_key_1945_ = lean_ctor_get(v_v_1936_, 0);
v_val_1946_ = lean_ctor_get(v_v_1936_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_v_1936_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1948_ = v_v_1936_;
v_isShared_1949_ = v_isSharedCheck_1956_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_val_1946_);
lean_inc(v_key_1945_);
lean_dec(v_v_1936_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1956_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
uint8_t v___x_1950_; 
v___x_1950_ = l_Lean_instBEqMVarId_beq(v_x_1925_, v_key_1945_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_del_object(v___x_1948_);
v___x_1951_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1945_, v_val_1946_, v_x_1925_, v_x_1926_);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___y_1940_ = v___x_1952_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_1954_; 
lean_dec(v_val_1946_);
lean_dec(v_key_1945_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v_x_1926_);
lean_ctor_set(v___x_1948_, 0, v_x_1925_);
v___x_1954_ = v___x_1948_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_x_1925_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_x_1926_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
v___y_1940_ = v___x_1954_;
goto v___jp_1939_;
}
}
}
}
case 1:
{
lean_object* v_node_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1969_; 
v_node_1957_ = lean_ctor_get(v_v_1936_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_v_1936_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1959_ = v_v_1936_;
v_isShared_1960_ = v_isSharedCheck_1969_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_node_1957_);
lean_dec(v_v_1936_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1969_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
size_t v___x_1961_; size_t v___x_1962_; size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1961_ = ((size_t)5ULL);
v___x_1962_ = lean_usize_shift_right(v_x_1923_, v___x_1961_);
v___x_1963_ = ((size_t)1ULL);
v___x_1964_ = lean_usize_add(v_x_1924_, v___x_1963_);
v___x_1965_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_node_1957_, v___x_1962_, v___x_1964_, v_x_1925_, v_x_1926_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 0, v___x_1965_);
v___x_1967_ = v___x_1959_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
v___y_1940_ = v___x_1967_;
goto v___jp_1939_;
}
}
}
default: 
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_x_1925_);
lean_ctor_set(v___x_1970_, 1, v_x_1926_);
v___y_1940_ = v___x_1970_;
goto v___jp_1939_;
}
}
v___jp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = lean_array_fset(v_xs_x27_1938_, v_j_1930_, v___y_1940_);
lean_dec(v_j_1930_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v___x_1941_);
v___x_1943_ = v___x_1934_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
}
else
{
lean_object* v_ks_1973_; lean_object* v_vs_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_1992_; 
v_ks_1973_ = lean_ctor_get(v_x_1922_, 0);
v_vs_1974_ = lean_ctor_get(v_x_1922_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_x_1922_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1976_ = v_x_1922_;
v_isShared_1977_ = v_isSharedCheck_1992_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_vs_1974_);
lean_inc(v_ks_1973_);
lean_dec(v_x_1922_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_1992_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_ks_1973_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_vs_1974_);
v___x_1979_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v_newNode_1980_; size_t v___x_1981_; uint8_t v___x_1982_; 
v_newNode_1980_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v___x_1979_, v_x_1925_, v_x_1926_);
v___x_1981_ = ((size_t)7ULL);
v___x_1982_ = lean_usize_dec_le(v___x_1981_, v_x_1924_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1983_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1980_);
v___x_1984_ = lean_unsigned_to_nat(4u);
v___x_1985_ = lean_nat_dec_lt(v___x_1983_, v___x_1984_);
lean_dec(v___x_1983_);
if (v___x_1985_ == 0)
{
lean_object* v_ks_1986_; lean_object* v_vs_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_ks_1986_ = lean_ctor_get(v_newNode_1980_, 0);
lean_inc_ref(v_ks_1986_);
v_vs_1987_ = lean_ctor_get(v_newNode_1980_, 1);
lean_inc_ref(v_vs_1987_);
lean_dec_ref(v_newNode_1980_);
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___closed__0);
v___x_1990_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_x_1924_, v_ks_1986_, v_vs_1987_, v___x_1988_, v___x_1989_);
lean_dec_ref(v_vs_1987_);
lean_dec_ref(v_ks_1986_);
return v___x_1990_;
}
else
{
return v_newNode_1980_;
}
}
else
{
return v_newNode_1980_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(size_t v_depth_1993_, lean_object* v_keys_1994_, lean_object* v_vals_1995_, lean_object* v_i_1996_, lean_object* v_entries_1997_){
_start:
{
lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1998_ = lean_array_get_size(v_keys_1994_);
v___x_1999_ = lean_nat_dec_lt(v_i_1996_, v___x_1998_);
if (v___x_1999_ == 0)
{
lean_dec(v_i_1996_);
return v_entries_1997_;
}
else
{
lean_object* v_k_2000_; lean_object* v_v_2001_; uint64_t v___x_2002_; size_t v_h_2003_; size_t v___x_2004_; lean_object* v___x_2005_; size_t v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; size_t v_h_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_k_2000_ = lean_array_fget_borrowed(v_keys_1994_, v_i_1996_);
v_v_2001_ = lean_array_fget_borrowed(v_vals_1995_, v_i_1996_);
v___x_2002_ = l_Lean_instHashableMVarId_hash(v_k_2000_);
v_h_2003_ = lean_uint64_to_usize(v___x_2002_);
v___x_2004_ = ((size_t)5ULL);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = ((size_t)1ULL);
v___x_2007_ = lean_usize_sub(v_depth_1993_, v___x_2006_);
v___x_2008_ = lean_usize_mul(v___x_2004_, v___x_2007_);
v_h_2009_ = lean_usize_shift_right(v_h_2003_, v___x_2008_);
v___x_2010_ = lean_nat_add(v_i_1996_, v___x_2005_);
lean_dec(v_i_1996_);
lean_inc(v_v_2001_);
lean_inc(v_k_2000_);
v___x_2011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_entries_1997_, v_h_2009_, v_depth_1993_, v_k_2000_, v_v_2001_);
v_i_1996_ = v___x_2010_;
v_entries_1997_ = v___x_2011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg___boxed(lean_object* v_depth_2013_, lean_object* v_keys_2014_, lean_object* v_vals_2015_, lean_object* v_i_2016_, lean_object* v_entries_2017_){
_start:
{
size_t v_depth_boxed_2018_; lean_object* v_res_2019_; 
v_depth_boxed_2018_ = lean_unbox_usize(v_depth_2013_);
lean_dec(v_depth_2013_);
v_res_2019_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_boxed_2018_, v_keys_2014_, v_vals_2015_, v_i_2016_, v_entries_2017_);
lean_dec_ref(v_vals_2015_);
lean_dec_ref(v_keys_2014_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg___boxed(lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
size_t v_x_19448__boxed_2025_; size_t v_x_19449__boxed_2026_; lean_object* v_res_2027_; 
v_x_19448__boxed_2025_ = lean_unbox_usize(v_x_2021_);
lean_dec(v_x_2021_);
v_x_19449__boxed_2026_ = lean_unbox_usize(v_x_2022_);
lean_dec(v_x_2022_);
v_res_2027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2020_, v_x_19448__boxed_2025_, v_x_19449__boxed_2026_, v_x_2023_, v_x_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
uint64_t v___x_2031_; size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2031_ = l_Lean_instHashableMVarId_hash(v_x_2029_);
v___x_2032_ = lean_uint64_to_usize(v___x_2031_);
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_2028_, v___x_2032_, v___x_2033_, v_x_2029_, v_x_2030_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(lean_object* v_mvarId_2035_, lean_object* v_val_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v___x_2039_; lean_object* v_mctx_2040_; lean_object* v_cache_2041_; lean_object* v_zetaDeltaFVarIds_2042_; lean_object* v_postponed_2043_; lean_object* v_diag_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2073_; 
v___x_2039_ = lean_st_ref_take(v___y_2037_);
v_mctx_2040_ = lean_ctor_get(v___x_2039_, 0);
v_cache_2041_ = lean_ctor_get(v___x_2039_, 1);
v_zetaDeltaFVarIds_2042_ = lean_ctor_get(v___x_2039_, 2);
v_postponed_2043_ = lean_ctor_get(v___x_2039_, 3);
v_diag_2044_ = lean_ctor_get(v___x_2039_, 4);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2046_ = v___x_2039_;
v_isShared_2047_ = v_isSharedCheck_2073_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_diag_2044_);
lean_inc(v_postponed_2043_);
lean_inc(v_zetaDeltaFVarIds_2042_);
lean_inc(v_cache_2041_);
lean_inc(v_mctx_2040_);
lean_dec(v___x_2039_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2073_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v_depth_2048_; lean_object* v_levelAssignDepth_2049_; lean_object* v_lmvarCounter_2050_; lean_object* v_mvarCounter_2051_; lean_object* v_lDecls_2052_; lean_object* v_decls_2053_; lean_object* v_userNames_2054_; lean_object* v_lAssignment_2055_; lean_object* v_eAssignment_2056_; lean_object* v_dAssignment_2057_; lean_object* v_instanceTypedMVars_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2072_; 
v_depth_2048_ = lean_ctor_get(v_mctx_2040_, 0);
v_levelAssignDepth_2049_ = lean_ctor_get(v_mctx_2040_, 1);
v_lmvarCounter_2050_ = lean_ctor_get(v_mctx_2040_, 2);
v_mvarCounter_2051_ = lean_ctor_get(v_mctx_2040_, 3);
v_lDecls_2052_ = lean_ctor_get(v_mctx_2040_, 4);
v_decls_2053_ = lean_ctor_get(v_mctx_2040_, 5);
v_userNames_2054_ = lean_ctor_get(v_mctx_2040_, 6);
v_lAssignment_2055_ = lean_ctor_get(v_mctx_2040_, 7);
v_eAssignment_2056_ = lean_ctor_get(v_mctx_2040_, 8);
v_dAssignment_2057_ = lean_ctor_get(v_mctx_2040_, 9);
v_instanceTypedMVars_2058_ = lean_ctor_get(v_mctx_2040_, 10);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_mctx_2040_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2060_ = v_mctx_2040_;
v_isShared_2061_ = v_isSharedCheck_2072_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_instanceTypedMVars_2058_);
lean_inc(v_dAssignment_2057_);
lean_inc(v_eAssignment_2056_);
lean_inc(v_lAssignment_2055_);
lean_inc(v_userNames_2054_);
lean_inc(v_decls_2053_);
lean_inc(v_lDecls_2052_);
lean_inc(v_mvarCounter_2051_);
lean_inc(v_lmvarCounter_2050_);
lean_inc(v_levelAssignDepth_2049_);
lean_inc(v_depth_2048_);
lean_dec(v_mctx_2040_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2072_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2062_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_eAssignment_2056_, v_mvarId_2035_, v_val_2036_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 8, v___x_2062_);
v___x_2064_ = v___x_2060_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_depth_2048_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_levelAssignDepth_2049_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_lmvarCounter_2050_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_mvarCounter_2051_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_lDecls_2052_);
lean_ctor_set(v_reuseFailAlloc_2071_, 5, v_decls_2053_);
lean_ctor_set(v_reuseFailAlloc_2071_, 6, v_userNames_2054_);
lean_ctor_set(v_reuseFailAlloc_2071_, 7, v_lAssignment_2055_);
lean_ctor_set(v_reuseFailAlloc_2071_, 8, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2071_, 9, v_dAssignment_2057_);
lean_ctor_set(v_reuseFailAlloc_2071_, 10, v_instanceTypedMVars_2058_);
v___x_2064_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2066_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2064_);
v___x_2066_ = v___x_2046_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_cache_2041_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v_zetaDeltaFVarIds_2042_);
lean_ctor_set(v_reuseFailAlloc_2070_, 3, v_postponed_2043_);
lean_ctor_set(v_reuseFailAlloc_2070_, 4, v_diag_2044_);
v___x_2066_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_st_ref_put(v___y_2037_, v___x_2066_);
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg___boxed(lean_object* v_mvarId_2074_, lean_object* v_val_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_2074_, v_val_2075_, v___y_2076_);
lean_dec(v___y_2076_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(lean_object* v_snd_2081_, lean_object* v_hyp_2082_, lean_object* v_a_2083_, lean_object* v_fst_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
lean_inc_ref(v_snd_2081_);
v___x_2094_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(v_snd_2081_, v_hyp_2082_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_focusHyp_2098_; lean_object* v_restHyps_2099_; lean_object* v_u_2100_; lean_object* v_00_u03c3s_2101_; lean_object* v_target_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___closed__0));
v___x_2097_ = lean_st_mk_ref(v___x_2096_);
v_focusHyp_2098_ = lean_ctor_get(v_a_2095_, 0);
v_restHyps_2099_ = lean_ctor_get(v_a_2095_, 1);
v_u_2100_ = lean_ctor_get(v_snd_2081_, 0);
v_00_u03c3s_2101_ = lean_ctor_get(v_snd_2081_, 1);
v_target_2102_ = lean_ctor_get(v_snd_2081_, 3);
lean_inc_ref(v_restHyps_2099_);
lean_inc_ref(v_target_2102_);
lean_inc_ref_n(v_00_u03c3s_2101_, 2);
lean_inc(v___x_2097_);
lean_inc_n(v_u_2100_, 2);
v___x_2103_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mCasesAddGoal___boxed), 11, 5);
lean_closure_set(v___x_2103_, 0, v_u_2100_);
lean_closure_set(v___x_2103_, 1, v___x_2097_);
lean_closure_set(v___x_2103_, 2, v_00_u03c3s_2101_);
lean_closure_set(v___x_2103_, 3, v_target_2102_);
lean_closure_set(v___x_2103_, 4, v_restHyps_2099_);
lean_inc_ref(v_focusHyp_2098_);
v___x_2104_ = l_Lean_Elab_Tactic_Do_ProofMode_mCasesCore___redArg(v_u_2100_, v_00_u03c3s_2101_, v_focusHyp_2098_, v_a_2083_, v___x_2103_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v_snd_2106_; lean_object* v_snd_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v_snd_2106_ = lean_ctor_get(v_a_2105_, 1);
lean_inc(v_snd_2106_);
lean_dec(v_a_2105_);
v_snd_2107_ = lean_ctor_get(v_snd_2106_, 1);
lean_inc(v_snd_2107_);
lean_dec(v_snd_2106_);
v___x_2108_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(v_a_2095_, v_snd_2081_, v_snd_2107_);
v___x_2109_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_fst_2084_, v___x_2108_, v___y_2090_);
lean_dec_ref(v___x_2109_);
v___x_2110_ = lean_st_ref_get(v___x_2097_);
lean_dec(v___x_2097_);
v___x_2111_ = lean_array_to_list(v___x_2110_);
v___x_2112_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_2111_, v___y_2086_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
return v___x_2112_;
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v___x_2097_);
lean_dec(v_a_2095_);
lean_dec(v_fst_2084_);
lean_dec_ref(v_snd_2081_);
v_a_2113_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2104_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2104_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_fst_2084_);
lean_dec(v_a_2083_);
lean_dec_ref(v_snd_2081_);
v_a_2121_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2094_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2094_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed(lean_object* v_snd_2129_, lean_object* v_hyp_2130_, lean_object* v_a_2131_, lean_object* v_fst_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0(v_snd_2129_, v_hyp_2130_, v_a_2131_, v_fst_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2142_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2143_; double v___x_2144_; 
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_float_of_nat(v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(lean_object* v_cls_2148_, lean_object* v_msg_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_ref_2155_; lean_object* v___x_2156_; lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2201_; 
v_ref_2155_ = lean_ctor_get(v___y_2152_, 2);
v___x_2156_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2201_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2201_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v_traceState_2162_; lean_object* v_env_2163_; lean_object* v_nextMacroScope_2164_; lean_object* v_ngen_2165_; lean_object* v_auxDeclNGen_2166_; lean_object* v_cache_2167_; lean_object* v_messages_2168_; lean_object* v_infoState_2169_; lean_object* v_snapshotTasks_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2200_; 
v___x_2161_ = lean_st_ref_take(v___y_2153_);
v_traceState_2162_ = lean_ctor_get(v___x_2161_, 4);
v_env_2163_ = lean_ctor_get(v___x_2161_, 0);
v_nextMacroScope_2164_ = lean_ctor_get(v___x_2161_, 1);
v_ngen_2165_ = lean_ctor_get(v___x_2161_, 2);
v_auxDeclNGen_2166_ = lean_ctor_get(v___x_2161_, 3);
v_cache_2167_ = lean_ctor_get(v___x_2161_, 5);
v_messages_2168_ = lean_ctor_get(v___x_2161_, 6);
v_infoState_2169_ = lean_ctor_get(v___x_2161_, 7);
v_snapshotTasks_2170_ = lean_ctor_get(v___x_2161_, 8);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2172_ = v___x_2161_;
v_isShared_2173_ = v_isSharedCheck_2200_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_snapshotTasks_2170_);
lean_inc(v_infoState_2169_);
lean_inc(v_messages_2168_);
lean_inc(v_cache_2167_);
lean_inc(v_traceState_2162_);
lean_inc(v_auxDeclNGen_2166_);
lean_inc(v_ngen_2165_);
lean_inc(v_nextMacroScope_2164_);
lean_inc(v_env_2163_);
lean_dec(v___x_2161_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2200_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
uint64_t v_tid_2174_; lean_object* v_traces_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2199_; 
v_tid_2174_ = lean_ctor_get_uint64(v_traceState_2162_, sizeof(void*)*1);
v_traces_2175_ = lean_ctor_get(v_traceState_2162_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_traceState_2162_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2177_ = v_traceState_2162_;
v_isShared_2178_ = v_isSharedCheck_2199_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_traces_2175_);
lean_dec(v_traceState_2162_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2199_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; double v___x_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__0);
v___x_2181_ = 0;
v___x_2182_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2183_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2183_, 0, v_cls_2148_);
lean_ctor_set(v___x_2183_, 1, v___x_2179_);
lean_ctor_set(v___x_2183_, 2, v___x_2182_);
lean_ctor_set_float(v___x_2183_, sizeof(void*)*3, v___x_2180_);
lean_ctor_set_float(v___x_2183_, sizeof(void*)*3 + 8, v___x_2180_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*3 + 16, v___x_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__2));
v___x_2185_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v_a_2157_);
lean_ctor_set(v___x_2185_, 2, v___x_2184_);
lean_inc(v_ref_2155_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_ref_2155_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_PersistentArray_push___redArg(v_traces_2175_, v___x_2186_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2187_);
v___x_2189_ = v___x_2177_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2187_);
lean_ctor_set_uint64(v_reuseFailAlloc_2198_, sizeof(void*)*1, v_tid_2174_);
v___x_2189_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 4, v___x_2189_);
v___x_2191_ = v___x_2172_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_env_2163_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_nextMacroScope_2164_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_ngen_2165_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_auxDeclNGen_2166_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2197_, 5, v_cache_2167_);
lean_ctor_set(v_reuseFailAlloc_2197_, 6, v_messages_2168_);
lean_ctor_set(v_reuseFailAlloc_2197_, 7, v_infoState_2169_);
lean_ctor_set(v_reuseFailAlloc_2197_, 8, v_snapshotTasks_2170_);
v___x_2191_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = lean_st_ref_put(v___y_2153_, v___x_2191_);
v___x_2193_ = lean_box(0);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2193_);
v___x_2195_ = v___x_2159_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___boxed(lean_object* v_cls_2202_, lean_object* v_msg_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2202_, v_msg_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(lean_object* v_as_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
if (lean_obj_tag(v_as_2213_) == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_box(0);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
else
{
lean_object* v_toCold_2225_; lean_object* v_options_2226_; uint8_t v_hasTrace_2227_; 
v_toCold_2225_ = lean_ctor_get(v___y_2220_, 0);
v_options_2226_ = lean_ctor_get(v_toCold_2225_, 2);
v_hasTrace_2227_ = lean_ctor_get_uint8(v_options_2226_, sizeof(void*)*1);
if (v_hasTrace_2227_ == 0)
{
lean_object* v_tail_2228_; 
v_tail_2228_ = lean_ctor_get(v_as_2213_, 1);
lean_inc(v_tail_2228_);
lean_dec_ref_known(v_as_2213_, 2);
v_as_2213_ = v_tail_2228_;
goto _start;
}
else
{
lean_object* v_head_2230_; lean_object* v_tail_2231_; lean_object* v_fst_2232_; lean_object* v_snd_2233_; lean_object* v_inheritedTraceOptions_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v_head_2230_ = lean_ctor_get(v_as_2213_, 0);
lean_inc(v_head_2230_);
v_tail_2231_ = lean_ctor_get(v_as_2213_, 1);
lean_inc(v_tail_2231_);
lean_dec_ref_known(v_as_2213_, 2);
v_fst_2232_ = lean_ctor_get(v_head_2230_, 0);
lean_inc_n(v_fst_2232_, 2);
v_snd_2233_ = lean_ctor_get(v_head_2230_, 1);
lean_inc(v_snd_2233_);
lean_dec(v_head_2230_);
v_inheritedTraceOptions_2234_ = lean_ctor_get(v_toCold_2225_, 11);
v___x_2235_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2236_ = l_Lean_Name_append(v___x_2235_, v_fst_2232_);
v___x_2237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2234_, v_options_2226_, v___x_2236_);
lean_dec(v___x_2236_);
if (v___x_2237_ == 0)
{
lean_dec(v_snd_2233_);
lean_dec(v_fst_2232_);
v_as_2213_ = v_tail_2231_;
goto _start;
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2239_, 0, v_snd_2233_);
v___x_2240_ = l_Lean_MessageData_ofFormat(v___x_2239_);
v___x_2241_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_fst_2232_, v___x_2240_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_dec_ref_known(v___x_2241_, 1);
v_as_2213_ = v_tail_2231_;
goto _start;
}
else
{
lean_dec(v_tail_2231_);
return v___x_2241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___boxed(lean_object* v_as_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v_as_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(lean_object* v_x_2254_, lean_object* v___y_2255_){
_start:
{
if (lean_obj_tag(v_x_2254_) == 0)
{
lean_object* v_a_2256_; lean_object* v___x_2257_; 
v_a_2256_ = lean_ctor_get(v_x_2254_, 0);
lean_inc(v_a_2256_);
v___x_2257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2257_, 0, v_a_2256_);
lean_ctor_set(v___x_2257_, 1, v___y_2255_);
return v___x_2257_;
}
else
{
lean_object* v_a_2258_; lean_object* v___x_2259_; 
v_a_2258_ = lean_ctor_get(v_x_2254_, 0);
lean_inc(v_a_2258_);
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v_a_2258_);
lean_ctor_set(v___x_2259_, 1, v___y_2255_);
return v___x_2259_;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg___boxed(lean_object* v_x_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_2260_, v___y_2261_);
lean_dec_ref(v_x_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(lean_object* v_env_2263_, lean_object* v_stx_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Elab_expandMacroImpl_x3f(v_env_2263_, v_stx_2264_, v___y_2265_, v___y_2266_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
if (lean_obj_tag(v_a_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2277_; 
v_a_2269_ = lean_ctor_get(v___x_2267_, 1);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; 
v_unused_2278_ = lean_ctor_get(v___x_2267_, 0);
lean_dec(v_unused_2278_);
v___x_2271_ = v___x_2267_;
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2267_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2277_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2273_ = lean_box(0);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2273_);
v___x_2275_ = v___x_2271_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_a_2269_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
else
{
lean_object* v_val_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2307_; 
v_val_2279_ = lean_ctor_get(v_a_2268_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v_a_2268_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2281_ = v_a_2268_;
v_isShared_2282_ = v_isSharedCheck_2307_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_val_2279_);
lean_dec(v_a_2268_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2307_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_snd_2283_; 
v_snd_2283_ = lean_ctor_get(v_val_2279_, 1);
lean_inc(v_snd_2283_);
lean_dec(v_val_2279_);
if (lean_obj_tag(v_snd_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2293_; 
lean_del_object(v___x_2281_);
v_a_2284_ = lean_ctor_get(v___x_2267_, 1);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2267_, 2);
v_a_2285_ = lean_ctor_get(v_snd_2283_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_snd_2283_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2287_ = v_snd_2283_;
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v_snd_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2293_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2290_, v_a_2284_);
lean_dec_ref(v___x_2290_);
return v___x_2291_;
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2306_; 
v_a_2294_ = lean_ctor_get(v___x_2267_, 1);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2267_, 2);
v_a_2295_ = lean_ctor_get(v_snd_2283_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_snd_2283_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2297_ = v_snd_2283_;
v_isShared_2298_ = v_isSharedCheck_2306_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v_snd_2283_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2306_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v___x_2300_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v_a_2295_);
v___x_2300_ = v___x_2281_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2295_);
v___x_2300_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2302_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2300_);
v___x_2302_ = v___x_2297_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; 
v___x_2303_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v___x_2302_, v_a_2294_);
lean_dec_ref(v___x_2302_);
return v___x_2303_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
v_a_2308_ = lean_ctor_get(v___x_2267_, 0);
v_a_2309_ = lean_ctor_get(v___x_2267_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2267_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_inc(v_a_2308_);
lean_dec(v___x_2267_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2308_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed(lean_object* v_env_2317_, lean_object* v_stx_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0(v_env_2317_, v_stx_2318_, v___y_2319_, v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(lean_object* v_msg_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_ref_2328_; lean_object* v___x_2329_; lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2338_; 
v_ref_2328_ = lean_ctor_get(v___y_2325_, 2);
v___x_2329_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_getQH_spec__0_spec__0(v_msg_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2338_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2336_; 
lean_inc(v_ref_2328_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_ref_2328_);
lean_ctor_set(v___x_2334_, 1, v_a_2330_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set_tag(v___x_2332_, 1);
lean_ctor_set(v___x_2332_, 0, v___x_2334_);
v___x_2336_ = v___x_2332_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_msg_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(lean_object* v_ref_2346_, lean_object* v_msg_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v_toCold_2357_; lean_object* v_currRecDepth_2358_; lean_object* v_ref_2359_; uint8_t v_diag_2360_; uint8_t v_suppressElabErrors_2361_; lean_object* v_ref_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v_toCold_2357_ = lean_ctor_get(v___y_2354_, 0);
v_currRecDepth_2358_ = lean_ctor_get(v___y_2354_, 1);
v_ref_2359_ = lean_ctor_get(v___y_2354_, 2);
v_diag_2360_ = lean_ctor_get_uint8(v___y_2354_, sizeof(void*)*3);
v_suppressElabErrors_2361_ = lean_ctor_get_uint8(v___y_2354_, sizeof(void*)*3 + 1);
v_ref_2362_ = l_Lean_replaceRef(v_ref_2346_, v_ref_2359_);
lean_inc(v_currRecDepth_2358_);
lean_inc_ref(v_toCold_2357_);
v___x_2363_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2363_, 0, v_toCold_2357_);
lean_ctor_set(v___x_2363_, 1, v_currRecDepth_2358_);
lean_ctor_set(v___x_2363_, 2, v_ref_2362_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*3, v_diag_2360_);
lean_ctor_set_uint8(v___x_2363_, sizeof(void*)*3 + 1, v_suppressElabErrors_2361_);
v___x_2364_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_2347_, v___y_2352_, v___y_2353_, v___x_2363_, v___y_2355_);
lean_dec_ref_known(v___x_2363_, 3);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg___boxed(lean_object* v_ref_2365_, lean_object* v_msg_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_2365_, v_msg_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v_ref_2365_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(lean_object* v_env_2377_, lean_object* v_options_2378_, lean_object* v_currNamespace_2379_, lean_object* v_openDecls_2380_, lean_object* v_n_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = l_Lean_ResolveName_resolveGlobalName(v_env_2377_, v_options_2378_, v_currNamespace_2379_, v_openDecls_2380_, v_n_2381_);
v___x_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
lean_ctor_set(v___x_2385_, 1, v___y_2383_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed(lean_object* v_env_2386_, lean_object* v_options_2387_, lean_object* v_currNamespace_2388_, lean_object* v_openDecls_2389_, lean_object* v_n_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4(v_env_2386_, v_options_2387_, v_currNamespace_2388_, v_openDecls_2389_, v_n_2390_, v___y_2391_, v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec_ref(v_options_2387_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(lean_object* v_currNamespace_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2397_, 0, v_currNamespace_2394_);
lean_ctor_set(v___x_2397_, 1, v___y_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed(lean_object* v_currNamespace_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3(v_currNamespace_2398_, v___y_2399_, v___y_2400_);
lean_dec_ref(v___y_2399_);
return v_res_2401_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = l_Lean_maxRecDepthErrorMessage;
v___x_2408_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
return v___x_2408_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__3);
v___x_2410_ = l_Lean_MessageData_ofFormat(v___x_2409_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__4);
v___x_2412_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__2));
v___x_2413_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v___x_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(lean_object* v_ref_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___closed__5);
v___x_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2417_, 0, v_ref_2414_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg___boxed(lean_object* v_ref_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(lean_object* v_env_2422_, lean_object* v_currNamespace_2423_, lean_object* v_openDecls_2424_, lean_object* v_n_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = l_Lean_ResolveName_resolveNamespace(v_env_2422_, v_currNamespace_2423_, v_openDecls_2424_, v_n_2425_);
v___x_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v___y_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed(lean_object* v_env_2430_, lean_object* v_currNamespace_2431_, lean_object* v_openDecls_2432_, lean_object* v_n_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2(v_env_2430_, v_currNamespace_2431_, v_openDecls_2432_, v_n_2433_, v___y_2434_, v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2436_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(lean_object* v_keys_2437_, lean_object* v_i_2438_, lean_object* v_k_2439_){
_start:
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = lean_array_get_size(v_keys_2437_);
v___x_2441_ = lean_nat_dec_lt(v_i_2438_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_dec(v_i_2438_);
return v___x_2441_;
}
else
{
lean_object* v_k_x27_2442_; uint8_t v___x_2443_; 
v_k_x27_2442_ = lean_array_fget_borrowed(v_keys_2437_, v_i_2438_);
v___x_2443_ = l_Lean_instBEqExtraModUse_beq(v_k_2439_, v_k_x27_2442_);
if (v___x_2443_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_unsigned_to_nat(1u);
v___x_2445_ = lean_nat_add(v_i_2438_, v___x_2444_);
lean_dec(v_i_2438_);
v_i_2438_ = v___x_2445_;
goto _start;
}
else
{
lean_dec(v_i_2438_);
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg___boxed(lean_object* v_keys_2447_, lean_object* v_i_2448_, lean_object* v_k_2449_){
_start:
{
uint8_t v_res_2450_; lean_object* v_r_2451_; 
v_res_2450_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_2447_, v_i_2448_, v_k_2449_);
lean_dec_ref(v_k_2449_);
lean_dec_ref(v_keys_2447_);
v_r_2451_ = lean_box(v_res_2450_);
return v_r_2451_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(lean_object* v_x_2452_, size_t v_x_2453_, lean_object* v_x_2454_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 0)
{
lean_object* v_es_2455_; lean_object* v___x_2456_; size_t v___x_2457_; size_t v___x_2458_; lean_object* v_j_2459_; lean_object* v___x_2460_; 
v_es_2455_ = lean_ctor_get(v_x_2452_, 0);
v___x_2456_ = lean_box(2);
v___x_2457_ = ((size_t)31ULL);
v___x_2458_ = lean_usize_land(v_x_2453_, v___x_2457_);
v_j_2459_ = lean_usize_to_nat(v___x_2458_);
v___x_2460_ = lean_array_get_borrowed(v___x_2456_, v_es_2455_, v_j_2459_);
lean_dec(v_j_2459_);
switch(lean_obj_tag(v___x_2460_))
{
case 0:
{
lean_object* v_key_2461_; uint8_t v___x_2462_; 
v_key_2461_ = lean_ctor_get(v___x_2460_, 0);
v___x_2462_ = l_Lean_instBEqExtraModUse_beq(v_x_2454_, v_key_2461_);
return v___x_2462_;
}
case 1:
{
lean_object* v_node_2463_; size_t v___x_2464_; size_t v___x_2465_; 
v_node_2463_ = lean_ctor_get(v___x_2460_, 0);
v___x_2464_ = ((size_t)5ULL);
v___x_2465_ = lean_usize_shift_right(v_x_2453_, v___x_2464_);
v_x_2452_ = v_node_2463_;
v_x_2453_ = v___x_2465_;
goto _start;
}
default: 
{
uint8_t v___x_2467_; 
v___x_2467_ = 0;
return v___x_2467_;
}
}
}
else
{
lean_object* v_ks_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v_ks_2468_ = lean_ctor_get(v_x_2452_, 0);
v___x_2469_ = lean_unsigned_to_nat(0u);
v___x_2470_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_ks_2468_, v___x_2469_, v_x_2454_);
return v___x_2470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg___boxed(lean_object* v_x_2471_, lean_object* v_x_2472_, lean_object* v_x_2473_){
_start:
{
size_t v_x_20206__boxed_2474_; uint8_t v_res_2475_; lean_object* v_r_2476_; 
v_x_20206__boxed_2474_ = lean_unbox_usize(v_x_2472_);
lean_dec(v_x_2472_);
v_res_2475_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2471_, v_x_20206__boxed_2474_, v_x_2473_);
lean_dec_ref(v_x_2473_);
lean_dec_ref(v_x_2471_);
v_r_2476_ = lean_box(v_res_2475_);
return v_r_2476_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(lean_object* v_x_2477_, lean_object* v_x_2478_){
_start:
{
uint64_t v___x_2479_; size_t v___x_2480_; uint8_t v___x_2481_; 
v___x_2479_ = l_Lean_instHashableExtraModUse_hash(v_x_2478_);
v___x_2480_ = lean_uint64_to_usize(v___x_2479_);
v___x_2481_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_2477_, v___x_2480_, v_x_2478_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_x_2482_, lean_object* v_x_2483_){
_start:
{
uint8_t v_res_2484_; lean_object* v_r_2485_; 
v_res_2484_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_2482_, v_x_2483_);
lean_dec_ref(v_x_2483_);
lean_dec_ref(v_x_2482_);
v_r_2485_ = lean_box(v_res_2484_);
return v_r_2485_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__1));
v___x_2489_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__0));
v___x_2490_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2489_, v___x_2488_);
return v___x_2490_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3(void){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2491_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__3);
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
return v___x_2493_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2494_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
return v___x_2495_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__4);
v___x_2497_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
lean_ctor_set(v___x_2497_, 2, v___x_2496_);
lean_ctor_set(v___x_2497_, 3, v___x_2496_);
lean_ctor_set(v___x_2497_, 4, v___x_2496_);
lean_ctor_set(v___x_2497_, 5, v___x_2496_);
return v___x_2497_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__9));
v___x_2503_ = l_Lean_stringToMessageData(v___x_2502_);
return v___x_2503_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__11));
v___x_2506_ = l_Lean_stringToMessageData(v___x_2505_);
return v___x_2506_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg___closed__1));
v___x_2508_ = l_Lean_stringToMessageData(v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14(void){
_start:
{
lean_object* v_cls_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_cls_2509_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8));
v___x_2510_ = ((lean_object*)(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5___closed__1));
v___x_2511_ = l_Lean_Name_append(v___x_2510_, v_cls_2509_);
return v___x_2511_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__15));
v___x_2514_ = l_Lean_stringToMessageData(v___x_2513_);
return v___x_2514_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__17));
v___x_2517_ = l_Lean_stringToMessageData(v___x_2516_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(lean_object* v_mod_2522_, uint8_t v_isMeta_2523_, lean_object* v_hint_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v___x_2534_; lean_object* v_env_2535_; uint8_t v_isExporting_2536_; lean_object* v___x_2537_; lean_object* v_env_2538_; lean_object* v___x_2539_; lean_object* v_entry_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2534_ = lean_st_ref_get(v___y_2532_);
v_env_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_ref(v_env_2535_);
lean_dec(v___x_2534_);
v_isExporting_2536_ = lean_ctor_get_uint8(v_env_2535_, sizeof(void*)*8);
lean_dec_ref(v_env_2535_);
v___x_2537_ = lean_st_ref_get(v___y_2532_);
v_env_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc_ref(v_env_2538_);
lean_dec(v___x_2537_);
v___x_2539_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__2);
lean_inc(v_mod_2522_);
v_entry_2540_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2540_, 0, v_mod_2522_);
lean_ctor_set_uint8(v_entry_2540_, sizeof(void*)*1, v_isExporting_2536_);
lean_ctor_set_uint8(v_entry_2540_, sizeof(void*)*1 + 1, v_isMeta_2523_);
v___x_2541_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2542_ = lean_box(1);
v___x_2543_ = lean_box(0);
v___x_2586_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2539_, v___x_2541_, v_env_2538_, v___x_2542_, v___x_2543_);
v___x_2587_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v___x_2586_, v_entry_2540_);
lean_dec(v___x_2586_);
if (v___x_2587_ == 0)
{
lean_object* v_toCold_2588_; lean_object* v_options_2589_; uint8_t v_hasTrace_2590_; 
v_toCold_2588_ = lean_ctor_get(v___y_2531_, 0);
v_options_2589_ = lean_ctor_get(v_toCold_2588_, 2);
v_hasTrace_2590_ = lean_ctor_get_uint8(v_options_2589_, sizeof(void*)*1);
if (v_hasTrace_2590_ == 0)
{
lean_dec(v_hint_2524_);
lean_dec(v_mod_2522_);
v___y_2545_ = v___y_2530_;
v___y_2546_ = v___y_2532_;
goto v___jp_2544_;
}
else
{
lean_object* v_inheritedTraceOptions_2591_; lean_object* v_cls_2592_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___x_2612_; uint8_t v___x_2613_; 
v_inheritedTraceOptions_2591_ = lean_ctor_get(v_toCold_2588_, 11);
v_cls_2592_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__8));
v___x_2612_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__14);
v___x_2613_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2591_, v_options_2589_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_dec(v_hint_2524_);
lean_dec(v_mod_2522_);
v___y_2545_ = v___y_2530_;
v___y_2546_ = v___y_2532_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2614_; lean_object* v___y_2616_; 
v___x_2614_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__16);
if (v_isExporting_2536_ == 0)
{
lean_object* v___x_2623_; 
v___x_2623_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__21));
v___y_2616_ = v___x_2623_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2624_; 
v___x_2624_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__22));
v___y_2616_ = v___x_2624_;
goto v___jp_2615_;
}
v___jp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_inc_ref(v___y_2616_);
v___x_2617_ = l_Lean_stringToMessageData(v___y_2616_);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2614_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__18);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
if (v_isMeta_2523_ == 0)
{
lean_object* v___x_2621_; 
v___x_2621_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__19));
v___y_2599_ = v___x_2620_;
v___y_2600_ = v___x_2621_;
goto v___jp_2598_;
}
else
{
lean_object* v___x_2622_; 
v___x_2622_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__20));
v___y_2599_ = v___x_2620_;
v___y_2600_ = v___x_2622_;
goto v___jp_2598_;
}
}
}
v___jp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___y_2594_);
lean_ctor_set(v___x_2596_, 1, v___y_2595_);
v___x_2597_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_2592_, v___x_2596_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_dec_ref_known(v___x_2597_, 1);
v___y_2545_ = v___y_2530_;
v___y_2546_ = v___y_2532_;
goto v___jp_2544_;
}
else
{
lean_dec_ref_known(v_entry_2540_, 1);
return v___x_2597_;
}
}
v___jp_2598_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
lean_inc_ref(v___y_2600_);
v___x_2601_ = l_Lean_stringToMessageData(v___y_2600_);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___y_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__10);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l_Lean_MessageData_ofName(v_mod_2522_);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = l_Lean_Name_isAnonymous(v_hint_2524_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__12);
v___x_2609_ = l_Lean_MessageData_ofName(v_hint_2524_);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___y_2594_ = v___x_2606_;
v___y_2595_ = v___x_2610_;
goto v___jp_2593_;
}
else
{
lean_object* v___x_2611_; 
lean_dec(v_hint_2524_);
v___x_2611_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__13);
v___y_2594_ = v___x_2606_;
v___y_2595_ = v___x_2611_;
goto v___jp_2593_;
}
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref_known(v_entry_2540_, 1);
lean_dec(v_hint_2524_);
lean_dec(v_mod_2522_);
v___x_2625_ = lean_box(0);
v___x_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
v___jp_2544_:
{
lean_object* v___x_2547_; lean_object* v_toEnvExtension_2548_; lean_object* v_env_2549_; lean_object* v_nextMacroScope_2550_; lean_object* v_ngen_2551_; lean_object* v_auxDeclNGen_2552_; lean_object* v_traceState_2553_; lean_object* v_messages_2554_; lean_object* v_infoState_2555_; lean_object* v_snapshotTasks_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2584_; 
v___x_2547_ = lean_st_ref_take(v___y_2546_);
v_toEnvExtension_2548_ = lean_ctor_get(v___x_2541_, 0);
v_env_2549_ = lean_ctor_get(v___x_2547_, 0);
v_nextMacroScope_2550_ = lean_ctor_get(v___x_2547_, 1);
v_ngen_2551_ = lean_ctor_get(v___x_2547_, 2);
v_auxDeclNGen_2552_ = lean_ctor_get(v___x_2547_, 3);
v_traceState_2553_ = lean_ctor_get(v___x_2547_, 4);
v_messages_2554_ = lean_ctor_get(v___x_2547_, 6);
v_infoState_2555_ = lean_ctor_get(v___x_2547_, 7);
v_snapshotTasks_2556_ = lean_ctor_get(v___x_2547_, 8);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v___x_2547_, 5);
lean_dec(v_unused_2585_);
v___x_2558_ = v___x_2547_;
v_isShared_2559_ = v_isSharedCheck_2584_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_snapshotTasks_2556_);
lean_inc(v_infoState_2555_);
lean_inc(v_messages_2554_);
lean_inc(v_traceState_2553_);
lean_inc(v_auxDeclNGen_2552_);
lean_inc(v_ngen_2551_);
lean_inc(v_nextMacroScope_2550_);
lean_inc(v_env_2549_);
lean_dec(v___x_2547_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2584_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v_asyncMode_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2564_; 
v_asyncMode_2560_ = lean_ctor_get(v_toEnvExtension_2548_, 2);
v___x_2561_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2541_, v_env_2549_, v_entry_2540_, v_asyncMode_2560_, v___x_2543_);
v___x_2562_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__5);
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 5, v___x_2562_);
lean_ctor_set(v___x_2558_, 0, v___x_2561_);
v___x_2564_ = v___x_2558_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2561_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_nextMacroScope_2550_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_ngen_2551_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_auxDeclNGen_2552_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v_traceState_2553_);
lean_ctor_set(v_reuseFailAlloc_2583_, 5, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2583_, 6, v_messages_2554_);
lean_ctor_set(v_reuseFailAlloc_2583_, 7, v_infoState_2555_);
lean_ctor_set(v_reuseFailAlloc_2583_, 8, v_snapshotTasks_2556_);
v___x_2564_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v_mctx_2567_; lean_object* v_zetaDeltaFVarIds_2568_; lean_object* v_postponed_2569_; lean_object* v_diag_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2581_; 
v___x_2565_ = lean_st_ref_put(v___y_2546_, v___x_2564_);
v___x_2566_ = lean_st_ref_take(v___y_2545_);
v_mctx_2567_ = lean_ctor_get(v___x_2566_, 0);
v_zetaDeltaFVarIds_2568_ = lean_ctor_get(v___x_2566_, 2);
v_postponed_2569_ = lean_ctor_get(v___x_2566_, 3);
v_diag_2570_ = lean_ctor_get(v___x_2566_, 4);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v___x_2566_, 1);
lean_dec(v_unused_2582_);
v___x_2572_ = v___x_2566_;
v_isShared_2573_ = v_isSharedCheck_2581_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_diag_2570_);
lean_inc(v_postponed_2569_);
lean_inc(v_zetaDeltaFVarIds_2568_);
lean_inc(v_mctx_2567_);
lean_dec(v___x_2566_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2581_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2574_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___closed__6);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 1, v___x_2574_);
v___x_2576_ = v___x_2572_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_mctx_2567_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_zetaDeltaFVarIds_2568_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v_postponed_2569_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v_diag_2570_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = lean_st_ref_put(v___y_2545_, v___x_2576_);
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5___boxed(lean_object* v_mod_2627_, lean_object* v_isMeta_2628_, lean_object* v_hint_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
uint8_t v_isMeta_boxed_2639_; lean_object* v_res_2640_; 
v_isMeta_boxed_2639_ = lean_unbox(v_isMeta_2628_);
v_res_2640_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_mod_2627_, v_isMeta_boxed_2639_, v_hint_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(lean_object* v_a_2641_, lean_object* v_x_2642_){
_start:
{
if (lean_obj_tag(v_x_2642_) == 0)
{
lean_object* v___x_2643_; 
v___x_2643_ = lean_box(0);
return v___x_2643_;
}
else
{
lean_object* v_key_2644_; lean_object* v_value_2645_; lean_object* v_tail_2646_; uint8_t v___x_2647_; 
v_key_2644_ = lean_ctor_get(v_x_2642_, 0);
v_value_2645_ = lean_ctor_get(v_x_2642_, 1);
v_tail_2646_ = lean_ctor_get(v_x_2642_, 2);
v___x_2647_ = lean_name_eq(v_key_2644_, v_a_2641_);
if (v___x_2647_ == 0)
{
v_x_2642_ = v_tail_2646_;
goto _start;
}
else
{
lean_object* v___x_2649_; 
lean_inc(v_value_2645_);
v___x_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2649_, 0, v_value_2645_);
return v___x_2649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg___boxed(lean_object* v_a_2650_, lean_object* v_x_2651_){
_start:
{
lean_object* v_res_2652_; 
v_res_2652_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2650_, v_x_2651_);
lean_dec(v_x_2651_);
lean_dec(v_a_2650_);
return v_res_2652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(lean_object* v_m_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v_buckets_2655_; lean_object* v___x_2656_; uint64_t v___y_2658_; 
v_buckets_2655_ = lean_ctor_get(v_m_2653_, 1);
v___x_2656_ = lean_array_get_size(v_buckets_2655_);
if (lean_obj_tag(v_a_2654_) == 0)
{
uint64_t v___x_2672_; 
v___x_2672_ = 1723ULL;
v___y_2658_ = v___x_2672_;
goto v___jp_2657_;
}
else
{
uint64_t v_hash_2673_; 
v_hash_2673_ = lean_ctor_get_uint64(v_a_2654_, sizeof(void*)*2);
v___y_2658_ = v_hash_2673_;
goto v___jp_2657_;
}
v___jp_2657_:
{
uint64_t v___x_2659_; uint64_t v___x_2660_; uint64_t v_fold_2661_; uint64_t v___x_2662_; uint64_t v___x_2663_; uint64_t v___x_2664_; size_t v___x_2665_; size_t v___x_2666_; size_t v___x_2667_; size_t v___x_2668_; size_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2659_ = 32ULL;
v___x_2660_ = lean_uint64_shift_right(v___y_2658_, v___x_2659_);
v_fold_2661_ = lean_uint64_xor(v___y_2658_, v___x_2660_);
v___x_2662_ = 16ULL;
v___x_2663_ = lean_uint64_shift_right(v_fold_2661_, v___x_2662_);
v___x_2664_ = lean_uint64_xor(v_fold_2661_, v___x_2663_);
v___x_2665_ = lean_uint64_to_usize(v___x_2664_);
v___x_2666_ = lean_usize_of_nat(v___x_2656_);
v___x_2667_ = ((size_t)1ULL);
v___x_2668_ = lean_usize_sub(v___x_2666_, v___x_2667_);
v___x_2669_ = lean_usize_land(v___x_2665_, v___x_2668_);
v___x_2670_ = lean_array_uget_borrowed(v_buckets_2655_, v___x_2669_);
v___x_2671_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_2654_, v___x_2670_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_m_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_2674_, v_a_2675_);
lean_dec(v_a_2675_);
lean_dec_ref(v_m_2674_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(lean_object* v___x_2677_, lean_object* v_declName_2678_, lean_object* v_as_2679_, size_t v_sz_2680_, size_t v_i_2681_, lean_object* v_b_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_2692_; 
v___x_2692_ = lean_usize_dec_lt(v_i_2681_, v_sz_2680_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
lean_dec(v_declName_2678_);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v_b_2682_);
return v___x_2693_;
}
else
{
lean_object* v___x_2694_; lean_object* v_modules_2695_; lean_object* v___x_2696_; lean_object* v_a_2697_; lean_object* v___x_2698_; lean_object* v_toImport_2699_; lean_object* v_module_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v___x_2694_ = l_Lean_Environment_header(v___x_2677_);
v_modules_2695_ = lean_ctor_get(v___x_2694_, 3);
lean_inc_ref(v_modules_2695_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2697_ = lean_array_uget_borrowed(v_as_2679_, v_i_2681_);
v___x_2698_ = lean_array_get(v___x_2696_, v_modules_2695_, v_a_2697_);
lean_dec_ref(v_modules_2695_);
v_toImport_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc_ref(v_toImport_2699_);
lean_dec(v___x_2698_);
v_module_2700_ = lean_ctor_get(v_toImport_2699_, 0);
lean_inc(v_module_2700_);
lean_dec_ref(v_toImport_2699_);
v___x_2701_ = 0;
lean_inc(v_declName_2678_);
v___x_2702_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2700_, v___x_2701_, v_declName_2678_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v___x_2703_; size_t v___x_2704_; size_t v___x_2705_; 
lean_dec_ref_known(v___x_2702_, 1);
v___x_2703_ = lean_box(0);
v___x_2704_ = ((size_t)1ULL);
v___x_2705_ = lean_usize_add(v_i_2681_, v___x_2704_);
v_i_2681_ = v___x_2705_;
v_b_2682_ = v___x_2703_;
goto _start;
}
else
{
lean_dec(v_declName_2678_);
return v___x_2702_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6___boxed(lean_object* v___x_2707_, lean_object* v_declName_2708_, lean_object* v_as_2709_, lean_object* v_sz_2710_, lean_object* v_i_2711_, lean_object* v_b_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
size_t v_sz_boxed_2722_; size_t v_i_boxed_2723_; lean_object* v_res_2724_; 
v_sz_boxed_2722_ = lean_unbox_usize(v_sz_2710_);
lean_dec(v_sz_2710_);
v_i_boxed_2723_ = lean_unbox_usize(v_i_2711_);
lean_dec(v_i_2711_);
v_res_2724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v___x_2707_, v_declName_2708_, v_as_2709_, v_sz_boxed_2722_, v_i_boxed_2723_, v_b_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec_ref(v_as_2709_);
lean_dec_ref(v___x_2707_);
return v_res_2724_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__1));
v___x_2728_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__0));
v___x_2729_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2728_, v___x_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(lean_object* v_declName_2732_, uint8_t v_isMeta_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; lean_object* v_env_2747_; lean_object* v___y_2749_; lean_object* v___x_2762_; 
v___x_2743_ = lean_st_ref_get(v___y_2741_);
v_env_2747_ = lean_ctor_get(v___x_2743_, 0);
lean_inc_ref(v_env_2747_);
lean_dec(v___x_2743_);
v___x_2762_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2747_, v_declName_2732_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_dec_ref(v_env_2747_);
lean_dec(v_declName_2732_);
goto v___jp_2744_;
}
else
{
lean_object* v_val_2763_; lean_object* v___x_2764_; lean_object* v_modules_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_val_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_val_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v___x_2764_ = l_Lean_Environment_header(v_env_2747_);
v_modules_2765_ = lean_ctor_get(v___x_2764_, 3);
lean_inc_ref(v_modules_2765_);
lean_dec_ref(v___x_2764_);
v___x_2766_ = lean_array_get_size(v_modules_2765_);
v___x_2767_ = lean_nat_dec_lt(v_val_2763_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_dec_ref(v_modules_2765_);
lean_dec(v_val_2763_);
lean_dec_ref(v_env_2747_);
lean_dec(v_declName_2732_);
goto v___jp_2744_;
}
else
{
lean_object* v___x_2768_; lean_object* v_env_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___y_2773_; 
v___x_2768_ = lean_st_ref_get(v___y_2741_);
v_env_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc_ref(v_env_2769_);
lean_dec(v___x_2768_);
v___x_2770_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__2);
v___x_2771_ = lean_array_fget(v_modules_2765_, v_val_2763_);
lean_dec(v_val_2763_);
lean_dec_ref(v_modules_2765_);
if (v_isMeta_2733_ == 0)
{
lean_dec_ref(v_env_2769_);
v___y_2773_ = v_isMeta_2733_;
goto v___jp_2772_;
}
else
{
uint8_t v___x_2784_; 
lean_inc(v_declName_2732_);
v___x_2784_ = l_Lean_isMarkedMeta(v_env_2769_, v_declName_2732_);
if (v___x_2784_ == 0)
{
v___y_2773_ = v_isMeta_2733_;
goto v___jp_2772_;
}
else
{
uint8_t v___x_2785_; 
v___x_2785_ = 0;
v___y_2773_ = v___x_2785_;
goto v___jp_2772_;
}
}
v___jp_2772_:
{
lean_object* v_toImport_2774_; lean_object* v_module_2775_; lean_object* v___x_2776_; 
v_toImport_2774_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_ref(v_toImport_2774_);
lean_dec(v___x_2771_);
v_module_2775_ = lean_ctor_get(v_toImport_2774_, 0);
lean_inc(v_module_2775_);
lean_dec_ref(v_toImport_2774_);
lean_inc(v_declName_2732_);
v___x_2776_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5(v_module_2775_, v___y_2773_, v_declName_2732_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec_ref_known(v___x_2776_, 1);
v___x_2777_ = l_Lean_indirectModUseExt;
v___x_2778_ = lean_box(1);
v___x_2779_ = lean_box(0);
lean_inc_ref(v_env_2747_);
v___x_2780_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2770_, v___x_2777_, v_env_2747_, v___x_2778_, v___x_2779_);
v___x_2781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v___x_2780_, v_declName_2732_);
lean_dec(v___x_2780_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v___x_2782_; 
v___x_2782_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___closed__3));
v___y_2749_ = v___x_2782_;
goto v___jp_2748_;
}
else
{
lean_object* v_val_2783_; 
v_val_2783_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v___x_2781_, 1);
v___y_2749_ = v_val_2783_;
goto v___jp_2748_;
}
}
else
{
lean_dec_ref(v_env_2747_);
lean_dec(v_declName_2732_);
return v___x_2776_;
}
}
}
}
v___jp_2744_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = lean_box(0);
v___x_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2745_);
return v___x_2746_;
}
v___jp_2748_:
{
lean_object* v___x_2750_; size_t v_sz_2751_; size_t v___x_2752_; lean_object* v___x_2753_; 
v___x_2750_ = lean_box(0);
v_sz_2751_ = lean_array_size(v___y_2749_);
v___x_2752_ = ((size_t)0ULL);
v___x_2753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__6(v_env_2747_, v_declName_2732_, v___y_2749_, v_sz_2751_, v___x_2752_, v___x_2750_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec_ref(v___y_2749_);
lean_dec_ref(v_env_2747_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; 
v_unused_2761_ = lean_ctor_get(v___x_2753_, 0);
lean_dec(v_unused_2761_);
v___x_2755_ = v___x_2753_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_dec(v___x_2753_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2750_);
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2750_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
return v___x_2753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3___boxed(lean_object* v_declName_2786_, lean_object* v_isMeta_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
uint8_t v_isMeta_boxed_2797_; lean_object* v_res_2798_; 
v_isMeta_boxed_2797_ = lean_unbox(v_isMeta_2787_);
v_res_2798_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_declName_2786_, v_isMeta_boxed_2797_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(lean_object* v_as_x27_2799_, lean_object* v_b_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_){
_start:
{
if (lean_obj_tag(v_as_x27_2799_) == 0)
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_b_2800_);
return v___x_2810_;
}
else
{
lean_object* v_head_2811_; lean_object* v_tail_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; 
v_head_2811_ = lean_ctor_get(v_as_x27_2799_, 0);
v_tail_2812_ = lean_ctor_get(v_as_x27_2799_, 1);
v___x_2813_ = 1;
lean_inc(v_head_2811_);
v___x_2814_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3(v_head_2811_, v___x_2813_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v___x_2815_; 
lean_dec_ref_known(v___x_2814_, 1);
v___x_2815_ = lean_box(0);
v_as_x27_2799_ = v_tail_2812_;
v_b_2800_ = v___x_2815_;
goto _start;
}
else
{
return v___x_2814_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2817_, lean_object* v_b_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_2817_, v_b_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
lean_dec(v_as_x27_2817_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(lean_object* v_env_2829_, lean_object* v_declName_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
uint8_t v___x_2833_; lean_object* v_env_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; uint8_t v___x_2837_; 
v___x_2833_ = 0;
v_env_2834_ = l_Lean_Environment_setExporting(v_env_2829_, v___x_2833_);
lean_inc(v_declName_2830_);
v___x_2835_ = l_Lean_mkPrivateName(v_env_2834_, v_declName_2830_);
v___x_2836_ = 1;
lean_inc_ref(v_env_2834_);
v___x_2837_ = l_Lean_Environment_contains(v_env_2834_, v___x_2835_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; uint8_t v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2838_ = l_Lean_privateToUserName(v_declName_2830_);
v___x_2839_ = l_Lean_Environment_contains(v_env_2834_, v___x_2838_, v___x_2836_);
v___x_2840_ = lean_box(v___x_2839_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2840_);
lean_ctor_set(v___x_2841_, 1, v___y_2832_);
return v___x_2841_;
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_dec_ref(v_env_2834_);
lean_dec(v_declName_2830_);
v___x_2842_ = lean_box(v___x_2837_);
v___x_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
lean_ctor_set(v___x_2843_, 1, v___y_2832_);
return v___x_2843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed(lean_object* v_env_2844_, lean_object* v_declName_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1(v_env_2844_, v_declName_2845_, v___y_2846_, v___y_2847_);
lean_dec_ref(v___y_2846_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(lean_object* v_x_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___x_2860_; lean_object* v_toCold_2861_; lean_object* v_env_2862_; lean_object* v_currRecDepth_2863_; lean_object* v_ref_2864_; lean_object* v_options_2865_; lean_object* v_maxRecDepth_2866_; lean_object* v_currNamespace_2867_; lean_object* v_openDecls_2868_; lean_object* v_quotContext_2869_; lean_object* v_currMacroScope_2870_; lean_object* v___x_2871_; lean_object* v_nextMacroScope_2872_; lean_object* v___f_2873_; lean_object* v___f_2874_; lean_object* v___f_2875_; lean_object* v___f_2876_; lean_object* v___f_2877_; lean_object* v_methods_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2860_ = lean_st_ref_get(v___y_2858_);
v_toCold_2861_ = lean_ctor_get(v___y_2857_, 0);
v_env_2862_ = lean_ctor_get(v___x_2860_, 0);
lean_inc_ref_n(v_env_2862_, 4);
lean_dec(v___x_2860_);
v_currRecDepth_2863_ = lean_ctor_get(v___y_2857_, 1);
v_ref_2864_ = lean_ctor_get(v___y_2857_, 2);
v_options_2865_ = lean_ctor_get(v_toCold_2861_, 2);
v_maxRecDepth_2866_ = lean_ctor_get(v_toCold_2861_, 3);
v_currNamespace_2867_ = lean_ctor_get(v_toCold_2861_, 4);
v_openDecls_2868_ = lean_ctor_get(v_toCold_2861_, 5);
v_quotContext_2869_ = lean_ctor_get(v_toCold_2861_, 8);
v_currMacroScope_2870_ = lean_ctor_get(v_toCold_2861_, 9);
v___x_2871_ = lean_st_ref_get(v___y_2858_);
v_nextMacroScope_2872_ = lean_ctor_get(v___x_2871_, 1);
lean_inc(v_nextMacroScope_2872_);
lean_dec(v___x_2871_);
v___f_2873_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_2873_, 0, v_env_2862_);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(v___f_2874_, 0, v_env_2862_);
lean_inc_n(v_openDecls_2868_, 2);
lean_inc_n(v_currNamespace_2867_, 3);
v___f_2875_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_2875_, 0, v_env_2862_);
lean_closure_set(v___f_2875_, 1, v_currNamespace_2867_);
lean_closure_set(v___f_2875_, 2, v_openDecls_2868_);
v___f_2876_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_2876_, 0, v_currNamespace_2867_);
lean_inc_ref(v_options_2865_);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(v___f_2877_, 0, v_env_2862_);
lean_closure_set(v___f_2877_, 1, v_options_2865_);
lean_closure_set(v___f_2877_, 2, v_currNamespace_2867_);
lean_closure_set(v___f_2877_, 3, v_openDecls_2868_);
v_methods_2878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_methods_2878_, 0, v___f_2873_);
lean_ctor_set(v_methods_2878_, 1, v___f_2876_);
lean_ctor_set(v_methods_2878_, 2, v___f_2874_);
lean_ctor_set(v_methods_2878_, 3, v___f_2875_);
lean_ctor_set(v_methods_2878_, 4, v___f_2877_);
lean_inc(v_ref_2864_);
lean_inc(v_maxRecDepth_2866_);
lean_inc(v_currRecDepth_2863_);
lean_inc(v_currMacroScope_2870_);
lean_inc(v_quotContext_2869_);
v___x_2879_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2879_, 0, v_methods_2878_);
lean_ctor_set(v___x_2879_, 1, v_quotContext_2869_);
lean_ctor_set(v___x_2879_, 2, v_currMacroScope_2870_);
lean_ctor_set(v___x_2879_, 3, v_currRecDepth_2863_);
lean_ctor_set(v___x_2879_, 4, v_maxRecDepth_2866_);
lean_ctor_set(v___x_2879_, 5, v_ref_2864_);
v___x_2880_ = lean_box(0);
v___x_2881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2881_, 0, v_nextMacroScope_2872_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
lean_ctor_set(v___x_2881_, 2, v___x_2880_);
v___x_2882_ = lean_apply_2(v_x_2850_, v___x_2879_, v___x_2881_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v_a_2884_; lean_object* v_macroScope_2885_; lean_object* v_traceMsgs_2886_; lean_object* v_expandedMacroDecls_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 1);
lean_inc(v_a_2883_);
v_a_2884_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2882_, 2);
v_macroScope_2885_ = lean_ctor_get(v_a_2883_, 0);
lean_inc(v_macroScope_2885_);
v_traceMsgs_2886_ = lean_ctor_get(v_a_2883_, 1);
lean_inc(v_traceMsgs_2886_);
v_expandedMacroDecls_2887_ = lean_ctor_get(v_a_2883_, 2);
lean_inc(v_expandedMacroDecls_2887_);
lean_dec(v_a_2883_);
v___x_2888_ = lean_box(0);
v___x_2889_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_expandedMacroDecls_2887_, v___x_2888_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
lean_dec(v_expandedMacroDecls_2887_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v___x_2890_; lean_object* v_env_2891_; lean_object* v_ngen_2892_; lean_object* v_auxDeclNGen_2893_; lean_object* v_traceState_2894_; lean_object* v_cache_2895_; lean_object* v_messages_2896_; lean_object* v_infoState_2897_; lean_object* v_snapshotTasks_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref_known(v___x_2889_, 1);
v___x_2890_ = lean_st_ref_take(v___y_2858_);
v_env_2891_ = lean_ctor_get(v___x_2890_, 0);
v_ngen_2892_ = lean_ctor_get(v___x_2890_, 2);
v_auxDeclNGen_2893_ = lean_ctor_get(v___x_2890_, 3);
v_traceState_2894_ = lean_ctor_get(v___x_2890_, 4);
v_cache_2895_ = lean_ctor_get(v___x_2890_, 5);
v_messages_2896_ = lean_ctor_get(v___x_2890_, 6);
v_infoState_2897_ = lean_ctor_get(v___x_2890_, 7);
v_snapshotTasks_2898_ = lean_ctor_get(v___x_2890_, 8);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2924_ == 0)
{
lean_object* v_unused_2925_; 
v_unused_2925_ = lean_ctor_get(v___x_2890_, 1);
lean_dec(v_unused_2925_);
v___x_2900_ = v___x_2890_;
v_isShared_2901_ = v_isSharedCheck_2924_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_snapshotTasks_2898_);
lean_inc(v_infoState_2897_);
lean_inc(v_messages_2896_);
lean_inc(v_cache_2895_);
lean_inc(v_traceState_2894_);
lean_inc(v_auxDeclNGen_2893_);
lean_inc(v_ngen_2892_);
lean_inc(v_env_2891_);
lean_dec(v___x_2890_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2924_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 1, v_macroScope_2885_);
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_env_2891_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_macroScope_2885_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v_ngen_2892_);
lean_ctor_set(v_reuseFailAlloc_2923_, 3, v_auxDeclNGen_2893_);
lean_ctor_set(v_reuseFailAlloc_2923_, 4, v_traceState_2894_);
lean_ctor_set(v_reuseFailAlloc_2923_, 5, v_cache_2895_);
lean_ctor_set(v_reuseFailAlloc_2923_, 6, v_messages_2896_);
lean_ctor_set(v_reuseFailAlloc_2923_, 7, v_infoState_2897_);
lean_ctor_set(v_reuseFailAlloc_2923_, 8, v_snapshotTasks_2898_);
v___x_2903_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2904_ = lean_st_ref_put(v___y_2858_, v___x_2903_);
v___x_2905_ = l_List_reverse___redArg(v_traceMsgs_2886_);
v___x_2906_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__5(v___x_2905_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; 
v_unused_2914_ = lean_ctor_get(v___x_2906_, 0);
lean_dec(v_unused_2914_);
v___x_2908_ = v___x_2906_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_dec(v___x_2906_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v_a_2884_);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2884_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec(v_a_2884_);
v_a_2915_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2906_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2906_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_dec(v_traceMsgs_2886_);
lean_dec(v_macroScope_2885_);
lean_dec(v_a_2884_);
v_a_2926_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2889_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2889_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; 
v_a_2934_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2882_, 2);
if (lean_obj_tag(v_a_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v_a_2936_; lean_object* v___x_2937_; uint8_t v___x_2938_; 
v_a_2935_ = lean_ctor_get(v_a_2934_, 0);
lean_inc(v_a_2935_);
v_a_2936_ = lean_ctor_get(v_a_2934_, 1);
lean_inc_ref(v_a_2936_);
lean_dec_ref_known(v_a_2934_, 2);
v___x_2937_ = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___closed__0));
v___x_2938_ = lean_string_dec_eq(v_a_2936_, v___x_2937_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_a_2936_);
v___x_2940_ = l_Lean_MessageData_ofFormat(v___x_2939_);
v___x_2941_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_a_2935_, v___x_2940_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
lean_dec(v_a_2935_);
return v___x_2941_;
}
else
{
lean_object* v___x_2942_; 
lean_dec_ref(v_a_2936_);
v___x_2942_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_a_2935_);
return v___x_2942_;
}
}
else
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg___boxed(lean_object* v_x_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_2944_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
lean_dec(v___y_2952_);
lean_dec_ref(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec_ref(v___y_2949_);
lean_dec(v___y_2948_);
lean_dec_ref(v___y_2947_);
lean_dec(v___y_2946_);
lean_dec_ref(v___y_2945_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(lean_object* v_x_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2975_; uint8_t v___x_2976_; 
v___x_2975_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
lean_inc(v_x_2965_);
v___x_2976_ = l_Lean_Syntax_isOfKind(v_x_2965_, v___x_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
lean_dec(v_x_2965_);
v___x_2977_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2977_;
}
else
{
lean_object* v___x_2978_; lean_object* v_hyp_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2978_ = lean_unsigned_to_nat(1u);
v_hyp_2979_ = l_Lean_Syntax_getArg(v_x_2965_, v___x_2978_);
v___x_2980_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__4));
lean_inc(v_hyp_2979_);
v___x_2981_ = l_Lean_Syntax_isOfKind(v_hyp_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_dec(v_hyp_2979_);
lean_dec(v_x_2965_);
v___x_2982_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__0___redArg();
return v___x_2982_;
}
else
{
lean_object* v___x_2983_; lean_object* v_pat_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2983_ = lean_unsigned_to_nat(3u);
v_pat_2984_ = l_Lean_Syntax_getArg(v_x_2965_, v___x_2983_);
lean_dec(v_x_2965_);
v___x_2985_ = lean_alloc_closure((void*)(l_Lean_Parser_Tactic_MCasesPat_parse___boxed), 3, 1);
lean_closure_set(v___x_2985_, 0, v_pat_2984_);
v___x_2986_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v___x_2985_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2988_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2988_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_2967_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v_fst_2990_; lean_object* v_snd_2991_; lean_object* v___f_2992_; lean_object* v___x_2993_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v_fst_2990_ = lean_ctor_get(v_a_2989_, 0);
lean_inc_n(v_fst_2990_, 2);
v_snd_2991_ = lean_ctor_get(v_a_2989_, 1);
lean_inc(v_snd_2991_);
lean_dec(v_a_2989_);
v___f_2992_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2992_, 0, v_snd_2991_);
lean_closure_set(v___f_2992_, 1, v_hyp_2979_);
lean_closure_set(v___f_2992_, 2, v_a_2987_);
lean_closure_set(v___f_2992_, 3, v_fst_2990_);
v___x_2993_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__3___redArg(v_fst_2990_, v___f_2992_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_);
return v___x_2993_;
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v_a_2987_);
lean_dec(v_hyp_2979_);
v_a_2994_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2988_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2988_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v_hyp_2979_);
v_a_3002_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2986_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2986_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed(lean_object* v_x_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMCases(v_x_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
lean_dec(v_a_3018_);
lean_dec_ref(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(lean_object* v_00_u03b1_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___redArg(v_x_3022_, v___y_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3026_, lean_object* v_x_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__2(v_00_u03b1_3026_, v_x_3027_, v___y_3028_, v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec_ref(v_x_3027_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(lean_object* v_00_u03b1_3031_, lean_object* v_ref_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___redArg(v_ref_3032_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7___boxed(lean_object* v_00_u03b1_3043_, lean_object* v_ref_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__7(v_00_u03b1_3043_, v_ref_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(lean_object* v_00_u03b1_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___redArg(v_x_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1___boxed(lean_object* v_00_u03b1_3067_, lean_object* v_x_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1(v_00_u03b1_3067_, v_x_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(lean_object* v_mvarId_3079_, lean_object* v_val_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___redArg(v_mvarId_3079_, v_val_3080_, v___y_3086_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2___boxed(lean_object* v_mvarId_3091_, lean_object* v_val_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2(v_mvarId_3091_, v_val_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(lean_object* v_cls_3103_, lean_object* v_msg_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___redArg(v_cls_3103_, v_msg_3104_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1___boxed(lean_object* v_cls_3115_, lean_object* v_msg_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__1(v_cls_3115_, v_msg_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(lean_object* v_as_3127_, lean_object* v_as_x27_3128_, lean_object* v_b_3129_, lean_object* v_a_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___redArg(v_as_x27_3128_, v_b_3129_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4___boxed(lean_object* v_as_3141_, lean_object* v_as_x27_3142_, lean_object* v_b_3143_, lean_object* v_a_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__4(v_as_3141_, v_as_x27_3142_, v_b_3143_, v_a_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v_as_x27_3142_);
lean_dec(v_as_3141_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(lean_object* v_00_u03b1_3155_, lean_object* v_ref_3156_, lean_object* v_msg_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___redArg(v_ref_3156_, v_msg_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6___boxed(lean_object* v_00_u03b1_3168_, lean_object* v_ref_3169_, lean_object* v_msg_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6(v_00_u03b1_3168_, v_ref_3169_, v_msg_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v_ref_3169_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9(lean_object* v_00_u03b2_3181_, lean_object* v_x_3182_, lean_object* v_x_3183_, lean_object* v_x_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9___redArg(v_x_3182_, v_x_3183_, v_x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3186_, lean_object* v_m_3187_, lean_object* v_a_3188_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___redArg(v_m_3187_, v_a_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3190_, lean_object* v_m_3191_, lean_object* v_a_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7(v_00_u03b2_3190_, v_m_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_m_3191_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_3194_, lean_object* v_msg_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___redArg(v_msg_3195_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_3206_, lean_object* v_msg_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__6_spec__11(v_00_u03b1_3206_, v_msg_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(lean_object* v_00_u03b2_3218_, lean_object* v_x_3219_, size_t v_x_3220_, size_t v_x_3221_, lean_object* v_x_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___redArg(v_x_3219_, v_x_3220_, v_x_3221_, v_x_3222_, v_x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15___boxed(lean_object* v_00_u03b2_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_, lean_object* v_x_3228_, lean_object* v_x_3229_, lean_object* v_x_3230_){
_start:
{
size_t v_x_21340__boxed_3231_; size_t v_x_21341__boxed_3232_; lean_object* v_res_3233_; 
v_x_21340__boxed_3231_ = lean_unbox_usize(v_x_3227_);
lean_dec(v_x_3227_);
v_x_21341__boxed_3232_ = lean_unbox_usize(v_x_3228_);
lean_dec(v_x_3228_);
v_res_3233_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15(v_00_u03b2_3225_, v_x_3226_, v_x_21340__boxed_3231_, v_x_21341__boxed_3232_, v_x_3229_, v_x_3230_);
return v_res_3233_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_3234_, lean_object* v_x_3235_, lean_object* v_x_3236_){
_start:
{
uint8_t v___x_3237_; 
v___x_3237_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___redArg(v_x_3235_, v_x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3238_, lean_object* v_x_3239_, lean_object* v_x_3240_){
_start:
{
uint8_t v_res_3241_; lean_object* v_r_3242_; 
v_res_3241_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8(v_00_u03b2_3238_, v_x_3239_, v_x_3240_);
lean_dec_ref(v_x_3240_);
lean_dec_ref(v_x_3239_);
v_r_3242_ = lean_box(v_res_3241_);
return v_r_3242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(lean_object* v_00_u03b2_3243_, lean_object* v_a_3244_, lean_object* v_x_3245_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___redArg(v_a_3244_, v_x_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3247_, lean_object* v_a_3248_, lean_object* v_x_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__7_spec__11(v_00_u03b2_3247_, v_a_3248_, v_x_3249_);
lean_dec(v_x_3249_);
lean_dec(v_a_3248_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18(lean_object* v_00_u03b2_3251_, lean_object* v_n_3252_, lean_object* v_k_3253_, lean_object* v_v_3254_){
_start:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18___redArg(v_n_3252_, v_k_3253_, v_v_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(lean_object* v_00_u03b2_3256_, size_t v_depth_3257_, lean_object* v_keys_3258_, lean_object* v_vals_3259_, lean_object* v_heq_3260_, lean_object* v_i_3261_, lean_object* v_entries_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___redArg(v_depth_3257_, v_keys_3258_, v_vals_3259_, v_i_3261_, v_entries_3262_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19___boxed(lean_object* v_00_u03b2_3264_, lean_object* v_depth_3265_, lean_object* v_keys_3266_, lean_object* v_vals_3267_, lean_object* v_heq_3268_, lean_object* v_i_3269_, lean_object* v_entries_3270_){
_start:
{
size_t v_depth_boxed_3271_; lean_object* v_res_3272_; 
v_depth_boxed_3271_ = lean_unbox_usize(v_depth_3265_);
lean_dec(v_depth_3265_);
v_res_3272_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__19(v_00_u03b2_3264_, v_depth_boxed_3271_, v_keys_3266_, v_vals_3267_, v_heq_3268_, v_i_3269_, v_entries_3270_);
lean_dec_ref(v_vals_3267_);
lean_dec_ref(v_keys_3266_);
return v_res_3272_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_3273_, lean_object* v_x_3274_, size_t v_x_3275_, lean_object* v_x_3276_){
_start:
{
uint8_t v___x_3277_; 
v___x_3277_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___redArg(v_x_3274_, v_x_3275_, v_x_3276_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13___boxed(lean_object* v_00_u03b2_3278_, lean_object* v_x_3279_, lean_object* v_x_3280_, lean_object* v_x_3281_){
_start:
{
size_t v_x_21374__boxed_3282_; uint8_t v_res_3283_; lean_object* v_r_3284_; 
v_x_21374__boxed_3282_ = lean_unbox_usize(v_x_3280_);
lean_dec(v_x_3280_);
v_res_3283_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13(v_00_u03b2_3278_, v_x_3279_, v_x_21374__boxed_3282_, v_x_3281_);
lean_dec_ref(v_x_3281_);
lean_dec_ref(v_x_3279_);
v_r_3284_ = lean_box(v_res_3283_);
return v_r_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20(lean_object* v_00_u03b2_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_, lean_object* v_x_3288_, lean_object* v_x_3289_){
_start:
{
lean_object* v___x_3290_; 
v___x_3290_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__2_spec__9_spec__15_spec__18_spec__20___redArg(v_x_3286_, v_x_3287_, v_x_3288_, v_x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(lean_object* v_00_u03b2_3291_, lean_object* v_keys_3292_, lean_object* v_vals_3293_, lean_object* v_heq_3294_, lean_object* v_i_3295_, lean_object* v_k_3296_){
_start:
{
uint8_t v___x_3297_; 
v___x_3297_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___redArg(v_keys_3292_, v_i_3295_, v_k_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3298_, lean_object* v_keys_3299_, lean_object* v_vals_3300_, lean_object* v_heq_3301_, lean_object* v_i_3302_, lean_object* v_k_3303_){
_start:
{
uint8_t v_res_3304_; lean_object* v_r_3305_; 
v_res_3304_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMCases_spec__1_spec__3_spec__5_spec__8_spec__13_spec__18(v_00_u03b2_3298_, v_keys_3299_, v_vals_3300_, v_heq_3301_, v_i_3302_, v_k_3303_);
lean_dec_ref(v_k_3303_);
lean_dec_ref(v_vals_3300_);
lean_dec_ref(v_keys_3299_);
v_r_3305_ = lean_box(v_res_3304_);
return v_r_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1(){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3315_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_3316_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___closed__2));
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___closed__1));
v___x_3318_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMCases___boxed), 10, 0);
v___x_3319_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3315_, v___x_3316_, v___x_3317_, v___x_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1___boxed(lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Cases_0__Lean_Elab_Tactic_Do_ProofMode_elabMCases___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMCases__1();
return v_res_3321_;
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
